'use strict';

const crypto = require('crypto');
const fs = require('fs');

module.exports = async function postOcrReview({ github, context, core }) {
  const owner = context.repo.owner;
  const repo = context.repo.repo;
  const pull_number = Number(process.env.OCR_PR_NUMBER);
  const commit_id = process.env.OCR_HEAD_SHA;
  const resultPath = process.env.OCR_RESULT_PATH;
  const stderrPath = process.env.OCR_STDERR_PATH;
  const metricsPath = process.env.OCR_METRICS_PATH;
  const maxInline = Number(process.env.OCR_MAX_INLINE_COMMENTS || 20);
  const rulesHash = (process.env.OCR_RULES_HASH || 'rules-v0').slice(0, 12);
  const reviewerVersion = (process.env.OCR_REVIEWER_VERSION || 'reviewer-v2').slice(0, 20);
  const routerVersion = (process.env.OCR_ROUTER_VERSION || 'router-v0').slice(0, 20);
  const mode = (process.env.OCR_MODE || 'legacy').slice(0, 40);
  const defaultDedupKey = buildDedupBaseKey({ commit_id, rulesHash, reviewerVersion, routerVersion, mode });
  const defaultRetryableTag = `<!-- paloma-ocr-review:${defaultDedupKey}:retryable-failure -->`;

  if (!pull_number || !commit_id) {
    throw new Error('OCR_PR_NUMBER and OCR_HEAD_SHA are required');
  }

  const raw = fs.existsSync(resultPath) ? fs.readFileSync(resultPath, 'utf8') : '';
  const stderr = fs.existsSync(stderrPath) ? fs.readFileSync(stderrPath, 'utf8').trim() : '';
  let result;
  try {
    result = JSON.parse(raw);
  } catch (err) {
    const alreadySucceeded = await hasExistingSuccessForDedupBase(github, {
      owner,
      repo,
      pull_number,
      dedupKeyBase: defaultDedupKey,
    });
    if (alreadySucceeded) {
      core.notice(`Successful OCR review for ${commit_id} was already posted; skipping invalid JSON failure duplicate.`);
      return;
    }
    writeMetrics(metricsPath, enrichMetrics(readMetrics(metricsPath), {
      mode,
      result: { status: 'invalid_json', comments: [], warnings: [] },
      stderr,
      retryable: true,
    }));
    await github.rest.issues.createComment({
      owner, repo, issue_number: pull_number,
      // Invalid JSON has no trustworthy result/metrics payload, so use the base retryable tag.
      body: `${defaultRetryableTag}\n⚠️ **OpenCodeReview failed to produce valid JSON.**\n\n${stderr ? fenced(stderr) : 'No stderr captured.'}`,
    });
    return;
  }

  const comments = Array.isArray(result.comments) ? result.comments : [];
  const warnings = Array.isArray(result.warnings) ? result.warnings : [];
  const usable = [];
  const summaryOnly = [];
  const retryableResult = isRetryableResult(result);
  const metrics = enrichMetrics(readMetrics(metricsPath), { mode, result, stderr, retryable: retryableResult });
  const dedupKey = buildDedupKey({ commit_id, rulesHash, reviewerVersion, routerVersion, mode, result, metrics });
  const successTag = `<!-- paloma-ocr-review:${dedupKey}:success -->`;
  const retryableTag = `<!-- paloma-ocr-review:${dedupKey}:retryable-failure -->`;

  const alreadyPosted = await hasExistingTag(github, { owner, repo, pull_number, tag: successTag });
  if (alreadyPosted) {
    core.notice(`Successful OCR review for ${commit_id} was already posted; skipping duplicate.`);
    return;
  }
  const legacyLargeLeanDuplicate = await hasExistingLegacyLargeLeanScoutSuccess(github, {
    owner,
    repo,
    pull_number,
    dedupKeyBase: defaultDedupKey,
    result,
    metrics,
  });
  if (legacyLargeLeanDuplicate) {
    core.notice(`Successful large Lean scout review for ${commit_id} with the same scout discriminator was already posted; skipping duplicate.`);
    return;
  }

  writeMetrics(metricsPath, metrics);

  for (const c of comments) {
    const path = String(c.path || '').trim();
    const line = Number(c.end_line || c.start_line || 0);
    const content = String(c.content || '').trim();
    if (!path || !content || !Number.isFinite(line) || line < 1) {
      summaryOnly.push(c);
      continue;
    }
    usable.push({
      path,
      line,
      side: 'RIGHT',
      body: renderComment(c),
      content,
      category: c.category,
      severity: c.severity,
    });
  }

  const selected = usable.slice(0, maxInline);
  const overflow = usable.slice(maxInline);
  const tag = retryableResult ? retryableTag : successTag;
  const body = retryableResult
    ? buildReviewBody({ tag, result, comments, selected: [], overflow: [...selected, ...overflow], summaryOnly, warnings, stderr, metrics, retryable: true })
    : buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr, metrics, retryable: false });

  if (retryableResult) {
    await github.rest.issues.createComment({
      owner,
      repo,
      issue_number: pull_number,
      body,
    });
    await publishSemanticReviewCheck({ github, core, owner, repo, head_sha: commit_id, mode, result, retryable: true });
    return;
  }

  try {
    await github.rest.pulls.createReview({
      owner,
      repo,
      pull_number,
      commit_id,
      event: 'COMMENT',
      body,
      comments: selected.map(toReviewComment),
    });
    await minimizeStaleScoutComments({ github, core, owner, repo, pull_number, commit_id });
  } catch (err) {
    core.warning(`Batch createReview failed: ${err.message}`);
    const fallbackBody = `${body.replace(successTag, retryableTag)}\n\n⚠️ Inline publication failed, so OCR findings are summarized here instead.\n\n${renderInlineFallback(selected)}\n\n${fenced(String(err.message || err))}`;
    await github.rest.issues.createComment({
      owner,
      repo,
      issue_number: pull_number,
      body: fallbackBody,
    });
  }

  await publishSemanticReviewCheck({ github, core, owner, repo, head_sha: commit_id, mode, result, retryable: retryableResult });
};

// P2: a second, honest check. The workflow job itself stays green whenever the
// pipeline ran, so this check-run carries the real review meaning: success
// only when a semantic review actually covered the diff (full OCR, or every
// planned packet group); neutral for triage-only or partial coverage.
async function publishSemanticReviewCheck({ github, core, owner, repo, head_sha, mode, result, retryable }) {
  try {
    let conclusion = 'neutral';
    let title = 'Triage only — no semantic review';
    const packet = result.summary?.packet_semantic;
    if (retryable || result.status === 'error') {
      conclusion = 'failure';
      title = 'Review errored — treat as unreviewed';
    } else if (mode === 'no-supported' || result.status === 'no-supported') {
      conclusion = 'neutral';
      title = 'No OCR-supported files in diff';
    } else if (mode !== 'large-lean-hotspots' && result.status !== 'scout_triage') {
      conclusion = 'success';
      title = `Full OCR semantic review (${mode})`;
    } else if (packet && packet.total_groups > 0) {
      const covered = `${packet.covered_groups}/${packet.total_groups}`;
      if (packet.covered_groups === packet.total_groups) {
        conclusion = 'success';
        title = `Packet semantic review: ${covered} groups covered`;
      } else {
        conclusion = 'neutral';
        title = `Partial packet review: ${covered} groups — rest is triage-only`;
      }
    }
    await github.rest.checks.create({
      owner,
      repo,
      name: 'OCR semantic review',
      head_sha,
      status: 'completed',
      conclusion,
      output: {
        title,
        summary: 'Semantic-review coverage published by post-ocr-review.js. Neutral means the diff (or part of it) only received scout triage: do not read the green pipeline job as review coverage.',
      },
    });
  } catch (err) {
    core.warning(`Semantic review check not published: ${err.message}`);
  }
}

// P4: once a newer head has a successful post, older heads' scout markers are
// noise that reads like open findings. Minimize (fold as OUTDATED) every OCR
// inline comment whose original commit differs from the current head.
async function minimizeStaleScoutComments({ github, core, owner, repo, pull_number, commit_id }) {
  try {
    const comments = await github.paginate(github.rest.pulls.listReviewComments, {
      owner,
      repo,
      pull_number,
      per_page: 100,
    });
    const stale = comments.filter(c =>
      c.user?.login === 'github-actions[bot]'
      && c.original_commit_id
      && c.original_commit_id !== commit_id
      && /(Scout triage coverage marker|OCR scout — question de triage|OpenCodeReview)/.test(c.body || ''),
    );
    for (const comment of stale) {
      try {
        await github.graphql(
          `mutation($id: ID!) { minimizeComment(input: { subjectId: $id, classifier: OUTDATED }) { minimizedComment { isMinimized } } }`,
          { id: comment.node_id },
        );
      } catch (err) {
        core.warning(`minimizeComment failed for ${comment.id}: ${err.message}`);
      }
    }
    if (stale.length) core.notice(`Minimized ${stale.length} stale OCR comment(s) from previous heads.`);
  } catch (err) {
    core.warning(`Stale scout comment minimization skipped: ${err.message}`);
  }
}

async function hasExistingTag(github, { owner, repo, pull_number, tag }) {
  const issueComments = await github.paginate(github.rest.issues.listComments, {
    owner, repo, issue_number: pull_number, per_page: 100,
  });
  if (issueComments.some(c => String(c.body || '').includes(tag))) return true;

  const reviews = await github.paginate(github.rest.pulls.listReviews, {
    owner, repo, pull_number, per_page: 100,
  });
  return reviews.some(r => String(r.body || '').includes(tag));
}

async function hasExistingSuccessForDedupBase(github, { owner, repo, pull_number, dedupKeyBase }) {
  const hasSuccess = body => {
    const text = String(body || '');
    const start = `<!-- paloma-ocr-review:${dedupKeyBase}`;
    let index = text.indexOf(start);
    while (index !== -1) {
      const end = text.indexOf('-->', index);
      if (end !== -1 && text.slice(index, end + 3).endsWith(':success -->')) return true;
      index = text.indexOf(start, index + start.length);
    }
    return false;
  };

  const issueComments = await github.paginate(github.rest.issues.listComments, {
    owner, repo, issue_number: pull_number, per_page: 100,
  });
  if (issueComments.some(c => hasSuccess(c.body))) return true;

  const reviews = await github.paginate(github.rest.pulls.listReviews, {
    owner, repo, pull_number, per_page: 100,
  });
  return reviews.some(r => hasSuccess(r.body));
}

async function hasExistingLegacyLargeLeanScoutSuccess(github, { owner, repo, pull_number, dedupKeyBase, result, metrics }) {
  const signature = largeLeanScoutVisibleSignature({ result, metrics });
  if (!signature) return false;
  const legacyTag = `<!-- paloma-ocr-review:${dedupKeyBase}:success -->`;
  const hasMatchingLegacySuccess = body => {
    const text = String(body || '');
    return text.includes(legacyTag)
      && hasExactLegacyPacketLine(text, signature)
      && hasExactLegacyScoutLine(text, signature);
  };

  const issueComments = await github.paginate(github.rest.issues.listComments, {
    owner, repo, issue_number: pull_number, per_page: 100,
  });
  if (issueComments.some(c => hasMatchingLegacySuccess(c.body))) return true;

  const reviews = await github.paginate(github.rest.pulls.listReviews, {
    owner, repo, pull_number, per_page: 100,
  });
  return reviews.some(r => hasMatchingLegacySuccess(r.body));
}

function isRetryableResult(result) {
  const status = String(result.status || '').toLowerCase();
  return status === 'error' || status === 'failed' || status === 'failure' || status === 'completed_with_errors';
}

function buildDedupKey({ commit_id, rulesHash, reviewerVersion, routerVersion, mode, result, metrics }) {
  const base = buildDedupBaseKey({ commit_id, rulesHash, reviewerVersion, routerVersion, mode });
  const discriminator = buildLargeLeanScoutDedupDiscriminator({ mode, result, metrics });
  return discriminator ? `${base}:${discriminator}` : base;
}

function buildDedupBaseKey({ commit_id, rulesHash, reviewerVersion, routerVersion, mode }) {
  return `${commit_id}:${rulesHash}:${reviewerVersion}:${routerVersion}:${mode}`;
}

function buildLargeLeanScoutDedupDiscriminator({ mode, result, metrics }) {
  const effectiveMode = metrics?.mode || result?.summary?.mode || mode;
  const packetReview = metrics?.packet_review || result?.summary?.packet_review;
  if (effectiveMode !== 'large-lean-hotspots' || !packetReview) return '';

  const scout = packetReview.scout || {};
  const enabled = scout.enabled ? 'enabled' : 'disabled';
  const model = sanitizeDedupComponent(scout.model || 'none', 80);
  const status = sanitizeDedupComponent(scout.status || 'unknown', 48);
  const selected = sanitizeDedupComponent(packetReview.packets_selected ?? 'unknown', 24);
  const budget = sanitizeDedupComponent(packetReview.packet_budget ?? 'unknown', 24);
  const packetFingerprint = fingerprintPacketIds(packetReview);
  return `scout-v1:${enabled}:model-${model}:status-${status}:packets-${selected}-of-${budget}:ids-${packetFingerprint}`;
}

function largeLeanScoutVisibleSignature({ result, metrics }) {
  const effectiveMode = metrics?.mode || result?.summary?.mode;
  const packetReview = metrics?.packet_review || result?.summary?.packet_review;
  if (effectiveMode !== 'large-lean-hotspots' || !packetReview) return null;

  const scout = packetReview.scout || {};
  const model = String(scout.model || '').trim();
  const status = String(scout.status || '').trim();
  const selected = packetReview.packets_selected;
  const budget = packetReview.packet_budget;
  if (!model || !status || selected == null || budget == null) return null;
  return {
    model,
    status,
    selected: String(selected),
    budget: String(budget),
  };
}

function hasExactLegacyPacketLine(text, signature) {
  const selected = escapeRegExp(signature.selected);
  const budget = escapeRegExp(signature.budget);
  return new RegExp(`(?:^|\\n)- Packet review: [^\\n]*selected ${selected}/${budget}(?:\\s|$)`).test(text);
}

function hasExactLegacyScoutLine(text, signature) {
  const status = escapeRegExp(signature.status);
  const model = escapeRegExp(signature.model);
  return new RegExp(`(?:^|\\n)- Scout: [^\\n]*status ${status}; model ${model}(?:\\s|$)`).test(text);
}

function escapeRegExp(value) {
  return String(value).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function sanitizeDedupComponent(value, maxLength = 80) {
  const raw = String(value ?? '');
  if (isSensitiveDedupValue(raw)) {
    return `redacted-${hashDedupValue(raw)}`;
  }
  const sanitized = raw
    .replace(/[^A-Za-z0-9._-]+/g, '_')
    .replace(/^_+|_+$/g, '')
    .slice(0, maxLength);
  return sanitized || 'empty';
}

function isSensitiveDedupValue(value) {
  const text = String(value || '').trim();
  if (!text) return false;
  if (/https?:\/\//i.test(text) || /(^|[\s,;])\/\/[^\s,;]+/.test(text)) return true;
  if (/(^|[\s,;])(?:[A-Za-z0-9-]+\.)+[A-Za-z]{2,}(?:[:/?#]|$)/.test(text)) return true;
  if (/(api[_-]?key|token|secret|password|bearer)/i.test(text)) return true;
  if (/^[A-Za-z0-9+/=_-]{16,}$/.test(text)) return true;
  return false;
}

function hashDedupValue(value) {
  return crypto.createHash('sha256').update(String(value)).digest('hex').slice(0, 12);
}

function fingerprintPacketIds(packetReview) {
  const packets = Array.isArray(packetReview?.packets) ? packetReview.packets : [];
  const ids = packets
    .map(packet => packet?.packet_id || packet?.id || `${packet?.path || 'unknown'}:${packet?.start_line ?? '?'}-${packet?.end_line ?? '?'}`)
    .filter(Boolean)
    .map(String);
  if (!ids.length) return 'none';
  return hashDedupValue(ids.join('|'));
}

function toReviewComment(c) {
  return {
    path: c.path,
    line: c.line,
    side: c.side,
    body: c.body,
  };
}

function buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr, metrics, retryable = false }) {
  const status = result.status || 'unknown';
  const message = result.message || '';
  const summary = result.summary || {};
  const mode = metrics?.mode || summary.mode || 'unknown';

  setPacketSemantic(result.summary?.packet_semantic);
  let body = `${tag}\n## OpenCodeReview first-pass review\n\n`;
  body += `${verdictLine({ status, mode, comments, retryable })}\n\n`;
  const packetSemantic = result.summary?.packet_semantic;
  if (mode === 'large-lean-hotspots' && packetSemantic) {
    const uncovered = (packetSemantic.per_group || []).filter(g => g.status !== 'success');
    if (uncovered.length > 0) {
      body += `### Paquets non couverts par la review sémantique\n\n`;
      for (const g of uncovered.slice(0, 10)) {
        body += `- **${escapeMd((g.files || []).join(', '))}** — ${escapeMd(g.status)}${g.error ? ` (${escapeMd(firstLine(g.error))})` : ''}\n`;
      }
      body += `\n`;
    }
    const extraGroups = (packetSemantic.total_groups_available ?? 0) - (packetSemantic.total_groups ?? 0);
    if (extraGroups > 0) {
      body += `📝 ${extraGroups} groupe(s) de paquets au-delà du budget n'ont eu que le triage scout.\n\n`;
    }
  }

  if (message) body += `${escapeMd(message)}\n\n`;
  if (selected.length > 0) body += `✅ Posted ${selected.length} inline comment(s).\n`;
  if (overflow.length > 0) body += `📝 ${overflow.length} additional positioned finding(s) omitted from inline comments to avoid spam.\n`;
  if (summaryOnly.length > 0) body += `📝 ${summaryOnly.length} finding(s) had no resolvable line and are summarized below.\n`;
  body += `\n`;

  const summarized = [...summaryOnly, ...overflow].slice(0, 20);
  if (summarized.length > 0) {
    body += `### Summary-only findings\n\n`;
    for (const c of summarized) {
      body += `- **${escapeMd(c.path || 'unknown')}**${badge(c)} — ${escapeMd(firstLine(c.content || ''))}\n`;
    }
    body += `\n`;
  }

  // The scout-coverage caveat already leads the verdict line for
  // large-lean-hotspots runs; repeating it in the warnings list is noise.
  const visibleWarnings = warnings.filter(
    w => !(mode === 'large-lean-hotspots' && /scout mode covers ranked hotspots/i.test(String(w.message || ''))),
  );
  if (visibleWarnings.length > 0) {
    body += `### Warnings\n\n`;
    for (const w of visibleWarnings.slice(0, 10)) {
      body += `- **${escapeMd(w.type || 'warning')}** ${escapeMd(w.file || '')}: ${escapeMd(firstLine(w.message || ''))}\n`;
    }
    body += `\n`;
  }

  if (stderr && /deadline|timed? ?out/i.test(stderr)) {
    body += `### Warnings\n\n- **timeout**: OCR stderr mentions a subtask deadline/timeout — findings may be incomplete; consider raising the mode timeout.\n\n`;
  }
  if (stderr) {
    const interesting = stderr.split('\n').filter(line => /warning|error|failed|fatal/i.test(line)).slice(0, 20).join('\n');
    if (interesting) {
      body += `<details><summary>OCR stderr highlights</summary>\n\n${fenced(interesting)}\n</details>\n\n`;
    }
  }

  // Operator telemetry stays available but folded, so the visible comment is
  // the review, not the pipeline report.
  const opsDetails = `${renderMetrics(metrics, result)}${renderPacketCoverage(metrics, result)}`.trim();
  if (opsDetails) {
    body += `<details><summary>OCR pilot metrics & packet coverage</summary>\n\n${opsDetails}\n\n</details>\n\n`;
  }
  body += `_Pilot mode: advisory only. Codex Review remains the merge gate._`;
  return body;
}

function severityRollup(comments) {
  const counts = { high: 0, medium: 0, low: 0 };
  let unrated = 0;
  for (const c of comments) {
    const sev = String(c.severity || '').toLowerCase();
    if (Object.prototype.hasOwnProperty.call(counts, sev)) counts[sev] += 1;
    else unrated += 1;
  }
  const parts = [];
  if (counts.high) parts.push(`${counts.high} high`);
  if (counts.medium) parts.push(`${counts.medium} medium`);
  if (counts.low) parts.push(`${counts.low} low`);
  if (unrated) parts.push(`${unrated} unrated`);
  return parts.join(' / ');
}

// One plain-language line a reviewer can act on without decoding router
// internals. Mode/status/version details live in the folded metrics block.
let _packetSemantic = null;
function setPacketSemantic(value) { _packetSemantic = value || null; }
function metricsPacketSemantic() { return _packetSemantic; }

function verdictLine({ status, mode, comments, retryable }) {
  const rollup = severityRollup(comments);
  const findings = comments.length
    ? `${comments.length} finding(s)${rollup ? ` (${rollup})` : ''}`
    : 'no findings';
  if (retryable) {
    return `🔁 **Incomplete — this run did not finish and will retry on the same commit.** Do not count it as review coverage.`;
  }
  if (status === 'no-supported' || mode === 'no-supported') {
    return `⚪ **OCR did not run** — this diff has no OCR-supported files. Not a review outcome.`;
  }
  if (status === 'error') {
    return `🔴 **Review errored** (${findings} before the failure) — treat this PR as unreviewed by OCR.`;
  }
  if (mode === 'large-lean-hotspots') {
    const packet = metricsPacketSemantic();
    if (packet && packet.total_groups > 0) {
      const covered = `${packet.covered_groups}/${packet.total_groups}`;
      const grade = packet.covered_groups === packet.total_groups ? '🟢' : '🟡';
      return `${grade} **Scout triage + ${covered} paquet(s) reviewés sémantiquement.** ${findings}; les hunks hors paquets restent à couvrir par un humain ou Codex.`;
    }
    return `🟡 **Scout triage only — not a full review.** ${findings}; a human or Codex must still cover the unflagged hunks and proof obligations.`;
  }
  if (comments.length > 0) {
    return `🟠 **${findings}** — see inline comments.`;
  }
  return `🟢 **No findings from the OCR first pass.** Advisory only.`;
}

function extractOcrSummary(result) {
  const summary = result.summary || {};
  const usage = result.usage || result.metrics || {};
  const toolCalls = result.tool_calls || result.toolCalls || {};
  return {
    status: result.status || 'unknown',
    commentsCount: Array.isArray(result.comments) ? result.comments.length : 0,
    filesReviewed: firstNumber(summary.files_reviewed, summary.filesReviewed, result.files_reviewed, result.filesReviewed),
    totalTokens: firstNumber(summary.total_tokens, summary.totalTokens, usage.total_tokens, usage.totalTokens, result.total_tokens),
    toolCallsTotal: firstNumber(toolCalls.total, toolCalls.total_calls, toolCalls.totalCalls, summary.tool_calls_total, summary.toolCallsTotal),
    warningsCount: Array.isArray(result.warnings) ? result.warnings.length : firstNumber(summary.warnings_count, summary.warningsCount),
  };
}

function enrichMetrics(metrics, { mode, result, stderr, retryable }) {
  const base = metrics && typeof metrics === 'object' ? metrics : {};
  const extracted = extractOcrSummary(result);
  const started = Date.parse(base.started_at || '');
  const completedAt = new Date().toISOString();
  const duration = Number.isFinite(started) ? Date.parse(completedAt) - started : null;
  return {
    ...base,
    mode: mode || base.mode || result.summary?.mode || 'unknown',
    completed_at: completedAt,
    ocr: {
      ...(base.ocr || {}),
      attempted: base.ocr?.attempted ?? !['no-supported', 'large-lean-hotspots', 'packetized_review'].includes(String(result.status || '')),
      retryable: Boolean(retryable),
      status: extracted.status,
      comments_count: extracted.commentsCount,
      files_reviewed: extracted.filesReviewed,
      total_tokens: extracted.totalTokens,
      tool_calls_total: extracted.toolCallsTotal,
      warnings_count: extracted.warningsCount,
      duration_ms: duration,
      stderr_highlights_count: stderr ? stderr.split('\n').filter(line => /warning|error|failed|fatal/i.test(line)).length : 0,
    },
  };
}

function renderMetrics(metrics, result) {
  const extracted = extractOcrSummary(result);
  const counts = metrics?.changed_files?.counts || {};
  const thresholds = metrics?.thresholds || result.summary?.thresholds || {};
  const largest = metrics?.changed_files?.largest || result.summary?.changed_files?.largest || [];
  const ocr = metrics?.ocr || {};
  let body = `### OCR pilot metrics\n\n`;
  body += `- Routing: ${escapeMd(metrics?.mode || result.summary?.mode || 'unknown')} (${escapeMd(metrics?.router_version || result.summary?.router_version || 'router unknown')})\n`;
  body += `- Changed files: ${counts.supported ?? 'unknown'} supported / ${counts.total ?? 'unknown'} total; Lean ${counts.lean ?? 0}, trust docs ${counts.trustDocs ?? 0}, workflow/scripts ${counts.workflowScripts ?? 0}, contracts ${counts.contracts ?? 0}, docs ${counts.docs ?? 0}\n`;
  body += `- Changed lines: ${metrics?.changed_files?.total_changed_lines ?? 'unknown'} supported; thresholds large Lean >=${thresholds.largeLeanFiles ?? '?'} files or >${thresholds.largeChangedLines ?? '?'} lines\n`;
  body += `- OCR: status ${escapeMd(extracted.status)}; comments ${extracted.commentsCount}; files ${extracted.filesReviewed ?? 'unknown'}; tokens ${extracted.totalTokens ?? 0}; tool calls ${extracted.toolCallsTotal ?? 0}; warnings ${extracted.warningsCount ?? 0}; duration ${formatDuration(ocr.duration_ms)}\n`;
  if (largest.length > 0) {
    body += `- Largest changed files: ${largest.slice(0, 5).map(f => `${escapeMd(f.path)} (+${f.added}/-${f.deleted})`).join(', ')}\n`;
  }
  body += `\n`;
  return body;
}

function renderPacketCoverage(metrics, result) {
  const packetReview = metrics?.packet_review || result.summary?.packet_review;
  if (!packetReview) return '';

  const packets = Array.isArray(packetReview.packets) ? packetReview.packets : [];
  let body = `### Packet coverage\n\n`;
  const scout = packetReview.scout || {};
  body += `- Packet review: ${packetReview.enabled ? 'enabled' : 'not used'}; selected ${packetReview.packets_selected ?? packets.length}/${packetReview.packet_budget ?? '?'} packet(s)\n`;
  body += `- Scout: ${scout.enabled ? 'configured' : 'not configured'}; status ${escapeMd(scout.status || 'unknown')}; model ${escapeMd(scout.model || 'none')}\n`;
  if (Array.isArray(scout.lenses) && scout.lenses.length) {
    body += `- Scout lenses: ${escapeMd(scout.lenses.join(', '))}`;
    if (scout.partial_lens_failures) body += ` (${scout.partial_lens_failures} lens(es) failed; union of the rest used)`;
    if (scout.rubric_items != null) body += `; rubric items checked ${scout.rubric_items}`;
    body += `\n`;
  }
  if (scout.error_detail) {
    if (typeof scout.http_status === 'number') body += `- Scout provider HTTP status: ${scout.http_status}\n`;
    body += `- Scout provider error: ${escapeMd(scout.error_detail)}\n`;
  }
  if (packetReview.strong_review_required) {
    body += `- Strong review: required; status ${escapeMd(packetReview.strong_review_status || 'unknown')}\n`;
  }
  if (packetReview.residual_risk) {
    body += `- Residual risk: ${escapeMd(packetReview.residual_risk)}\n`;
  }
  if (packetReview.strong_review_blocker) {
    body += `- Strong packet-review blocker: ${escapeMd(packetReview.strong_review_blocker)}\n`;
  }
  if (packets.length > 0) {
    body += `- Covered packets:\n`;
    for (const packet of packets.slice(0, 8)) {
      const signals = Array.isArray(packet.signals) && packet.signals.length ? packet.signals.join(', ') : 'hotspot path/churn';
      const lensTag = Array.isArray(packet.scout_lens_ids) && packet.scout_lens_ids.length ? ` [lenses: ${packet.scout_lens_ids.join(', ')}]` : '';
      const question = packet.scout_question ? `; ask: ${packet.scout_question}` : '';
      body += `  - ${escapeMd(packet.path)}:${packet.start_line ?? '?'} score ${packet.score ?? '?'}${escapeMd(lensTag)} — ${escapeMd(signals + question)}\n`;
    }
  }
  body += `\n`;
  return body;
}

function readMetrics(metricsPath) {
  if (!metricsPath || !fs.existsSync(metricsPath)) return {};
  try {
    return JSON.parse(fs.readFileSync(metricsPath, 'utf8'));
  } catch {
    return {};
  }
}

function writeMetrics(metricsPath, metrics) {
  if (!metricsPath) return;
  fs.writeFileSync(metricsPath, `${JSON.stringify(metrics, null, 2)}\n`);
}

function firstNumber(...values) {
  for (const value of values) {
    if (value == null || value === '') continue;
    const number = Number(value);
    if (Number.isFinite(number)) return number;
  }
  return null;
}

function formatDuration(ms) {
  if (!Number.isFinite(Number(ms))) return 'unknown';
  return `${Math.max(0, Math.round(Number(ms) / 1000))}s`;
}

function renderComment(c) {
  if (c.category === 'large-lean-hotspots') {
    // P3: scout markers are coverage QUESTIONS, not findings. Lead with the
    // caveat so a controller or human never mistakes one for a review verdict.
    return `🟡 **OCR scout — question de triage (non-review)${badge(c)}**\n\n`
      + `_Question de couverture pour le reviewer humain/Codex — pas une review sémantique finale ni une approbation._\n\n`
      + `${String(c.content || '').trim()}`;
  }
  const label = c.category === 'packet-semantic'
    ? `**OpenCodeReview — packet semantic review${badge(c)}**`
    : `**OpenCodeReview${badge(c)}**`;
  let body = `${label}\n\n${String(c.content || '').trim()}`;
  if (c.suggestion_code) {
    body += `\n\nSuggested change:\n${fenced(String(c.suggestion_code))}`;
  }
  return body;
}

function renderInlineFallback(selected) {
  if (!selected.length) return 'No positioned inline findings were selected.';
  let body = '### Inline findings that could not be posted\n\n';
  for (const c of selected) {
    body += `- **${escapeMd(c.path)}:${c.line}** — ${escapeMd(firstLine(c.body.replace(/\*\*OpenCodeReview[^\n]*\*\*\n\n?/, '')))}\n`;
  }
  return body.trim();
}

// Router mode names are pipeline internals, not review categories; keep the
// badge to reviewer-meaningful bits (severity, semantic categories).
const MODE_LIKE_CATEGORIES = new Set([
  'large-lean-hotspots',
  'packetized_review',
  'small-lean',
  'standard',
  'workflow-scripts',
]);

function badge(c) {
  const bits = [c.category, c.severity]
    .filter(Boolean)
    .map(String)
    .filter(bit => !MODE_LIKE_CATEGORIES.has(bit));
  return bits.length ? ` [${bits.join(' · ')}]` : '';
}

function firstLine(s) {
  return String(s).trim().split(/\r?\n/)[0].slice(0, 240);
}

function fenced(s) {
  const ticks = String(s).includes('```') ? '````' : '```';
  return `${ticks}\n${String(s).slice(0, 8000)}\n${ticks}`;
}

function escapeMd(s) {
  return String(s).replace(/[<>@]/g, ch => ({ '<': '&lt;', '>': '&gt;', '@': '&#64;' }[ch]));
}

module.exports.isRetryableResult = isRetryableResult;
module.exports.renderComment = renderComment;
module.exports.buildReviewBody = buildReviewBody;
module.exports.extractOcrSummary = extractOcrSummary;
module.exports.buildDedupKey = buildDedupKey;
module.exports.buildLargeLeanScoutDedupDiscriminator = buildLargeLeanScoutDedupDiscriminator;
