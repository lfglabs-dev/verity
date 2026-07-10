'use strict';

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
  const dedupKey = `${commit_id}:${rulesHash}:${reviewerVersion}:${routerVersion}:${mode}`;
  const successTag = `<!-- paloma-ocr-review:${dedupKey}:success -->`;
  const retryableTag = `<!-- paloma-ocr-review:${dedupKey}:retryable-failure -->`;

  if (!pull_number || !commit_id) {
    throw new Error('OCR_PR_NUMBER and OCR_HEAD_SHA are required');
  }

  const alreadyPosted = await hasExistingTag(github, { owner, repo, pull_number, tag: successTag });
  if (alreadyPosted) {
    core.notice(`Successful OCR review for ${commit_id} was already posted; skipping duplicate.`);
    return;
  }

  const raw = fs.existsSync(resultPath) ? fs.readFileSync(resultPath, 'utf8') : '';
  const stderr = fs.existsSync(stderrPath) ? fs.readFileSync(stderrPath, 'utf8').trim() : '';
  let result;
  try {
    result = JSON.parse(raw);
  } catch (err) {
    writeMetrics(metricsPath, enrichMetrics(readMetrics(metricsPath), {
      mode,
      result: { status: 'invalid_json', comments: [], warnings: [] },
      stderr,
      retryable: true,
    }));
    await github.rest.issues.createComment({
      owner, repo, issue_number: pull_number,
      body: `${retryableTag}\n⚠️ **OpenCodeReview failed to produce valid JSON.**\n\n${stderr ? fenced(stderr) : 'No stderr captured.'}`,
    });
    return;
  }

  const comments = Array.isArray(result.comments) ? result.comments : [];
  const warnings = Array.isArray(result.warnings) ? result.warnings : [];
  const usable = [];
  const summaryOnly = [];
  const retryableResult = isRetryableResult(result);
  const metrics = enrichMetrics(readMetrics(metricsPath), { mode, result, stderr, retryable: retryableResult });
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
    ? buildReviewBody({ tag, result, comments, selected: [], overflow: [...selected, ...overflow], summaryOnly, warnings, stderr, metrics })
    : buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr, metrics });

  if (retryableResult) {
    await github.rest.issues.createComment({
      owner,
      repo,
      issue_number: pull_number,
      body: `${body}\n\n⚠️ OCR did not complete successfully; this run is intentionally retryable for the same commit.`,
    });
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
};

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

function isRetryableResult(result) {
  const status = String(result.status || '').toLowerCase();
  return status === 'error' || status === 'failed' || status === 'failure' || status === 'completed_with_errors';
}

function toReviewComment(c) {
  return {
    path: c.path,
    line: c.line,
    side: c.side,
    body: c.body,
  };
}

function buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr, metrics }) {
  const status = result.status || 'unknown';
  const message = result.message || '';
  const summary = result.summary || {};
  const extracted = extractOcrSummary(result);
  const tokens = extracted.totalTokens != null ? ` · ${extracted.totalTokens} tokens` : '';
  const files = extracted.filesReviewed != null ? `${extracted.filesReviewed} files` : 'files unknown';
  const toolCalls = extracted.toolCallsTotal != null ? ` · ${extracted.toolCallsTotal} tool calls` : '';

  let body = `${tag}\n## OpenCodeReview first-pass review\n\n`;
  body += `Status: **${escapeMd(status)}** · Mode: **${escapeMd(metrics?.mode || summary.mode || 'unknown')}** · ${comments.length} finding(s) · ${files}${tokens}${toolCalls}\n\n`;

  if (message) body += `${escapeMd(message)}\n\n`;
  if ((metrics?.mode || summary.mode) === 'large-lean-hotspots') {
    body += `⚠️ Large Lean scout mode covers ranked packets/checklists only; it is not a full-file OCR review and must not be read as LGTM.\n`;
  }
  if (selected.length > 0) body += `✅ Posted ${selected.length} inline comment(s).\n`;
  if (overflow.length > 0) body += `📝 ${overflow.length} additional positioned finding(s) omitted from inline comments to avoid spam.\n`;
  if (summaryOnly.length > 0) body += `📝 ${summaryOnly.length} finding(s) had no resolvable line and are summarized below.\n`;
  if (warnings.length > 0) body += `⚠️ ${warnings.length} OCR warning(s) reported.\n`;
  body += `\n`;

  const summarized = [...summaryOnly, ...overflow].slice(0, 20);
  if (summarized.length > 0) {
    body += `### Summary-only findings\n\n`;
    for (const c of summarized) {
      body += `- **${escapeMd(c.path || 'unknown')}**${badge(c)} — ${escapeMd(firstLine(c.content || ''))}\n`;
    }
    body += `\n`;
  }

  if (warnings.length > 0) {
    body += `### Warnings\n\n`;
    for (const w of warnings.slice(0, 10)) {
      body += `- **${escapeMd(w.type || 'warning')}** ${escapeMd(w.file || '')}: ${escapeMd(firstLine(w.message || ''))}\n`;
    }
    body += `\n`;
  }

  if (stderr) {
    const interesting = stderr.split('\n').filter(line => /warning|error|failed|fatal/i.test(line)).slice(0, 20).join('\n');
    if (interesting) {
      body += `<details><summary>OCR stderr highlights</summary>\n\n${fenced(interesting)}\n</details>\n\n`;
    }
  }

  body += renderMetrics(metrics, result);
  body += renderPacketCoverage(metrics, result);
  body += `_Pilot mode: advisory only. Codex Review remains the merge gate._`;
  return body;
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
      const question = packet.scout_question ? `; ask: ${packet.scout_question}` : '';
      body += `  - ${escapeMd(packet.path)}:${packet.start_line ?? '?'} score ${packet.score ?? '?'} — ${escapeMd(signals + question)}\n`;
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
  let body = `**OpenCodeReview${badge(c)}**\n\n${String(c.content || '').trim()}`;
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

function badge(c) {
  const bits = [c.category, c.severity].filter(Boolean).map(String);
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
module.exports.buildReviewBody = buildReviewBody;
module.exports.extractOcrSummary = extractOcrSummary;
