'use strict';

const fs = require('fs');

module.exports = async function postOcrReview({ github, context, core }) {
  const owner = context.repo.owner;
  const repo = context.repo.repo;
  const pull_number = Number(process.env.OCR_PR_NUMBER);
  const commit_id = process.env.OCR_HEAD_SHA;
  const resultPath = process.env.OCR_RESULT_PATH;
  const stderrPath = process.env.OCR_STDERR_PATH;
  const maxInline = Number(process.env.OCR_MAX_INLINE_COMMENTS || 20);
  const successTag = `<!-- paloma-ocr-review:${commit_id}:success -->`;
  const retryableTag = `<!-- paloma-ocr-review:${commit_id}:retryable-failure -->`;

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
  const body = buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr });

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
  return status === 'error' || status === 'failed' || status === 'failure';
}

function toReviewComment(c) {
  return {
    path: c.path,
    line: c.line,
    side: c.side,
    body: c.body,
  };
}

function buildReviewBody({ tag, result, comments, selected, overflow, summaryOnly, warnings, stderr }) {
  const status = result.status || 'unknown';
  const message = result.message || '';
  const summary = result.summary || {};
  const tokens = summary.total_tokens ? ` · ${summary.total_tokens} tokens` : '';
  const files = summary.files_reviewed != null ? `${summary.files_reviewed} files` : 'files unknown';
  const toolCalls = result.tool_calls?.total != null ? ` · ${result.tool_calls.total} tool calls` : '';

  let body = `${tag}\n## OpenCodeReview first-pass review\n\n`;
  body += `Status: **${escapeMd(status)}** · ${comments.length} finding(s) · ${files}${tokens}${toolCalls}\n\n`;

  if (message) body += `${escapeMd(message)}\n\n`;
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

  body += `_Pilot mode: advisory only. Codex Review remains the merge gate._`;
  return body;
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
  return String(s).replace(/[<>]/g, ch => ({ '<': '&lt;', '>': '&gt;' }[ch]));
}
