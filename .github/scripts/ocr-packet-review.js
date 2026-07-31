'use strict';

// P1: bounded per-packet semantic review for large-lean PRs.
//
// The router's large-lean route used to dead-end after scout triage
// (`strong_review_status: blocked_packet_input`). This runner closes the loop:
// for each scout-selected packet group it executes the real `ocr review`
// scoped to that group's files. `ocr` has no --include flag, so scoping works
// by excluding the exact complement — every OTHER changed supported file from
// the same diff. The exclusion list is finite and derived from the diff, so a
// packet run reviews precisely its files' hunks with full-file context.
//
// Failure isolation mirrors the scout lens fan-out: one packet's failure never
// discards another packet's findings, and every outcome lands in the result
// summary so the posting step can report honest covered/total numbers.

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const PER_PACKET_TIMEOUT_MINUTES = Number(process.env.OCR_PACKET_TIMEOUT_MINUTES || 10);
// Hard node-side ceiling: the CLI timeout is advisory inside the tool; a hung
// provider call must not consume the whole 45-minute job budget.
const PER_PACKET_KILL_MS = (PER_PACKET_TIMEOUT_MINUTES + 3) * 60_000;

function main() {
  const planPath = requiredEnv('OCR_PACKET_PLAN_PATH');
  const resultPath = requiredEnv('OCR_RESULT_PATH');
  const metricsPath = process.env.OCR_METRICS_PATH || '';
  const rulesPath = requiredEnv('OCR_RULES_PATH');

  const plan = readJson(planPath);
  const result = readJson(resultPath);
  const groups = Array.isArray(plan.groups) ? plan.groups : [];

  const perGroup = [];
  let covered = 0;
  for (const group of groups) {
    const outcome = reviewGroup(plan, group, rulesPath);
    perGroup.push(outcome);
    if (outcome.status === 'success') {
      covered += 1;
      const comments = Array.isArray(outcome.comments) ? outcome.comments : [];
      for (const comment of comments) {
        result.comments = result.comments || [];
        result.comments.push({ ...comment, category: 'packet-semantic' });
      }
    }
    console.log(`packet group [${group.files.join(', ')}]: ${outcome.status}${outcome.findings != null ? ` (${outcome.findings} finding(s))` : ''}`);
  }

  result.summary = result.summary || {};
  result.summary.packet_semantic = {
    covered_groups: covered,
    total_groups: groups.length,
    total_groups_available: plan.total_groups_available ?? groups.length,
    per_group: perGroup.map(g => ({
      files: g.files,
      packet_ids: g.packet_ids,
      status: g.status,
      findings: g.findings ?? 0,
      error: g.error,
    })),
  };
  if (covered > 0) {
    result.status = 'scout_triage_with_packet_review';
  }
  fs.writeFileSync(resultPath, `${JSON.stringify(result, null, 2)}\n`);

  if (metricsPath && fs.existsSync(metricsPath)) {
    try {
      const metrics = readJson(metricsPath);
      metrics.packet_semantic = result.summary.packet_semantic;
      fs.writeFileSync(metricsPath, `${JSON.stringify(metrics, null, 2)}\n`);
    } catch (err) {
      console.warn(`metrics update skipped: ${err.message}`);
    }
  }

  console.log(`packet semantic review: ${covered}/${groups.length} group(s) covered`);
}

function reviewGroup(plan, group, rulesPath) {
  const base = { files: group.files, packet_ids: group.packet_ids };
  const outPath = path.join(process.env.RUNNER_TEMP || '.', `ocr-packet-${(group.packet_ids || ['g'])[0]}.json`);
  const args = [
    'review',
    '--from', plan.diff_base,
    '--to', plan.head,
    '--format', 'json',
    '--audience', 'agent',
    '--rule', rulesPath,
    '--concurrency', '1',
    '--timeout', String(PER_PACKET_TIMEOUT_MINUTES),
  ];
  const exclude = Array.isArray(group.exclude) ? group.exclude.filter(Boolean) : [];
  if (exclude.length > 0) {
    args.push('--exclude', exclude.join(','));
  }
  try {
    const stdout = execFileSync('ocr', args, {
      encoding: 'utf8',
      timeout: PER_PACKET_KILL_MS,
      maxBuffer: 32 * 1024 * 1024,
      env: process.env,
    });
    fs.writeFileSync(outPath, stdout);
    const parsed = JSON.parse(stdout);
    const comments = Array.isArray(parsed.comments) ? parsed.comments : [];
    return { ...base, status: 'success', findings: comments.length, comments };
  } catch (err) {
    const detail = String(err && err.message ? err.message : err).slice(0, 300);
    // execFileSync surfaces its timeout as code ETIMEDOUT (killed stays false
    // on some platforms) — observed live on PR #2219 group 2. Label budget
    // exhaustion as timeout so the summary suggests raising
    // OCR_PACKET_TIMEOUT_MINUTES rather than implying a crash.
    const timedOut = Boolean(err && (err.killed || err.code === 'ETIMEDOUT' || /ETIMEDOUT/.test(detail)));
    const status = timedOut ? 'timeout' : 'error';
    return { ...base, status, error: detail };
  }
}

function readJson(file) {
  return JSON.parse(fs.readFileSync(file, 'utf8'));
}

function requiredEnv(name) {
  const value = process.env[name];
  if (!value) throw new Error(`Missing required env: ${name}`);
  return value;
}

main();
