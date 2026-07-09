'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const ROUTER_VERSION = 'router-v1';
const THRESHOLDS = Object.freeze({
  smallLeanFiles: 1,
  smallChangedLines: 300,
  mediumLeanFiles: 2,
  mediumChangedLines: 800,
  largeLeanFiles: 3,
  largeChangedLines: 800,
});

function main() {
  const baseRef = requiredEnv('BASE_REF');
  const headSha = requiredEnv('HEAD_SHA');
  const prNumber = process.env.OCR_PR_NUMBER || '';
  const metricsPath = process.env.OCR_METRICS_PATH || path.join(process.env.RUNNER_TEMP || '.', 'ocr-metrics.json');
  const resultPath = process.env.OCR_RESULT_PATH || path.join(process.env.RUNNER_TEMP || '.', 'ocr-result.json');
  const outputPath = process.env.GITHUB_OUTPUT || '';

  const startedAt = new Date().toISOString();
  const diff = loadDiff(`origin/${baseRef}`, headSha);
  const decision = decideRoute(diff.files);
  const metrics = buildMetrics({
    prNumber,
    headSha,
    baseRef,
    startedAt,
    decision,
    diff,
  });

  fs.writeFileSync(metricsPath, `${JSON.stringify(metrics, null, 2)}\n`);

  if (!decision.shouldRunOcr) {
    fs.writeFileSync(resultPath, `${JSON.stringify(buildSyntheticResult(decision, metrics), null, 2)}\n`);
  }

  writeOutputs(outputPath, {
    mode: decision.mode,
    should_run_ocr: String(decision.shouldRunOcr),
    reason: decision.reason,
    concurrency: String(decision.ocr.concurrency),
    timeout: String(decision.ocr.timeout),
    background_chars: String(decision.ocr.backgroundChars),
    metrics_path: metricsPath,
    result_path: resultPath,
    router_version: ROUTER_VERSION,
  });

  console.log(`OCR route: ${decision.mode} (${decision.reason})`);
  console.log(`Changed files: ${diff.files.length}; supported: ${decision.counts.supported}; Lean: ${decision.counts.lean}; changed lines: ${decision.changedLines}`);
}

function loadDiff(base, head) {
  const output = git(['diff', '--numstat', '--find-renames', base, head, '--']);
  const files = output.split(/\r?\n/).filter(Boolean).map(parseNumstatLine).filter(Boolean);
  return { base, head, files };
}

function parseNumstatLine(line) {
  const parts = line.split('\t');
  if (parts.length < 3) return null;
  const added = parts[0] === '-' ? 0 : Number(parts[0]);
  const deleted = parts[1] === '-' ? 0 : Number(parts[1]);
  const rawPath = parts.slice(2).join('\t');
  const filePath = normalizeDiffPath(rawPath);
  return {
    path: filePath,
    added: Number.isFinite(added) ? added : 0,
    deleted: Number.isFinite(deleted) ? deleted : 0,
    changed: (Number.isFinite(added) ? added : 0) + (Number.isFinite(deleted) ? deleted : 0),
    category: categorize(filePath),
    supported: isSupported(filePath),
  };
}

function normalizeDiffPath(rawPath) {
  const arrow = rawPath.match(/\{(.+) => (.+)\}/);
  if (arrow) {
    return rawPath.replace(/\{(.+) => (.+)\}/, arrow[2]).replace(/^\s+|\s+$/g, '');
  }
  const rename = rawPath.match(/^(.+) => (.+)$/);
  if (rename) return rename[2].trim();
  return rawPath.trim();
}

function decideRoute(files) {
  const included = files.filter(f => !isExcluded(f.path));
  const supportedFiles = included.filter(f => f.supported);
  const leanFiles = supportedFiles.filter(f => f.category === 'lean');
  const changedLines = supportedFiles.reduce((sum, f) => sum + f.changed, 0);
  const counts = countCategories(included, supportedFiles);
  const largestFiles = [...supportedFiles].sort((a, b) => b.changed - a.changed).slice(0, 8);

  if (supportedFiles.length === 0) {
    return route({
      mode: 'skipped',
      shouldRunOcr: false,
      reason: 'No changed files matched OCR include rules.',
      counts,
      changedLines,
      largestFiles,
      ocr: { concurrency: 0, timeout: 0, backgroundChars: 0 },
    });
  }

  if (leanFiles.length > 0 && (leanFiles.length >= THRESHOLDS.largeLeanFiles || changedLines > THRESHOLDS.largeChangedLines)) {
    return route({
      mode: 'guarded-large-lean',
      shouldRunOcr: false,
      reason: `Lean OCR guard: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
      counts,
      changedLines,
      largestFiles,
      ocr: { concurrency: 0, timeout: 0, backgroundChars: 0 },
    });
  }

  if (leanFiles.length > 0 && (leanFiles.length > THRESHOLDS.smallLeanFiles || changedLines > THRESHOLDS.smallChangedLines)) {
    return route({
      mode: 'bounded-lean',
      shouldRunOcr: true,
      reason: `Medium Lean diff routed with reduced OCR bounds: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
      counts,
      changedLines,
      largestFiles,
      ocr: { concurrency: 1, timeout: 12, backgroundChars: 800 },
    });
  }

  return route({
    mode: 'normal',
    shouldRunOcr: true,
    reason: leanFiles.length > 0
      ? `Small Lean diff: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`
      : 'Supported non-Lean diff; OCR enabled.',
    counts,
    changedLines,
    largestFiles,
    ocr: { concurrency: 3, timeout: 20, backgroundChars: 1200 },
  });
}

function route(decision) {
  return { ...decision, thresholds: THRESHOLDS, routerVersion: ROUTER_VERSION };
}

function countCategories(included, supportedFiles) {
  const counts = {
    total: included.length,
    supported: supportedFiles.length,
    lean: 0,
    trustDocs: 0,
    workflowScripts: 0,
    contracts: 0,
    docs: 0,
    other: 0,
  };
  for (const file of supportedFiles) {
    if (file.category === 'lean') counts.lean += 1;
    else if (file.category === 'trust-doc') counts.trustDocs += 1;
    else if (file.category === 'workflow-script') counts.workflowScripts += 1;
    else if (file.category === 'contract') counts.contracts += 1;
    else if (file.category === 'doc') counts.docs += 1;
    else counts.other += 1;
  }
  return counts;
}

function categorize(filePath) {
  const base = path.posix.basename(filePath);
  if (filePath.endsWith('.lean')) return 'lean';
  if (['AUDIT.md', 'TRUST_ASSUMPTIONS.md', 'AXIOMS.md'].includes(base)) return 'trust-doc';
  if (filePath.startsWith('.github/')) return 'workflow-script';
  if (/\.(sol|yul|cairo)$/.test(filePath)) return 'contract';
  if (filePath === 'README.md' || (filePath.startsWith('docs/') && filePath.endsWith('.md'))) return 'doc';
  if (/\.(py|sh|bash|js|ts|json|ya?ml|toml)$/.test(filePath)) return 'workflow-script';
  return 'other';
}

function isSupported(filePath) {
  if (isExcluded(filePath)) return false;
  const base = path.posix.basename(filePath);
  return filePath.endsWith('.lean') ||
    /\.(sol|yul|cairo)$/.test(filePath) ||
    ['AUDIT.md', 'TRUST_ASSUMPTIONS.md', 'AXIOMS.md', 'README.md'].includes(base) ||
    (filePath.startsWith('docs/') && filePath.endsWith('.md')) ||
    filePath.startsWith('.github/');
}

function isExcluded(filePath) {
  return filePath.includes('/.lake/') ||
    filePath.includes('/lake-packages/') ||
    filePath.includes('/node_modules/') ||
    filePath.includes('/dist/') ||
    filePath.includes('/build/') ||
    filePath.includes('/generated/') ||
    filePath.startsWith('.lake/') ||
    filePath.startsWith('lake-packages/') ||
    filePath.startsWith('node_modules/') ||
    filePath.startsWith('dist/') ||
    filePath.startsWith('build/') ||
    filePath.startsWith('generated/') ||
    filePath.endsWith('.lock');
}

function buildMetrics({ prNumber, headSha, baseRef, startedAt, decision, diff }) {
  return {
    schema_version: 1,
    router_version: ROUTER_VERSION,
    pr_number: prNumber ? Number(prNumber) : null,
    head_sha: headSha,
    base_ref: baseRef,
    started_at: startedAt,
    mode: decision.mode,
    reason: decision.reason,
    thresholds: decision.thresholds,
    changed_files: {
      counts: decision.counts,
      total_changed_lines: decision.changedLines,
      largest: decision.largestFiles.map(f => ({
        path: f.path,
        added: f.added,
        deleted: f.deleted,
        changed: f.changed,
        category: f.category,
      })),
    },
    ocr: {
      attempted: decision.shouldRunOcr,
      status: decision.shouldRunOcr ? 'pending' : decision.mode,
      comments_count: 0,
      files_reviewed: null,
      total_tokens: null,
      tool_calls_total: null,
      warnings_count: 0,
      duration_ms: null,
    },
    diff_base: diff.base,
    diff_head: diff.head,
  };
}

function buildSyntheticResult(decision, metrics) {
  return {
    status: decision.mode,
    message: decision.reason,
    comments: [],
    warnings: decision.mode === 'guarded-large-lean'
      ? [{ type: 'routing', message: 'Full OCR skipped by Lean scaling guard.' }]
      : [],
    summary: {
      files_reviewed: 0,
      total_tokens: 0,
      mode: decision.mode,
      router_version: ROUTER_VERSION,
      changed_files: metrics.changed_files,
      thresholds: decision.thresholds,
    },
    tool_calls: { total: 0 },
  };
}

function writeOutputs(outputPath, values) {
  const lines = Object.entries(values).map(([key, value]) => `${key}=${String(value).replace(/\n/g, ' ')}`);
  if (outputPath) fs.appendFileSync(outputPath, `${lines.join('\n')}\n`);
}

function git(args) {
  return execFileSync('git', args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
}

function requiredEnv(name) {
  const value = process.env[name];
  if (!value) throw new Error(`${name} is required`);
  return value;
}

if (require.main === module) {
  main();
}

module.exports = {
  ROUTER_VERSION,
  THRESHOLDS,
  categorize,
  decideRoute,
  isSupported,
  parseNumstatLine,
  buildSyntheticResult,
  buildMetrics,
};
