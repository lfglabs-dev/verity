'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const ROUTER_VERSION = 'router-v2';
const THRESHOLDS = Object.freeze({
  smallLeanFiles: 1,
  smallChangedLines: 300,
  mediumLeanFiles: 2,
  mediumChangedLines: 800,
  largeLeanFiles: 3,
  largeChangedLines: 800,
  packetMaxFiles: 12,
  packetMaxChangedLines: 2500,
  packetMaxCount: 8,
  packetContextLines: 12,
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
  const hunksByPath = loadDiffHunks(base, head);
  for (const file of files) {
    file.hunks = hunksByPath.get(file.path) || [];
    file.risk = scoreFileRisk(file);
  }
  return { base, head, files };
}

function loadDiffHunks(base, head) {
  const output = git(['diff', '--find-renames', `--unified=${THRESHOLDS.packetContextLines}`, base, head, '--']);
  return parseUnifiedDiff(output);
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

function parseUnifiedDiff(diffText) {
  const byPath = new Map();
  let currentPath = null;
  let currentHunk = null;
  let oldLine = 0;
  let newLine = 0;

  for (const line of diffText.split(/\r?\n/)) {
    if (line.startsWith('diff --git ')) {
      currentPath = null;
      currentHunk = null;
      continue;
    }
    if (line.startsWith('+++ ')) {
      const raw = line.slice(4).trim();
      if (raw === '/dev/null') {
        currentPath = null;
        continue;
      }
      currentPath = raw.replace(/^b\//, '');
      if (!byPath.has(currentPath)) byPath.set(currentPath, []);
      continue;
    }
    const hunkHeader = line.match(/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,(\d+))? @@(.*)$/);
    if (hunkHeader && currentPath) {
      oldLine = Number(hunkHeader[1]);
      newLine = Number(hunkHeader[2]);
      currentHunk = {
        path: currentPath,
        oldStart: oldLine,
        newStart: newLine,
        newSpan: Number(hunkHeader[3] || 1),
        header: hunkHeader[4].trim(),
        lines: [],
      };
      byPath.get(currentPath).push(currentHunk);
      continue;
    }
    if (!currentHunk || line.startsWith('\\ No newline')) continue;

    const prefix = line[0] || ' ';
    const text = line.slice(1);
    if (prefix === '+') {
      currentHunk.lines.push({ type: 'add', newLine, oldLine: null, text });
      newLine += 1;
    } else if (prefix === '-') {
      currentHunk.lines.push({ type: 'del', newLine: null, oldLine, text });
      oldLine += 1;
    } else {
      currentHunk.lines.push({ type: 'ctx', newLine, oldLine, text });
      oldLine += 1;
      newLine += 1;
    }
  }

  return byPath;
}

function decideRoute(files) {
  const included = files.filter(f => !isExcluded(f.path));
  const supportedFiles = included.filter(f => f.supported);
  const leanFiles = supportedFiles.filter(f => f.category === 'lean');
  const changedLines = supportedFiles.reduce((sum, f) => sum + f.changed, 0);
  const counts = countCategories(included, supportedFiles);
  const largestFiles = [...supportedFiles].sort((a, b) => b.changed - a.changed).slice(0, 8);
  const packets = buildReviewPackets(supportedFiles);

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

  if (leanFiles.length > 0 && (leanFiles.length > THRESHOLDS.packetMaxFiles || changedLines > THRESHOLDS.packetMaxChangedLines)) {
    return route({
      mode: 'guarded-oversized-lean',
      shouldRunOcr: false,
      reason: `Lean packet budget exceeded: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
      counts,
      changedLines,
      largestFiles,
      packets,
      ocr: { concurrency: 0, timeout: 0, backgroundChars: 0 },
    });
  }

  if (leanFiles.length > 0 && (leanFiles.length >= THRESHOLDS.largeLeanFiles || changedLines > THRESHOLDS.largeChangedLines)) {
    if (packets.length === 0) {
      return route({
        mode: 'guarded-unpacketized-lean',
        shouldRunOcr: false,
        reason: `Lean diff exceeded full OCR thresholds, but no safe review packets could be produced: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
        counts,
        changedLines,
        largestFiles,
        packets,
        ocr: { concurrency: 0, timeout: 0, backgroundChars: 0 },
      });
    }
    return route({
      mode: 'packetized-lean',
      shouldRunOcr: false,
      reason: `Large Lean diff routed to bounded packet review: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
      counts,
      changedLines,
      largestFiles,
      packets,
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
      packets,
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
    packets,
    ocr: { concurrency: 3, timeout: 20, backgroundChars: 1200 },
  });
}

function route(decision) {
  return { ...decision, thresholds: THRESHOLDS, routerVersion: ROUTER_VERSION };
}

function buildReviewPackets(files) {
  const packets = [];
  for (const file of files) {
    if (!file.supported || !Array.isArray(file.hunks)) continue;
    for (const hunk of file.hunks) {
      const signals = detectSignals(file, hunk);
      const pathRisk = scorePathRisk(file.path);
      const churnRisk = Math.min(10, Math.floor((hunk.lines.filter(l => l.type !== 'ctx').length) / 20));
      const score = pathRisk + churnRisk + signals.reduce((sum, s) => sum + s.weight, 0);
      if (score <= 0 && file.category !== 'lean') continue;

      const addedLines = hunk.lines.filter(l => l.type === 'add');
      const changedLines = hunk.lines.filter(l => l.type !== 'ctx');
      const anchor = firstChangedNewLine(hunk) || hunk.newStart || 1;
      packets.push({
        path: file.path,
        start_line: anchor,
        end_line: lastChangedNewLine(hunk) || anchor,
        score,
        category: file.category,
        signals: signals.map(s => s.name),
        summary: summarizePacket(file, hunk, signals, changedLines.length),
        added_sample: addedLines.slice(0, 8).map(l => ({ line: l.newLine, text: l.text.slice(0, 220) })),
        changed_lines: changedLines.length,
      });
    }
  }

  return packets
    .sort((a, b) => b.score - a.score || b.changed_lines - a.changed_lines || a.path.localeCompare(b.path))
    .slice(0, THRESHOLDS.packetMaxCount);
}

function scoreFileRisk(file) {
  return scorePathRisk(file.path) + Math.min(20, Math.floor((file.changed || 0) / 100));
}

function scorePathRisk(filePath) {
  if (/^Compiler\/Proofs\/YulGeneration\//.test(filePath)) return 35;
  if (/^Compiler\/Proofs\//.test(filePath)) return 30;
  if (/^Compiler\//.test(filePath)) return 25;
  if (/^IRGeneration\//.test(filePath) || /\/IRGeneration\//.test(filePath)) return 25;
  if (/^Semantics\//.test(filePath) || /\/Semantics\//.test(filePath)) return 25;
  if (/TRUST|AXIOM|AUDIT/.test(path.posix.basename(filePath))) return 24;
  if (/^docs\/.*(trust|axiom|audit|spec)/i.test(filePath)) return 18;
  if (filePath.endsWith('.lean')) return 12;
  if (filePath.startsWith('.github/')) return 10;
  return 0;
}

function detectSignals(file, hunk) {
  const signals = new Map();
  const add = (name, weight) => signals.set(name, { name, weight: Math.max(weight, signals.get(name)?.weight || 0) });
  const added = hunk.lines.filter(l => l.type === 'add').map(l => l.text);
  const deleted = hunk.lines.filter(l => l.type === 'del').map(l => l.text);
  const allChanged = [...added, ...deleted];

  if (added.some(line => /\b(sorry|admit)\b/.test(line))) add('introduced sorry/admit', 80);
  if (added.some(line => /^\s*axiom\b/.test(line) || /\baxiom\b/.test(line))) add('introduced/changed axiom', 75);
  if (added.some(line => /\bunsafe\b/.test(line))) add('introduced unsafe', 55);
  if (allChanged.some(line => /^\s*import\s+/.test(line))) add('changed imports', 30);
  if (allChanged.some(line => publicDeclPattern().test(line))) add('public declaration/signature changed', 34);
  if (file.category === 'trust-doc') add('trust-boundary docs drift', 38);
  if (file.category === 'doc' && /(trust|axiom|audit|sound|semantic|proof)/i.test(file.path)) add('trust/proof docs drift', 25);
  if (deleted.length >= 80 || deleted.join('\n').length > 6000) add('large deleted proof obligation', 35);
  if (deleted.some(line => publicDeclPattern().test(line)) && added.some(line => publicDeclPattern().test(line))) {
    add('theorem/public statement changed', 45);
  }
  if (changedTheoremStatements(deleted, added).length > 0) add('theorem statement changed/possibly weakened', 65);

  return [...signals.values()].sort((a, b) => b.weight - a.weight || a.name.localeCompare(b.name));
}

function publicDeclPattern() {
  return /^\s*(?:theorem|lemma|def|abbrev|axiom|opaque|instance|class|structure|inductive)\s+[A-Za-z0-9_'.]+/;
}

function changedTheoremStatements(deleted, added) {
  const removed = new Map();
  for (const line of deleted) {
    const match = line.match(/^\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)\b(.*)$/);
    if (match) removed.set(match[2], line.trim());
  }
  const changed = [];
  for (const line of added) {
    const match = line.match(/^\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)\b(.*)$/);
    if (match && removed.has(match[2]) && removed.get(match[2]) !== line.trim()) {
      changed.push(match[2]);
    }
  }
  return changed;
}

function summarizePacket(file, hunk, signals, changedCount) {
  const signalText = signals.length ? signals.map(s => s.name).join(', ') : 'hotspot path/churn';
  return `${signalText}; ${changedCount} changed line(s) near ${file.path}:${firstChangedNewLine(hunk) || hunk.newStart || 1}`;
}

function firstChangedNewLine(hunk) {
  const changed = hunk.lines.find(l => l.type === 'add' && Number.isFinite(l.newLine)) ||
    hunk.lines.find(l => l.type === 'ctx' && Number.isFinite(l.newLine));
  return changed?.newLine || null;
}

function lastChangedNewLine(hunk) {
  for (let i = hunk.lines.length - 1; i >= 0; i -= 1) {
    const line = hunk.lines[i];
    if ((line.type === 'add' || line.type === 'ctx') && Number.isFinite(line.newLine)) return line.newLine;
  }
  return null;
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
        risk: f.risk || scorePathRisk(f.path),
      })),
    },
    packet_review: shouldReportPacketReview(decision) ? {
      enabled: decision.mode === 'packetized-lean',
      packets_selected: decision.packets?.length || 0,
      packet_budget: THRESHOLDS.packetMaxCount,
      packets: (decision.packets || []).map(p => ({
        path: p.path,
        start_line: p.start_line,
        end_line: p.end_line,
        score: p.score,
        category: p.category,
        signals: p.signals,
        summary: p.summary,
        changed_lines: p.changed_lines,
      })),
      residual_risk: packetResidualRisk(decision),
    } : null,
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
  if (decision.mode === 'packetized-lean') {
    return buildPacketizedResult(decision, metrics);
  }

  return {
    status: decision.mode,
    message: decision.reason,
    comments: [],
    warnings: ['guarded-oversized-lean', 'guarded-unpacketized-lean'].includes(decision.mode)
      ? [{ type: 'routing', message: 'Diff exceeded bounded packet review capability; full OCR not attempted.' }]
      : [],
    summary: {
      files_reviewed: 0,
      total_tokens: 0,
      mode: decision.mode,
      router_version: ROUTER_VERSION,
      changed_files: metrics.changed_files,
      packet_review: metrics.packet_review,
      thresholds: decision.thresholds,
    },
    tool_calls: { total: 0 },
  };
}

function buildPacketizedResult(decision, metrics) {
  const packets = decision.packets || [];
  return {
    status: 'packetized_review',
    message: `${decision.reason} Full-file OCR was not attempted; this is deterministic hotspot coverage, not complete review coverage.`,
    comments: packets.map(packet => ({
      path: packet.path,
      start_line: packet.start_line,
      end_line: packet.end_line,
      category: 'packetized-lean',
      severity: packet.score >= 90 ? 'high' : packet.score >= 60 ? 'medium' : 'low',
      content: renderPacketFinding(packet),
    })),
    warnings: [{
      type: 'coverage',
      message: 'Packetized Lean review covers ranked hotspots only. Codex/human review must cover skipped hunks and proof obligations.',
    }],
    summary: {
      files_reviewed: uniqueCount(packets.map(p => p.path)),
      total_tokens: 0,
      mode: decision.mode,
      router_version: ROUTER_VERSION,
      changed_files: metrics.changed_files,
      packet_review: metrics.packet_review,
      thresholds: decision.thresholds,
    },
    tool_calls: { total: 0 },
  };
}

function renderPacketFinding(packet) {
  const lines = [
    `Bounded Lean packet selected for review: ${packet.summary}.`,
    `Risk signals: ${packet.signals.length ? packet.signals.join(', ') : 'hotspot path/churn'}.`,
  ];
  if (packet.added_sample.length > 0) {
    lines.push('Added-line sample:');
    for (const sample of packet.added_sample.slice(0, 5)) {
      lines.push(`- L${sample.line}: ${sample.text}`);
    }
  }
  lines.push('This packet is a coverage marker and deterministic checklist item; it is not a full OCR semantic review.');
  return lines.join('\n');
}

function packetResidualRisk(decision) {
  if (decision.mode === 'packetized-lean') {
    return `Reviewed top ${decision.packets?.length || 0} packet(s) by deterministic risk score; remaining changed hunks/files require Codex or human proof review.`;
  }
  if (decision.mode === 'guarded-oversized-lean') {
    return 'Diff exceeded packet budget; use top changed files and deterministic signals as required Codex/human review checklist.';
  }
  if (decision.mode === 'guarded-unpacketized-lean') {
    return 'Router could not produce safe diff packets; use top changed files as required Codex/human review checklist.';
  }
  return null;
}

function shouldReportPacketReview(decision) {
  return ['packetized-lean', 'guarded-oversized-lean', 'guarded-unpacketized-lean'].includes(decision.mode);
}

function uniqueCount(values) {
  return new Set(values.filter(Boolean)).size;
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
  buildReviewPackets,
  parseUnifiedDiff,
  scorePathRisk,
};
