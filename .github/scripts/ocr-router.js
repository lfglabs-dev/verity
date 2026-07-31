'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const ROUTER_VERSION = 'router-v10';
const DEFAULT_SCOUT_MODEL = 'MiniMax-M3';
const RUBRIC_PATH = path.join(__dirname, '..', 'ocr', 'rubric.json');

// Multi-lens scout configuration. A single scout pass converges serially: on a
// real PR each pass surfaced exactly one new defect class, so review needed
// three cycles (checksum-manifest scoping -> verification-replay independence ->
// shallow-clone verification contract). Instead we run one scout call PER LENS
// in parallel and union their findings, so a single review surfaces every
// defect class at once. Each lens reframes the same bounded dossier toward a
// distinct failure family. Extend by appending to this list (and, if the lens
// maps to a recurring defect, adding a matching rubric item — see rubric.json).
const LENSES = Object.freeze([
  Object.freeze({
    id: 'provenance',
    title: 'Data & artifact provenance',
    focus: 'Scrutinize data/artifact provenance and manifest scoping: does a checksum or manifest cover ALL relevant artifacts or only a subset; are inputs traceable to a trusted source; can a producer silently add or swap an artifact the manifest does not pin?',
  }),
  Object.freeze({
    id: 'verification-independence',
    title: 'Verification independence',
    focus: 'Scrutinize whether a claimed-independent check is actually independent: does the verifier reuse producer code, trust a producer-emitted output, run against a shallow/partial clone that drops required history, or otherwise replay non-independently rather than re-deriving the result?',
  }),
  Object.freeze({
    id: 'environment-determinism',
    title: 'Environment determinism',
    focus: 'Scrutinize environment, override, and toolchain assumptions: NVCC / RUN_CPU / feature flags, environment-variable overrides, unpinned toolchains, and nondeterministic build or runtime configuration that can change what is actually proven or verified between environments.',
  }),
  Object.freeze({
    id: 'proof-soundness',
    title: 'Lean proof soundness',
    focus: 'Scrutinize Lean proof soundness: vacuous or over-strong hypotheses, introduced sorry/admit/axiom, unsound tactic shortcuts, weakened theorem conclusions, and broad automation replacing structured proof.',
  }),
]);
const STRONG_REVIEW_BLOCKER_MESSAGE = 'OpenCodeReview 1.7.9 supports --from/--to full diff ranges, but this workflow does not have a safe packet/window input bridge for Lean hunks yet.';
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
  scoutDossierMaxChars: 18000,
  // Thinking models (GLM-5.2, MiniMax-M3) reason at length before emitting
  // the JSON verdict; 45s aborted every scout call and forced
  // fallback_deterministic on all large-Lean reviews. The scout runs once
  // per review inside a 45-minute job budget — give it real headroom.
  scoutTimeoutMs: 240000,
});

async function main() {
  const baseRef = requiredEnv('BASE_REF');
  const headSha = requiredEnv('HEAD_SHA');
  const prNumber = process.env.OCR_PR_NUMBER || '';
  const metricsPath = process.env.OCR_METRICS_PATH || path.join(process.env.RUNNER_TEMP || '.', 'ocr-metrics.json');
  const resultPath = process.env.OCR_RESULT_PATH || path.join(process.env.RUNNER_TEMP || '.', 'ocr-result.json');
  const outputPath = process.env.GITHUB_OUTPUT || '';

  const startedAt = new Date().toISOString();
  const diff = loadDiff(`origin/${baseRef}`, headSha);
  const decision = decideRoute(diff.files);
  if (decision.mode === 'large-lean-hotspots') {
    await applyScoutStage(decision, diff, resolveScoutConfig(process.env));
  }
  const packetPlanPath = writePacketReviewPlan(decision, diff);
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
    has_lean: String(decision.counts.lean > 0),
    reason: decision.reason,
    concurrency: String(decision.ocr.concurrency),
    timeout: String(decision.ocr.timeout),
    background_chars: String(decision.ocr.backgroundChars),
    metrics_path: metricsPath,
    result_path: resultPath,
    diff_base: diff.base,
    router_version: ROUTER_VERSION,
    packet_review_planned: String(Boolean(packetPlanPath)),
    packet_plan_path: packetPlanPath || '',
  });

  console.log(`OCR route: ${decision.mode} (${decision.reason})`);
  console.log(`Changed files: ${diff.files.length}; supported: ${decision.counts.supported}; Lean: ${decision.counts.lean}; changed lines: ${decision.changedLines}`);
  if (decision.scout) {
    console.log(`Scout enabled: ${decision.scout.enabled}; model: ${decision.scout.model || DEFAULT_SCOUT_MODEL}; status: ${decision.scout.status}`);
  }
}

function loadDiff(base, head) {
  const mergeBase = git(['merge-base', base, head]).trim();
  const output = git(['diff', '--numstat', '--find-renames', mergeBase, head, '--']);
  const files = output.split(/\r?\n/).filter(Boolean).map(parseNumstatLine).filter(Boolean);
  const hunksByPath = loadDiffHunks(mergeBase, head);
  for (const file of files) {
    file.hunks = hunksByPath.get(file.path) || [];
    file.risk = scoreFileRisk(file);
  }
  return { base: mergeBase, head, files };
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
      mode: 'no-supported',
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
      mode: 'large-lean-hotspots',
      shouldRunOcr: false,
      reason: `Lean packet budget exceeded: ${leanFiles.length} Lean file(s), ${changedLines} changed supported line(s).`,
      counts,
      changedLines,
      largestFiles,
      packets: [],
      ocr: { concurrency: 0, timeout: 0, backgroundChars: 0 },
    });
  }

  if (leanFiles.length > 0 && (leanFiles.length >= THRESHOLDS.largeLeanFiles || changedLines > THRESHOLDS.largeChangedLines)) {
    if (packets.length === 0) {
      return route({
        mode: 'large-lean-hotspots',
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
      mode: 'large-lean-hotspots',
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
      mode: 'medium-lean',
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
    mode: leanFiles.length > 0 ? 'small-lean' : 'config-docs',
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
        diff_excerpt: renderHunkExcerpt(hunk, 24),
        changed_lines: changedLines.length,
      });
    }
  }

  return packets
    .sort((a, b) => b.score - a.score || b.changed_lines - a.changed_lines || a.path.localeCompare(b.path))
    .slice(0, THRESHOLDS.packetMaxCount)
    .map((packet, index) => ({ ...packet, packet_id: `pkt-${index + 1}` }));
}

// P1 (packet semantic review): materialize the scout-selected packets as an
// executable plan. `ocr review` has no --include flag, so each group is scoped
// by EXCLUDING the exact complement — every other changed supported file. The
// exclusion list is bounded by the diff itself, never a glob over the repo.
function writePacketReviewPlan(decision, diff) {
  if (decision.mode !== 'large-lean-hotspots') return '';
  const packets = decision.packets || [];
  if (packets.length === 0) return '';
  const runnerTemp = process.env.RUNNER_TEMP || '.';
  const byFile = new Map();
  for (const packet of packets) {
    if (!byFile.has(packet.path)) byFile.set(packet.path, []);
    byFile.get(packet.path).push(packet.packet_id);
  }
  const allSupported = diff.files.filter(f => f.supported && !isExcluded(f.path)).map(f => f.path);
  const groups = [...byFile.entries()]
    .map(([file, packetIds]) => ({
      files: [file],
      packet_ids: packetIds,
      exclude: allSupported.filter(other => other !== file),
    }))
    .slice(0, PACKET_REVIEW_MAX_GROUPS);
  const plan = {
    schema_version: 1,
    diff_base: diff.base,
    head: diff.head,
    total_groups_available: byFile.size,
    groups,
  };
  const planPath = path.join(runnerTemp, 'ocr-packet-plan.json');
  fs.writeFileSync(planPath, `${JSON.stringify(plan, null, 2)}\n`);
  return planPath;
}

const PACKET_REVIEW_MAX_GROUPS = 4;

// P5 (grounded scout dossiers): a bounded, node-side outline of each packet's
// file — declarations plus soundness-relevant markers. Full LSP diagnostics
// remain the packet reviewer's job (its MCP session has lean_diagnostic_messages);
// the scout only needs enough structure to ask anchored questions.
const OUTLINE_DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque)\b[^:=]{0,120}/;
const OUTLINE_MARKER_RE = /\b(sorry|admit|native_decide|axiom)\b/;
const outlineCache = new Map();
function leanOutlineForFile(filePath) {
  if (!/\.lean$/.test(filePath)) return undefined;
  if (outlineCache.has(filePath)) return outlineCache.get(filePath);
  let outline;
  try {
    const text = fs.readFileSync(filePath, 'utf8');
    const decls = [];
    const markers = [];
    const lines = text.split(/\r?\n/);
    for (let i = 0; i < lines.length; i += 1) {
      const line = lines[i];
      const decl = OUTLINE_DECL_RE.exec(line);
      if (decl && decls.length < 40) decls.push(`L${i + 1}: ${line.trim().slice(0, 140)}`);
      if (OUTLINE_MARKER_RE.test(line) && !/^\s*--/.test(line) && markers.length < 20) {
        markers.push(`L${i + 1}: ${line.trim().slice(0, 120)}`);
      }
    }
    outline = {
      declarations: decls,
      soundness_markers: markers.length ? markers : undefined,
    };
    const raw = JSON.stringify(outline);
    if (raw.length > 2000) outline = { declarations: decls.slice(0, 20), soundness_markers: markers.slice(0, 10), truncated: true };
  } catch (err) {
    outline = undefined;
  }
  outlineCache.set(filePath, outline);
  return outline;
}

function renderHunkExcerpt(hunk, maxLines) {
  return hunk.lines.slice(0, maxLines).map(line => {
    const prefix = line.type === 'add' ? '+' : line.type === 'del' ? '-' : ' ';
    const number = line.type === 'del' ? line.oldLine : line.newLine;
    return `${prefix}${number || '?'} ${line.text}`.slice(0, 260);
  }).join('\n');
}

async function applyScoutStage(decision, diff, config) {
  const deterministicPackets = decision.packets || [];
  const scoutSwitchOn = config.enabled !== false;
  const enabled = Boolean(scoutSwitchOn && config.url && config.key && config.model);
  const lenses = resolveLenses(config);
  const rubric = loadRubric();
  decision.scout = {
    enabled,
    configured: Boolean(config.url && config.key && config.model),
    attempted: false,
    status: scoutSwitchOn ? 'not_configured' : 'disabled',
    model: config.model ? redactModel(config.model) : DEFAULT_SCOUT_MODEL,
    lenses: lenses.map(lens => lens.id),
    lens_count: lenses.length,
    rubric_items: rubric.length,
    selected_packets: deterministicPackets.map(p => p.packet_id),
    residual_coverage: packetResidualRisk(decision),
    strong_review_status: 'blocked_packet_input',
    strong_review_blocker: STRONG_REVIEW_BLOCKER_MESSAGE,
  };

  if (deterministicPackets.length === 0) {
    decision.scout.status = decision.scout.enabled ? 'skipped_no_packets' : decision.scout.status;
    decision.scout.residual_coverage = 'No safe packets were produced; use top changed files and deterministic checklist items for Codex/human review.';
    return decision;
  }

  if (!decision.scout.enabled) return decision;

  decision.scout.attempted = true;
  decision.scout.status = 'pending';

  // Fan out one scout call per lens IN PARALLEL. Each call reuses the same
  // per-call scoutTimeoutMs, so wall-clock time stays bounded to a single
  // scout timeout rather than N of them. Promise.all never rejects here because
  // runScoutLens catches per-lens failures into a result object, so one broken
  // lens cannot lose the findings of the others.
  const results = await Promise.all(
    lenses.map(lens => runScoutLens(config, decision, diff, lens, rubric)),
  );
  const successful = results.filter(r => r.ok);
  const failed = results.filter(r => !r.ok);

  decision.scout.lens_results = results.map(r => ({
    lens: r.lens.id,
    status: r.ok ? 'success' : 'error',
    raw_selected: r.ok ? r.rawCount : null,
    error_type: r.ok ? null : classifyScoutError(r.error),
  }));
  decision.scout.raw_selected_count = successful.reduce((sum, r) => sum + (r.rawCount || 0), 0);

  if (successful.length === 0) {
    // Every lens failed: identical outcome to the old single-call failure, so
    // preserve the same failure surface (error/error_type/http_status/detail).
    const err = failed[0]?.error;
    decision.scout.status = 'fallback_deterministic';
    decision.scout.error = 'Scout model call failed; deterministic packet ranking retained.';
    decision.scout.error_type = classifyScoutError(err);
    decision.scout.error_detail = sanitizeScoutErrorDetail(err);
    if (err?.status) decision.scout.http_status = err.status;
    return decision;
  }

  const selected = unionScoutPackets(deterministicPackets, successful);
  if (selected.length > 0) {
    decision.packets = selected;
    const lensList = successful.map(r => r.lens.id).join(', ');
    decision.reason = `${decision.reason} Multi-lens scout (${successful.length}/${lenses.length} lens(es): ${lensList}) surfaced ${selected.length}/${deterministicPackets.length} packet(s) for stronger review.`;
    decision.scout.selected_packets = selected.map(p => p.packet_id);
    decision.scout.status = 'success';
    decision.scout.summary = mergeLensSummaries(successful);
    decision.scout.residual_coverage = mergeLensResidual(successful) || decision.scout.residual_coverage;
    if (failed.length) {
      decision.scout.partial_lens_failures = failed.length;
    }
  } else {
    decision.scout.status = 'fallback_no_selection';
    decision.scout.summary = mergeLensSummaries(successful) || 'Scout returned no valid packet IDs; deterministic ranking retained.';
    decision.scout.residual_coverage = 'Scout returned no valid packet IDs, so deterministic packet ranking was retained and all selected packets still need strong reviewer analysis.';
  }
  return decision;
}

// Run one lens's scout call. Builds a lens-framed, rubric-injected dossier and
// resolves to a tagged result instead of throwing, so the caller can union
// across lenses even when some fail.
async function runScoutLens(config, decision, diff, lens, rubric) {
  try {
    const dossier = buildRiskDossier(decision, diff, { lens, rubric });
    const scout = await callScoutModel(config, dossier, lens);
    const rawCount = Array.isArray(scout.selected_packets) ? scout.selected_packets.length : 0;
    return { lens, ok: true, scout, rawCount };
  } catch (err) {
    return { lens, ok: false, error: err };
  }
}

// Union + de-duplicate packet selections across lenses. A packet flagged by
// several lenses appears ONCE, carrying every lens's finding in scout_lenses.
// Deterministic packet order is preserved. The legacy single-value scout fields
// (scout_reason/scout_risk_category/scout_question) are kept, populated from the
// first lens that flagged the packet, so the existing finding shape/contract is
// unchanged for any consumer that does not read scout_lenses.
function unionScoutPackets(deterministicPackets, lensResults) {
  const byId = new Map(deterministicPackets.map(p => [p.packet_id, p]));
  const order = deterministicPackets.map(p => p.packet_id);
  const merged = new Map();
  for (const result of lensResults) {
    const items = Array.isArray(result.scout?.selected_packets) ? result.scout.selected_packets : [];
    for (const item of items) {
      const id = String(item.id || item.packet_id || '').trim();
      const packet = byId.get(id);
      if (!packet) continue;
      if (!merged.has(id)) merged.set(id, { packet, findings: [] });
      const entry = merged.get(id);
      if (entry.findings.some(f => f.lens === result.lens.id)) continue;
      entry.findings.push({
        lens: result.lens.id,
        lens_title: result.lens.title,
        reason: String(item.reason || '').slice(0, 500),
        risk_category: String(item.risk_category || '').slice(0, 120),
        question: String(item.question_for_stronger_reviewer || '').slice(0, 500),
      });
    }
  }
  const selected = [];
  for (const id of order) {
    if (!merged.has(id)) continue;
    const { packet, findings } = merged.get(id);
    const primary = findings[0];
    selected.push({
      ...packet,
      scout_reason: primary.reason,
      scout_risk_category: primary.risk_category,
      scout_question: primary.question,
      scout_lenses: findings,
      scout_lens_ids: findings.map(f => f.lens),
    });
  }
  return selected.slice(0, THRESHOLDS.packetMaxCount);
}

function mergeLensSummaries(lensResults) {
  const seen = new Set();
  const parts = [];
  for (const result of lensResults) {
    const summary = String(result.scout?.summary || '').trim();
    if (!summary || seen.has(summary)) continue;
    seen.add(summary);
    parts.push(`${result.lens.id}: ${summary}`);
  }
  return parts.join(' ').slice(0, 800);
}

function mergeLensResidual(lensResults) {
  const seen = new Set();
  const parts = [];
  for (const result of lensResults) {
    const residual = String(result.scout?.residual_coverage || '').trim();
    if (!residual || seen.has(residual)) continue;
    seen.add(residual);
    parts.push(residual);
  }
  return parts.join(' ').slice(0, 800) || null;
}

function buildRiskDossier(decision, diff, options = {}) {
  const lens = options.lens || null;
  const rubric = Array.isArray(options.rubric) ? options.rubric : [];
  const packets = (decision.packets || []).map(packet => ({
    id: packet.packet_id,
    file: packet.path,
    line_window: { start: packet.start_line, end: packet.end_line },
    score: packet.score,
    risk_category: packet.signals,
    summary: packet.summary,
    changed_lines: packet.changed_lines,
    diff_excerpt: packet.diff_excerpt,
    file_outline: leanOutlineForFile(packet.path),
  }));

  const supported = diff.files.filter(f => f.supported);
  const dossier = {
    schema_version: 1,
    task: lens
      ? `Rank dangerous Lean/code review packets for a stronger reviewer THROUGH THE "${lens.title}" LENS. ${lens.focus} Only flag packets relevant to this lens. Do not approve the PR.`
      : 'Rank dangerous Lean review packets for a stronger reviewer. Do not approve the PR.',
    lens: lens ? { id: lens.id, title: lens.title, focus: lens.focus } : undefined,
    mode: decision.mode,
    thresholds: decision.thresholds,
    counts: decision.counts,
    total_supported_changed_lines: decision.changedLines,
    top_changed_files: decision.largestFiles.map(f => ({
      file: f.path,
      added: f.added,
      deleted: f.deleted,
      category: f.category,
      risk: f.risk,
    })),
    deterministic_signals: summarizeSignals(decision.packets || []),
    supported_files: supported.map(f => ({
      file: f.path,
      added: f.added,
      deleted: f.deleted,
      category: f.category,
      hunk_count: Array.isArray(f.hunks) ? f.hunks.length : 0,
    })).slice(0, 30),
    candidate_packets: packets,
    // Accumulating rubric: permanent checklist of defect classes confirmed on
    // past Verity PRs. Every review re-checks these so a defect class is caught
    // once and never has to be rediscovered serially.
    rubric: rubric.length ? rubric.map(item => ({
      id: item.id,
      lens: item.lens,
      title: item.title,
      check: item.check,
    })) : undefined,
    lens_rubric_focus: lens && rubric.length
      ? rubric.filter(item => item.lens === lens.id).map(item => item.id)
      : undefined,
    required_json_schema: {
      selected_packets: [{
        id: 'pkt-1',
        reason: 'Why this packet is dangerous.',
        risk_category: 'sorry/admit | theorem weakening | trust boundary | import/axiom | proof deletion | semantic hotspot',
        file: 'path',
        line_window: { start: 1, end: 2 },
        question_for_stronger_reviewer: 'Specific question OCR/reviewer should answer.',
      }],
      residual_coverage: 'What changed areas remain unreviewed after packet selection.',
      summary: 'One sentence triage summary.',
    },
  };
  return truncateJson(dossier, THRESHOLDS.scoutDossierMaxChars);
}

function summarizeSignals(packets) {
  const counts = new Map();
  for (const packet of packets) {
    for (const signal of packet.signals || []) counts.set(signal, (counts.get(signal) || 0) + 1);
  }
  return [...counts.entries()].map(([signal, count]) => ({ signal, count }))
    .sort((a, b) => b.count - a.count || a.signal.localeCompare(b.signal));
}

async function callScoutModel(config, dossier, lens = null) {
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), THRESHOLDS.scoutTimeoutMs);
  const systemContent = lens
    ? `You are a cautious Lean/code review triage scout applying the "${lens.title}" lens. ${lens.focus} Only select packets relevant to this lens. Return only JSON matching the requested schema. Never claim final review coverage or approval.`
    : 'You are a cautious Lean proof-change triage scout. Return only JSON matching the requested schema. Never claim final review coverage or approval.';
  try {
    const response = await fetch(openAiChatUrl(config.url), {
      method: 'POST',
      signal: controller.signal,
      headers: {
        'content-type': 'application/json',
        authorization: `Bearer ${config.key}`,
      },
      body: JSON.stringify({
        model: config.model,
        temperature: 0,
        response_format: { type: 'json_object' },
        messages: [
          {
            role: 'system',
            content: systemContent,
          },
          {
            role: 'user',
            content: JSON.stringify(dossier),
          },
        ],
      }),
    });
    const text = await response.text();
    if (!response.ok) {
      const err = new Error(text || response.statusText || 'scout model rejected request');
      err.status = response.status;
      throw err;
    }
    const payload = JSON.parse(text);
    const content = payload.choices?.[0]?.message?.content;
    if (!content) throw new Error('scout model returned no message content');
    return parseScoutJson(content);
  } finally {
    clearTimeout(timeout);
  }
}

function resolveScoutConfig(env = process.env) {
  const enabled = !isFalse(env.OCR_SCOUT_ENABLED);
  return {
    enabled,
    url: env.OCR_SCOUT_LLM_URL || env.OCR_LLM_URL || '',
    key: env.OCR_SCOUT_LLM_KEY || env.OCR_LLM_KEY || env.OCR_LLM_TOKEN || '',
    model: env.OCR_SCOUT_LLM_MODEL || DEFAULT_SCOUT_MODEL,
  };
}

function isFalse(value) {
  return /^(0|false|no|off)$/i.test(String(value || '').trim());
}

// Which lenses fan out for this review. Defaults to the full LENSES set; an
// operator can pin a subset via config.lenses or OCR_SCOUT_LENSES (a
// comma-separated list of lens ids) without a code change. Unknown ids are
// ignored, and an empty/all-unknown selection falls back to the full set so a
// mis-set env var never silently disables scouting.
function resolveLenses(config = {}, env = process.env) {
  const requested = String(config.lenses || env.OCR_SCOUT_LENSES || '').trim();
  if (!requested) return LENSES;
  const ids = new Set(requested.split(',').map(s => s.trim().toLowerCase()).filter(Boolean));
  const selected = LENSES.filter(lens => ids.has(lens.id));
  return selected.length ? selected : LENSES;
}

// Load the accumulating review rubric. Every scout dossier embeds this so past
// defect classes are re-checked on every future PR. Missing/invalid file is a
// soft failure (empty rubric) — the scout still runs on its lenses.
function loadRubric(rubricPath = RUBRIC_PATH) {
  try {
    const parsed = JSON.parse(fs.readFileSync(rubricPath, 'utf8'));
    return Array.isArray(parsed.items) ? parsed.items : [];
  } catch {
    return [];
  }
}

// Mechanism for growing the rubric: when a review confirms a NEW defect class,
// call appendRubricItem({ id, lens, title, check, origin }) to persist it as a
// permanent checklist item so every later review explicitly checks for it.
// De-dupes by id (returns false if the id already exists). This is the wiring
// point for future automation (e.g. a bot that appends when a reviewer labels a
// finding as a new class); today it is invoked deliberately by an operator.
function appendRubricItem(item, rubricPath = RUBRIC_PATH) {
  const id = String(item && item.id || '').trim();
  if (!id) throw new Error('appendRubricItem requires an item.id');
  let doc;
  try {
    doc = JSON.parse(fs.readFileSync(rubricPath, 'utf8'));
  } catch {
    doc = { schema_version: 1, items: [] };
  }
  if (!Array.isArray(doc.items)) doc.items = [];
  if (doc.items.some(existing => String(existing.id).trim() === id)) return false;
  doc.items.push({
    id,
    lens: String(item.lens || '').trim(),
    title: String(item.title || '').trim(),
    check: String(item.check || '').trim(),
    origin: String(item.origin || '').trim(),
    added_at: String(item.added_at || new Date().toISOString().slice(0, 10)),
  });
  fs.writeFileSync(rubricPath, `${JSON.stringify(doc, null, 2)}\n`);
  return true;
}

function parseScoutJson(content) {
  const text = stripThinking(String(content || '')).trim();
  try {
    return JSON.parse(text);
  } catch (err) {
    const extracted = extractJsonObject(text);
    if (!extracted) throw err;
    return JSON.parse(extracted);
  }
}

function stripThinking(text) {
  return text
    .replace(/<mm:think>[\s\S]*?<\/mm:think>/gi, '')
    .replace(/<think>[\s\S]*?<\/think>/gi, '')
    .trim()
    .replace(/^```(?:json)?\s*/i, '')
    .replace(/\s*```$/i, '');
}

function extractJsonObject(text) {
  return extractJsonValue(text, '{', '}');
}

function extractJsonValue(text, open, close) {
  const start = text.indexOf(open);
  if (start === -1) return null;
  let depth = 0;
  let inString = false;
  let escaped = false;
  for (let i = start; i < text.length; i += 1) {
    const ch = text[i];
    if (inString) {
      if (escaped) {
        escaped = false;
      } else if (ch === '\\') {
        escaped = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }
    if (ch === '"') {
      inString = true;
    } else if (ch === open) {
      depth += 1;
    } else if (ch === close) {
      depth -= 1;
      if (depth === 0) return text.slice(start, i + 1);
    }
  }
  return null;
}

function classifyScoutError(err) {
  const text = String(err?.message || err || '').toLowerCase();
  if (err?.status) return 'http_error';
  if (text.includes('abort')) return 'timeout';
  if (text.includes('http')) return 'http_error';
  if (text.includes('json')) return 'invalid_json';
  return 'request_failed';
}

function sanitizeScoutErrorDetail(err) {
  const raw = String(err?.message || err || '');
  const structured = redactStructuredError(raw.slice(0, 64000));
  return redactSecretText(structured || raw.slice(0, 2000))
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 500);
}

function redactStructuredError(text) {
  const trimmed = String(text || '').trim();
  if (!trimmed) return null;
  let replaced = trimmed;
  let changed = false;
  for (const candidate of extractJsonCandidates(trimmed)) {
    try {
      const redacted = JSON.stringify(redactSecretJsonValue(JSON.parse(candidate)));
      replaced = replaceLiteralAll(replaced, candidate, redacted);
      changed = true;
    } catch {
      // Keep scanning; provider diagnostics may mix invalid and valid fragments.
    }
  }
  if (changed) return replaced;
  const candidate = /^[\[{]/.test(trimmed)
    ? trimmed
    : extractJsonObject(trimmed) || extractJsonValue(trimmed, '[', ']');
  if (!candidate) return null;
  try {
    const redacted = JSON.stringify(redactSecretJsonValue(JSON.parse(candidate)));
    return candidate === trimmed ? redacted : replaceLiteralAll(trimmed, candidate, redacted);
  } catch {
    const embedded = extractJsonObject(trimmed) || extractJsonValue(trimmed, '[', ']');
    if (embedded && embedded !== candidate) {
      try {
        const redacted = JSON.stringify(redactSecretJsonValue(JSON.parse(embedded)));
        return replaceLiteralAll(trimmed, embedded, redacted);
      } catch {
        return null;
      }
    }
    return null;
  }
}

function extractJsonCandidates(text) {
  const candidates = [];
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i];
    if (ch !== '{' && ch !== '[') continue;
    const close = ch === '{' ? '}' : ']';
    if (text.indexOf(close, i + 1) === -1) continue;
    const candidate = extractJsonValue(text.slice(i, i + 8192), ch, close);
    if (!candidate) continue;
    candidates.push(candidate);
    i += candidate.length - 1;
    if (candidates.length >= 20) break;
  }
  return candidates;
}

function redactSecretJsonValue(value, key = '') {
  if (isSecretKey(key)) return '[redacted]';
  if (Array.isArray(value)) {
    let redactNext = false;
    let secretContext = false;
    return value.map((item, index) => {
      if (redactNext) {
        redactNext = false;
        return '[redacted]';
      }
      if (secretContext && isValueCarrier(item)) {
        redactNext = true;
        return redactSecretJsonValue(item);
      }
      if (typeof item === 'string' && hasSecretIndicator(item)) {
        if (isValueCarrier(value[index + 1])) {
          secretContext = true;
        } else {
          redactNext = true;
        }
        return redactSecretJsonValue(item);
      }
      return redactSecretJsonValue(item);
    });
  }
  if (value && typeof value === 'object') {
    const secretContext = Object.entries(value).some(([childKey, childValue]) => {
      if (!/^(field|field_name|fieldName|param|parameter|name|key|loc|location|path|property|property_name|propertyName|attribute|target)$/i.test(childKey)) return false;
      return hasSecretIndicator(childValue);
    });
    return Object.fromEntries(Object.entries(value).map(([childKey, childValue]) => [
      childKey,
      secretContext && /^(value|input|input_value|inputValue|provided|actual|message|detail|details|text|description|error_description|errorDescription)$/i.test(childKey)
        ? '[redacted]'
        : redactSecretJsonValue(childValue, childKey),
    ]));
  }
  if (typeof value === 'string') {
    const structured = redactStructuredError(value);
    return redactSecretText(structured || value);
  }
  return value;
}

function hasSecretIndicator(value) {
  if (Array.isArray(value)) return value.some(hasSecretIndicator);
  if (value && typeof value === 'object') return Object.values(value).some(hasSecretIndicator);
  return isSecretKey(String(value || ''));
}

function isValueCarrier(value) {
  return /^(value|input|input_value|inputValue|provided|actual)$/i.test(String(value || ''));
}

function isSecretKey(key) {
  const normalized = String(key || '')
    .replace(/([a-z0-9])([A-Z])/g, '$1_$2')
    .replace(/[^a-zA-Z0-9]+/g, '_')
    .toLowerCase();
  const parts = normalized.split('_').filter(Boolean);
  return normalized === 'key'
    || normalized === 'token'
    || (parts.some(part => /^(ocr|llm|scout)$/.test(part)) && parts.some(part => /^(key|token)$/.test(part)))
    || /(^|_)(api_key|apikey|api_token|access_token|refresh_token|id_token|client_secret|client_id|api_secret|consumer_secret|private_key|bearer_token|session_secret|session_token|auth_code|authcode|authorization|password|passphrase|credential|credentials|secret)($|_)/.test(normalized);
}

function redactSecretText(text) {
  return String(text || '')
    .replace(/https?:\/\/[^\s"')]+/g, '[url-redacted]')
    .replace(/\beyJ[A-Za-z0-9_-]+\.eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\b/g, '[redacted]')
    .replace(/Bearer\s+[^\s"',)}\]]+/gi, 'Bearer [redacted]')
    .replace(/Basic\s+[A-Za-z0-9+/=._~-]+/gi, 'Basic [redacted]')
    .replace(/\bsk-[A-Za-z0-9._-]+/gi, '[redacted]')
    .replace(/(["'`])([A-Za-z0-9_-]*(?:ocr|llm|scout)[A-Za-z0-9_-]*(?:key|token)|[A-Za-z0-9_-]*(?:key|token)[A-Za-z0-9_-]*(?:ocr|llm|scout))\1(\s*:\s*)(["'`])(?:\\.|(?!\4).){0,300}\4/gi, '$1$2$1$3$4[redacted]$4')
    .replace(/\b([A-Za-z0-9_-]*(?:ocr|llm|scout)[A-Za-z0-9_-]*(?:key|token)|[A-Za-z0-9_-]*(?:key|token)[A-Za-z0-9_-]*(?:ocr|llm|scout))\b([^"'`\n]{0,120}?[:=]\s*)(["'`])(?:\\.|(?!\3).){0,300}\3/gi, '$1$2$3[redacted]$3')
    .replace(/\b([A-Za-z0-9_-]*(?:ocr|llm|scout)[A-Za-z0-9_-]*(?:key|token)|[A-Za-z0-9_-]*(?:key|token)[A-Za-z0-9_-]*(?:ocr|llm|scout))\b([^"'`\n]{0,120}?[:=]\s*)([^\s"',)}\]]{6,})/gi, '$1$2[redacted]')
    .replace(/(["'`])((?:[A-Za-z0-9_-]*(?:api\s*key|api[_-]?key|apikey|access[_-]?token|refresh[_-]?token|id[_-]?token|client[_-]?(?:secret|id)|api[_-]?secret|consumer[_-]?secret|private[_-]?key|bearer[_-]?token|session[_-]?(?:secret|token)|auth[_-]?code|credential|credentials|passphrase|password|secret))|token|authorization)\1(\s*:\s*)(["'`])(?:\\.|(?!\4).){0,300}\4/gi, '$1$2$1$3$4[redacted]$4')
    .replace(/\b((?:[A-Za-z0-9_-]*(?:api\s*key|api[_-]?key|apikey|access[_-]?token|refresh[_-]?token|id[_-]?token|client[_-]?(?:secret|id)|api[_-]?secret|consumer[_-]?secret|private[_-]?key|bearer[_-]?token|session[_-]?(?:secret|token)|auth[_-]?code|credential|credentials|passphrase|password|secret))|token|authorization)\b([^"'`\n]{0,120}?[:=]\s*)(["'`])(?:\\.|(?!\3).){0,300}\3/gi, '$1$2$3[redacted]$3')
    .replace(/\b((?:(?:[A-Za-z0-9_-]*(?:api\s*key|api[_-]?key|apikey|access[_-]?token|refresh[_-]?token|id[_-]?token|client[_-]?(?:secret|id)|api[_-]?secret|consumer[_-]?secret|private[_-]?key|bearer[_-]?token|session[_-]?(?:secret|token)|auth[_-]?code|credential|credentials|passphrase|password|secret))|token|authorization)\b[^"'`\n]{0,120}?[:=]\s*)([^\s"',)}\]]{6,})/gi, '$1[redacted]')
    .replace(/\b(?![a-f0-9]{40}\b)(?![0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b)(?!req_[A-Za-z0-9._-]{20,}\b)(?!trace[_-][A-Za-z0-9._-]{20,}\b)(?!correlation[_-][A-Za-z0-9._-]{20,}\b)(?=[A-Za-z0-9._~+/-]{32,}\b)(?=[A-Za-z0-9._~+/-]*[A-Za-z])(?=[A-Za-z0-9._~+/-]*\d)[A-Za-z0-9._~+/-]{32,}={0,2}\b/g, '[redacted]');
}

function replaceLiteralAll(text, needle, replacement) {
  return String(text).split(needle).join(replacement);
}

function openAiChatUrl(baseUrl) {
  const trimmed = String(baseUrl || '').replace(/\/+$/, '');
  if (trimmed.endsWith('/chat/completions')) return trimmed;
  if (trimmed.endsWith('/v1')) return `${trimmed}/chat/completions`;
  return `${trimmed}/v1/chat/completions`;
}

function truncateJson(value, maxChars) {
  const json = JSON.stringify(value);
  if (json.length <= maxChars) return value;
  const clone = JSON.parse(json);
  clone.candidate_packets = (clone.candidate_packets || []).map(packet => ({
    ...packet,
    diff_excerpt: String(packet.diff_excerpt || '').slice(0, 900),
  }));
  while (JSON.stringify(clone).length > maxChars && clone.candidate_packets.length > 1) {
    clone.candidate_packets.pop();
  }
  return clone;
}

function redactModel(model) {
  return String(model).slice(0, 80);
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
  const addedRiskCode = codeLinesForHunkSide(hunk, 'new');
  const deletedRiskCode = codeLinesForHunkSide(hunk, 'old');
  const addedStatementText = statementLinesForHunkSide(hunk, 'new');
  const deletedStatementText = statementLinesForHunkSide(hunk, 'old');
  const allChangedRiskCode = [...addedRiskCode, ...deletedRiskCode];
  const allChangedStatementText = [...addedStatementText, ...deletedStatementText];

  if (addedRiskCode.some(line => /\b(sorry|admit)\b/.test(line))) add('introduced sorry/admit', 80);
  if (addedRiskCode.some(line => /^\s*axiom\b/.test(line) || /\baxiom\b/.test(line))) add('introduced/changed axiom', 75);
  if (addedRiskCode.some(line => /\bunsafe\b/.test(line))) add('introduced unsafe', 55);
  if (allChangedRiskCode.some(line => /^\s*import\s+/.test(line))) add('changed imports', 30);
  if (allChangedStatementText.some(line => publicDeclPattern().test(line))) add('public declaration/signature changed', 34);
  if (file.category === 'trust-doc') add('trust-boundary docs drift', 38);
  if (file.category === 'doc' && /(trust|axiom|audit|sound|semantic|proof)/i.test(file.path)) add('trust/proof docs drift', 25);
  if (deletedRiskCode.length >= 80 || deletedRiskCode.join('\n').length > 6000) add('large deleted proof obligation', 35);
  if (deletedStatementText.some(line => publicDeclPattern().test(line)) && addedStatementText.some(line => publicDeclPattern().test(line))) {
    add('theorem/public statement changed', 45);
  }
  if (changedTheoremStatements(deletedStatementText, addedStatementText).length > 0) add('theorem statement changed/possibly weakened', 65);

  return [...signals.values()].sort((a, b) => b.weight - a.weight || a.name.localeCompare(b.name));
}

function codeLinesForHunkSide(hunk, side, options = {}) {
  const includeType = side === 'old' ? 'del' : 'add';
  const skipType = side === 'old' ? 'add' : 'del';
  const scanner = createLeanChangedCodeScanner(options);
  for (const line of hunk.lines || []) {
    if (line.type === skipType) continue;
    scanner.scanLine(line.text, line.type === includeType);
  }
  return scanner.finish();
}

function statementLinesForHunkSide(hunk, side) {
  return codeLinesForHunkSide(hunk, side, { preserveStrings: true });
}

function createLeanChangedCodeScanner(options = {}) {
  const code = [];
  const interpolationFrames = [];
  let current = '';
  let commentDepth = 0;
  let lineComment = false;
  let escapedIdent = false;
  let charLiteral = false;
  let charEscaped = false;
  let string = null;
  let prefix = '';

  const remember = ch => {
    prefix = ch === '\n' ? '' : `${prefix}${ch}`.slice(-32);
  };
  const emit = (ch, include) => {
    if (include) current += ch;
  };
  const flush = () => {
    if (current.trim()) code.push(current);
    current = '';
  };
  const inInterpolationCode = () => interpolationFrames.length > 0 && !string;
  const rememberText = text => {
    for (const ch of String(text || '')) remember(ch);
  };
  const emitText = (text, include) => {
    if (include) current += text;
  };
  const openString = (interpolated, rawTerminator = null) => {
    string = { interpolated, escaped: false, rawTerminator };
  };
  const openInterpolation = () => {
    interpolationFrames.push({ braceDepth: 1, returnString: string ? { ...string, escaped: false } : null });
    string = null;
  };
  const closeInterpolationBrace = () => {
    const frame = interpolationFrames[interpolationFrames.length - 1];
    frame.braceDepth -= 1;
    if (frame.braceDepth === 0) {
      interpolationFrames.pop();
      string = frame.returnString;
    }
  };

  const scanChar = (ch, next, include, text, index) => {
    if (ch === '\n') {
      lineComment = false;
      flush();
      remember(ch);
      return 1;
    }

    if (lineComment) return 1;

    if (commentDepth > 0) {
      if (ch === '/' && next === '-') {
        commentDepth += 1;
        return 2;
      }
      if (ch === '-' && next === '/') {
        commentDepth -= 1;
        return 2;
      }
      return 1;
    }

    if (escapedIdent) {
      emit(ch, include);
      remember(ch);
      if (ch === '»') escapedIdent = false;
      return 1;
    }

    if (charLiteral) {
      emit(ch, include);
      remember(ch);
      if (charEscaped) {
        charEscaped = false;
      } else if (ch === '\\') {
        charEscaped = true;
      } else if (ch === "'") {
        charLiteral = false;
      }
      return 1;
    }

    if (string) {
      if (string.rawTerminator) {
        if (ch === '"' && text.slice(index, index + string.rawTerminator.length) === string.rawTerminator) {
          const length = string.rawTerminator.length;
          if (options.preserveStrings) emitText(string.rawTerminator, include);
          rememberText(string.rawTerminator);
          string = null;
          return length;
        }
        if (options.preserveStrings) emit(ch, include);
        remember(ch);
        return 1;
      }
      if (string.escaped) {
        if (options.preserveStrings) emit(ch, include);
        remember(ch);
        string.escaped = false;
        return 1;
      }
      if (ch === '\\') {
        if (options.preserveStrings) emit(ch, include);
        remember(ch);
        string.escaped = true;
        return 1;
      }
      if (string.interpolated && ch === '{') {
        if (options.preserveStrings) emit(ch, include);
        remember(ch);
        openInterpolation();
        return 1;
      }
      if (!string.rawTerminator && ch === '"') {
        if (options.preserveStrings) emit(ch, include);
        remember(ch);
        string = null;
        return 1;
      }
      if (options.preserveStrings) emit(ch, include);
      remember(ch);
      return 1;
    }

    if (ch === '-' && next === '-') {
      lineComment = true;
      return 2;
    }
    if (ch === '/' && next === '-') {
      commentDepth = 1;
      return 2;
    }
    if (ch === '«') {
      escapedIdent = true;
      emit(ch, include);
      remember(ch);
      return 1;
    }
    if (ch === '"') {
      const rawTerminator = rawStringTerminatorBeforeQuote(prefix);
      const interpolated = /[A-Za-z]!$/.test(prefix);
      if (options.preserveStrings) emit(ch, include);
      remember(ch);
      openString(interpolated && !rawTerminator, rawTerminator);
      return 1;
    }
    if (ch === "'" && startsLeanCharLiteral(text, index)) {
      charLiteral = true;
      charEscaped = false;
      emit(ch, include);
      remember(ch);
      return 1;
    }
    if (inInterpolationCode() && ch === '{') {
      interpolationFrames[interpolationFrames.length - 1].braceDepth += 1;
      emit(ch, include);
      remember(ch);
      return 1;
    }
    if (inInterpolationCode() && ch === '}') {
      if (options.preserveStrings) emit(ch, include);
      remember(ch);
      closeInterpolationBrace();
      return 1;
    }

    emit(ch, include);
    remember(ch);
    return 1;
  };

  return {
    scanLine(text, include) {
      const line = `${String(text || '')}\n`;
      for (let i = 0; i < line.length;) {
        i += scanChar(line[i], line[i + 1], include, line, i);
      }
    },
    finish() {
      flush();
      return code;
    },
  };
}

function isLeanIdentContinue(ch) {
  return /^[\p{L}\p{N}\p{M}_]$/u.test(ch);
}

function rawStringTerminatorBeforeQuote(prefix) {
  const match = String(prefix || '').match(/r(#{0,16})$/);
  if (!match) return null;
  return `"${match[1]}`;
}

function startsLeanCharLiteral(text, quoteIndex) {
  const previous = previousCodePoint(text, quoteIndex);
  return previous !== "'" && !isLeanIdentContinue(previous);
}

function previousCodePoint(text, index) {
  if (index <= 0) return '';
  const points = Array.from(text.slice(0, index));
  return points[points.length - 1] || '';
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
    if (line.type === 'add' && Number.isFinite(line.newLine)) return line.newLine;
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
    filePath.startsWith('.github/') ||
    /\.(py|sh|bash|js|ts|json|ya?ml|toml)$/.test(filePath);
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
      enabled: decision.mode === 'large-lean-hotspots' && (decision.packets?.length || 0) > 0,
      packets_selected: decision.packets?.length || 0,
      packet_budget: THRESHOLDS.packetMaxCount,
      packets: (decision.packets || []).map(p => ({
        path: p.path,
        start_line: p.start_line,
        end_line: p.end_line,
        score: p.score,
        packet_id: p.packet_id,
        category: p.category,
        signals: p.signals,
        summary: p.summary,
        scout_reason: p.scout_reason || null,
        scout_risk_category: p.scout_risk_category || null,
        scout_question: p.scout_question || null,
        scout_lens_ids: Array.isArray(p.scout_lens_ids) ? p.scout_lens_ids : null,
        changed_lines: p.changed_lines,
      })),
      residual_risk: packetResidualRisk(decision),
      scout: decision.scout || null,
      strong_review_required: decision.mode === 'large-lean-hotspots',
      strong_review_status: decision.scout?.strong_review_status || 'blocked_packet_input',
      strong_review_blocker: decision.scout?.strong_review_blocker || STRONG_REVIEW_BLOCKER_MESSAGE,
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
  if (decision.mode === 'large-lean-hotspots' && (decision.packets?.length || 0) > 0) {
    return buildPacketizedResult(decision, metrics);
  }

  return {
    status: decision.mode,
    message: decision.reason,
    comments: [],
    warnings: decision.mode === 'large-lean-hotspots'
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
  const scout = decision.scout || {};
  const reviewLabel = scout.attempted
    ? `Scout triage ${scout.status}; strong packet review required.`
    : 'Deterministic fallback triage; scout model not configured and strong packet review required.';
  return {
    status: 'scout_triage',
    message: `${decision.reason} ${reviewLabel} Full-file OCR was not attempted.`,
    comments: packets.map(packet => ({
      path: packet.path,
      start_line: packet.start_line,
      end_line: packet.end_line,
      category: 'large-lean-hotspots',
      severity: packet.score >= 90 ? 'high' : packet.score >= 60 ? 'medium' : 'low',
      content: renderPacketFinding(packet),
    })),
    warnings: [{
      type: 'coverage',
      message: 'Large Lean scout mode covers ranked hotspots only. Scout-selected packets get a bounded semantic OCR pass (see packet coverage); Codex/human review must still cover unselected hunks and proof obligations.',
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
  // Reader-first ordering: the substantive finding leads, the router's
  // selection rationale follows, and the triage caveat closes.
  const lines = [];
  const lensFindings = Array.isArray(packet.scout_lenses) ? packet.scout_lenses : [];
  if (lensFindings.length > 1) {
    // Multi-lens: this packet tripped more than one lens, so list every lens's
    // finding — that is the whole point of the fan-out (surface all defect
    // classes at once instead of one per review cycle).
    lines.push(`**Findings (${lensFindings.length} lenses):**`);
    for (const finding of lensFindings) {
      const label = sanitizeCommentText(finding.lens_title || finding.lens || 'lens');
      const detail = sanitizeCommentText(finding.reason || '(no detail)');
      lines.push(`- _${label}:_ ${detail}`);
      if (finding.question) {
        lines.push(`  - Ask the reviewer: ${sanitizeCommentText(finding.question)}`);
      }
    }
  } else {
    if (packet.scout_reason) {
      lines.push(`**Finding:** ${sanitizeCommentText(packet.scout_reason)}`);
    }
    if (packet.scout_question) {
      lines.push(`**Ask the reviewer:** ${sanitizeCommentText(packet.scout_question)}`);
    }
  }
  lines.push(
    `**Why flagged:** ${packet.summary}. Signals: ${
      packet.signals.length ? packet.signals.join(', ') : 'hotspot path/churn'
    }.`,
  );
  if (packet.added_sample.length > 0) {
    lines.push('Added-line sample:');
    for (const sample of packet.added_sample.slice(0, 5)) {
      lines.push(`- L${sample.line}: ${renderCodeSample(sample.text)}`);
    }
  }
  return lines.join('\n');
}

// Neutralize injection vectors (mentions, raw HTML, control characters) in
// model-authored prose WITHOUT destroying markdown readability: code spans,
// dots, hyphens, and paragraph breaks survive. Length-capped at a word
// boundary with an explicit truncation marker instead of a mid-word cut.
function sanitizeCommentText(value) {
  const text = String(value || '')
    .replace(/\r\n?/g, '\n')
    .replace(/[\u0000-\u0009\u000b-\u001f\u007f]/g, ' ')
    .replace(/@/g, '@\u200b')
    .replace(/[<>]/g, ch => ({ '<': '&lt;', '>': '&gt;' }[ch]))
    .replace(/[^\S\n]+/g, ' ')
    .replace(/ ?\n ?/g, '\n')
    .replace(/\n{3,}/g, '\n\n')
    .trim();
  if (text.length <= 1200) return text;
  const cut = text.slice(0, 1200);
  const boundary = cut.lastIndexOf(' ');
  return `${boundary > 800 ? cut.slice(0, boundary) : cut} \u2026 _(truncated)_`;
}

// Added-line samples are code: render as an inline code span so Lean/Yul
// operators are not read as markdown. Inside a code span mentions and HTML
// are inert; the plain-text fallback (sample contains a backtick) gets the
// usual neutralization instead.
function renderCodeSample(value) {
  const text = String(value || '')
    .replace(/[\u0000-\u001f\u007f]/g, ' ')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 200);
  if (!text) return '`(empty)`';
  // Backticks inside a sample would terminate the code span; substitute a
  // prime mark so the sample still renders inertly inside one code span
  // (no markdown, mentions, or HTML interpretation) instead of falling back
  // to prose rendering.
  return `\`${text.replace(/`/g, '\u2032')}\``;
}

function packetResidualRisk(decision) {
  if (decision.mode === 'large-lean-hotspots' && (decision.packets?.length || 0) > 0) {
    const basis = decision.scout?.attempted && decision.scout?.status === 'success' ? 'scout-ranked' : 'deterministically ranked';
    return `Triaged top ${decision.packets?.length || 0} ${basis} packet(s); remaining changed hunks/files require Codex or human proof review, and selected packets still need strong reviewer analysis.`;
  }
  if (decision.mode === 'large-lean-hotspots' && ((decision.counts?.lean || 0) > THRESHOLDS.packetMaxFiles || (decision.changedLines || 0) > THRESHOLDS.packetMaxChangedLines)) {
    return 'Diff exceeded packet budget; use top changed files and deterministic signals as required Codex/human review checklist.';
  }
  if (decision.mode === 'large-lean-hotspots') {
    return 'Router could not produce safe diff packets; use top changed files as required Codex/human review checklist.';
  }
  return null;
}

function shouldReportPacketReview(decision) {
  return decision.mode === 'large-lean-hotspots';
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
  main().catch(err => {
    console.error(err);
    process.exit(1);
  });
}

module.exports = {
  ROUTER_VERSION,
  THRESHOLDS,
  DEFAULT_SCOUT_MODEL,
  LENSES,
  categorize,
  decideRoute,
  isSupported,
  parseNumstatLine,
  buildSyntheticResult,
  buildMetrics,
  buildReviewPackets,
  applyScoutStage,
  resolveScoutConfig,
  resolveLenses,
  loadRubric,
  appendRubricItem,
  unionScoutPackets,
  renderPacketFinding,
  writePacketReviewPlan,
  leanOutlineForFile,
  parseScoutJson,
  sanitizeScoutErrorDetail,
  buildRiskDossier,
  parseUnifiedDiff,
  scorePathRisk,
  loadDiff,
};
