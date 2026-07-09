'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const ROUTER_VERSION = 'router-v8';
const DEFAULT_SCOUT_MODEL = 'MiniMax-M3';
const STRONG_REVIEW_BLOCKER_MESSAGE = 'OpenCodeReview 1.7.5 supports --from/--to full diff ranges, but this workflow does not have a safe packet/window input bridge for Lean hunks yet.';
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
  scoutTimeoutMs: 45000,
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
  if (decision.scout) {
    console.log(`Scout enabled: ${decision.scout.enabled}; model: ${decision.scout.model || DEFAULT_SCOUT_MODEL}; status: ${decision.scout.status}`);
  }
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
  decision.scout = {
    enabled,
    configured: Boolean(config.url && config.key && config.model),
    attempted: false,
    status: scoutSwitchOn ? 'not_configured' : 'disabled',
    model: config.model ? redactModel(config.model) : DEFAULT_SCOUT_MODEL,
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
  try {
    const dossier = buildRiskDossier(decision, diff);
    const scout = await callScoutModel(config, dossier);
    const selected = selectScoutPackets(deterministicPackets, scout);
    decision.scout.raw_selected_count = Array.isArray(scout.selected_packets) ? scout.selected_packets.length : null;
    if (selected.length > 0) {
      decision.packets = selected;
      decision.reason = `${decision.reason} Scout model ranked ${selected.length}/${deterministicPackets.length} packet(s) for stronger review.`;
      decision.scout.selected_packets = selected.map(p => p.packet_id);
      decision.scout.status = 'success';
      decision.scout.summary = scout.summary || '';
      decision.scout.residual_coverage = scout.residual_coverage || decision.scout.residual_coverage;
    } else {
      decision.scout.status = 'fallback_no_selection';
      decision.scout.summary = scout.summary || 'Scout returned no valid packet IDs; deterministic ranking retained.';
      decision.scout.residual_coverage = 'Scout returned no valid packet IDs, so deterministic packet ranking was retained and all selected packets still need strong reviewer analysis.';
    }
  } catch (err) {
    decision.scout.status = 'fallback_deterministic';
    decision.scout.error = 'Scout model call failed; deterministic packet ranking retained.';
    decision.scout.error_type = classifyScoutError(err);
    decision.scout.error_detail = sanitizeScoutErrorDetail(err);
    if (err?.status) decision.scout.http_status = err.status;
  }
  return decision;
}

function buildRiskDossier(decision, diff) {
  const packets = (decision.packets || []).map(packet => ({
    id: packet.packet_id,
    file: packet.path,
    line_window: { start: packet.start_line, end: packet.end_line },
    score: packet.score,
    risk_category: packet.signals,
    summary: packet.summary,
    changed_lines: packet.changed_lines,
    diff_excerpt: packet.diff_excerpt,
  }));

  const supported = diff.files.filter(f => f.supported);
  const dossier = {
    schema_version: 1,
    task: 'Rank dangerous Lean review packets for a stronger reviewer. Do not approve the PR.',
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

async function callScoutModel(config, dossier) {
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), THRESHOLDS.scoutTimeoutMs);
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
            content: 'You are a cautious Lean proof-change triage scout. Return only JSON matching the requested schema. Never claim final review coverage or approval.',
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
  const start = text.indexOf('{');
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
    } else if (ch === '{') {
      depth += 1;
    } else if (ch === '}') {
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
  const structured = redactStructuredError(raw);
  return redactSecretText(structured || raw)
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 500);
}

function redactStructuredError(text) {
  const trimmed = String(text || '').trim();
  if (!trimmed || !/^[\[{]/.test(trimmed)) return null;
  try {
    return JSON.stringify(redactSecretJsonValue(JSON.parse(trimmed)));
  } catch {
    return null;
  }
}

function redactSecretJsonValue(value, key = '') {
  if (isSecretKey(key)) return '[redacted]';
  if (Array.isArray(value)) return value.map(item => redactSecretJsonValue(item));
  if (value && typeof value === 'object') {
    const secretContext = Object.entries(value).some(([childKey, childValue]) => {
      if (!/^(field|param|parameter|name|key|loc|path)$/i.test(childKey)) return false;
      return hasSecretIndicator(childValue);
    });
    return Object.fromEntries(Object.entries(value).map(([childKey, childValue]) => [
      childKey,
      secretContext && /^(value|input|provided|actual)$/i.test(childKey)
        ? '[redacted]'
        : redactSecretJsonValue(childValue, childKey),
    ]));
  }
  if (typeof value === 'string') return redactSecretText(value);
  return value;
}

function hasSecretIndicator(value) {
  if (Array.isArray(value)) return value.some(hasSecretIndicator);
  if (value && typeof value === 'object') return Object.values(value).some(hasSecretIndicator);
  return isSecretKey(String(value || ''));
}

function isSecretKey(key) {
  const normalized = String(key || '')
    .replace(/([a-z0-9])([A-Z])/g, '$1_$2')
    .replace(/[\s-]+/g, '_')
    .toLowerCase();
  return normalized === 'token'
    || /(^|_)(api_key|access_token|refresh_token|id_token|client_secret|api_secret|private_key|bearer_token|session_secret|session_token|authorization|password|secret)($|_)/.test(normalized);
}

function redactSecretText(text) {
  return String(text || '')
    .replace(/https?:\/\/[^\s"')]+/g, '[url-redacted]')
    .replace(/\beyJ[A-Za-z0-9_-]+\.eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\b/g, '[redacted]')
    .replace(/Bearer\s+[A-Za-z0-9._~+/-]+={0,2}/gi, 'Bearer [redacted]')
    .replace(/\bsk-[A-Za-z0-9._-]+/gi, '[redacted]')
    .replace(/\b(api\s*key|api[_-]?key|access[_-]?token|refresh[_-]?token|id[_-]?token|client[_-]?secret|api[_-]?secret|private[_-]?key|bearer[_-]?token|session[_-]?(?:secret|token)|token|authorization|password|secret)(\s*[:=]\s*)(["'`])(?:\\.|(?!\3).){0,300}\3/gi, '$1$2$3[redacted]$3')
    .replace(/\b(?![a-f0-9]{40}\b)(?=[A-Za-z0-9._~+/-]{32,}\b)(?=[A-Za-z0-9._~+/-]*[A-Za-z])(?=[A-Za-z0-9._~+/-]*\d)[A-Za-z0-9._~+/-]{32,}={0,2}\b/g, '[redacted]')
    .replace(/\b((?:api\s*key|api[_-]?key|access[_-]?token|refresh[_-]?token|id[_-]?token|client[_-]?secret|api[_-]?secret|private[_-]?key|bearer[_-]?token|session[_-]?(?:secret|token)|token|authorization|password|secret)\b[^"'`\n]{0,120}?)([A-Za-z0-9._~+/-]{12,}={0,2})/gi, '$1[redacted]');
}

function openAiChatUrl(baseUrl) {
  const trimmed = String(baseUrl || '').replace(/\/+$/, '');
  if (trimmed.endsWith('/chat/completions')) return trimmed;
  if (trimmed.endsWith('/v1')) return `${trimmed}/chat/completions`;
  return `${trimmed}/v1/chat/completions`;
}

function selectScoutPackets(deterministicPackets, scout) {
  const byId = new Map(deterministicPackets.map(p => [p.packet_id, p]));
  const selected = [];
  for (const item of Array.isArray(scout?.selected_packets) ? scout.selected_packets : []) {
    const packet = byId.get(String(item.id || item.packet_id || '').trim());
    if (!packet || selected.some(p => p.packet_id === packet.packet_id)) continue;
    selected.push({
      ...packet,
      scout_reason: String(item.reason || '').slice(0, 500),
      scout_risk_category: String(item.risk_category || '').slice(0, 120),
      scout_question: String(item.question_for_stronger_reviewer || '').slice(0, 500),
    });
  }
  return selected.slice(0, THRESHOLDS.packetMaxCount);
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
  const added = hunk.lines.filter(l => l.type === 'add').map(l => l.text);
  const deleted = hunk.lines.filter(l => l.type === 'del').map(l => l.text);
  const addedCode = codeLines(added);
  const deletedCode = codeLines(deleted);
  const allChanged = [...addedCode, ...deletedCode];

  if (addedCode.some(line => /\b(sorry|admit)\b/.test(line))) add('introduced sorry/admit', 80);
  if (addedCode.some(line => /^\s*axiom\b/.test(line) || /\baxiom\b/.test(line))) add('introduced/changed axiom', 75);
  if (addedCode.some(line => /\bunsafe\b/.test(line))) add('introduced unsafe', 55);
  if (allChanged.some(line => /^\s*import\s+/.test(line))) add('changed imports', 30);
  if (allChanged.some(line => publicDeclPattern().test(line))) add('public declaration/signature changed', 34);
  if (file.category === 'trust-doc') add('trust-boundary docs drift', 38);
  if (file.category === 'doc' && /(trust|axiom|audit|sound|semantic|proof)/i.test(file.path)) add('trust/proof docs drift', 25);
  if (deletedCode.length >= 80 || deletedCode.join('\n').length > 6000) add('large deleted proof obligation', 35);
  if (deletedCode.some(line => publicDeclPattern().test(line)) && addedCode.some(line => publicDeclPattern().test(line))) {
    add('theorem/public statement changed', 45);
  }
  if (changedTheoremStatements(deletedCode, addedCode).length > 0) add('theorem statement changed/possibly weakened', 65);

  return [...signals.values()].sort((a, b) => b.weight - a.weight || a.name.localeCompare(b.name));
}

function codeLines(lines) {
  const code = [];
  let inBlockComment = false;
  for (const line of lines) {
    const stripped = stripLeanCommentsFromLine(line, { inBlockComment });
    inBlockComment = stripped.inBlockComment;
    if (stripped.code.trim()) code.push(stripped.code);
  }
  return code;
}

function stripLeanCommentsFromLine(line, state) {
  let rest = String(line || '');
  let code = '';
  let inBlockComment = Boolean(state.inBlockComment);

  while (rest) {
    if (inBlockComment) {
      const blockEnd = rest.indexOf('-/');
      if (blockEnd === -1) return { code, inBlockComment: true };
      rest = rest.slice(blockEnd + 2);
      inBlockComment = false;
      continue;
    }

    const lineComment = rest.indexOf('--');
    const blockStart = rest.indexOf('/-');
    if (lineComment !== -1 && (blockStart === -1 || lineComment < blockStart)) {
      code += rest.slice(0, lineComment);
      return { code, inBlockComment: false };
    }
    if (blockStart === -1) {
      code += rest;
      return { code, inBlockComment: false };
    }

    code += rest.slice(0, blockStart);
    rest = rest.slice(blockStart + 2);
    const blockEnd = rest.indexOf('-/');
    if (blockEnd === -1) return { code, inBlockComment: true };
    rest = rest.slice(blockEnd + 2);
  }

  return { code, inBlockComment };
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
      message: 'Large Lean scout mode covers ranked hotspots only. Codex/human review must cover skipped hunks and proof obligations; OCR strong packet review is not wired yet.',
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
    `Large Lean packet selected for stronger review: ${packet.summary}.`,
    `Risk signals: ${packet.signals.length ? packet.signals.join(', ') : 'hotspot path/churn'}.`,
  ];
  if (packet.scout_reason) lines.push(`Scout reason: ${sanitizeCommentText(packet.scout_reason)}`);
  if (packet.scout_question) lines.push(`Question for stronger reviewer: ${sanitizeCommentText(packet.scout_question)}`);
  if (packet.added_sample.length > 0) {
    lines.push('Added-line sample:');
    for (const sample of packet.added_sample.slice(0, 5)) {
      lines.push(`- L${sample.line}: ${sanitizeCommentText(sample.text)}`);
    }
  }
  lines.push('This packet is scout triage and a coverage marker; it is not a final OCR semantic review or approval.');
  return lines.join('\n');
}

function sanitizeCommentText(value) {
  return String(value || '')
    .replace(/[\u0000-\u001f\u007f]/g, ' ')
    .replace(/@/g, '@\u200b')
    .replace(/[<>]/g, ch => ({ '<': '&lt;', '>': '&gt;' }[ch]))
    .replace(/([\\`*_{}\[\]()#+.!|-])/g, '\\$1')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 700);
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
  categorize,
  decideRoute,
  isSupported,
  parseNumstatLine,
  buildSyntheticResult,
  buildMetrics,
  buildReviewPackets,
  applyScoutStage,
  resolveScoutConfig,
  parseScoutJson,
  sanitizeScoutErrorDetail,
  buildRiskDossier,
  parseUnifiedDiff,
  scorePathRisk,
};
