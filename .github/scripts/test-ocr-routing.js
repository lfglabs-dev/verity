'use strict';

const assert = require('assert');
const fs = require('fs');
const os = require('os');
const path = require('path');

const router = require('./ocr-router');
const postOcrReview = require('./post-ocr-review');

function file(filePath, added = 10, deleted = 0) {
  return {
    path: filePath,
    added,
    deleted,
    changed: added + deleted,
    category: router.categorize(filePath),
    supported: router.isSupported(filePath),
    hunks: [hunk(filePath, 10, [
      ['ctx', 'namespace Verity'],
      ['add', 'theorem soundness_preserved : True := by trivial'],
      ['add', 'unsafe def riskyFastPath := 1'],
      ['ctx', 'end Verity'],
    ])],
  };
}

function hunk(filePath, newStart, lines) {
  let next = newStart;
  return {
    path: filePath,
    oldStart: newStart,
    newStart,
    newSpan: lines.length,
    header: '',
    lines: lines.map(([type, text]) => {
      const entry = {
        type,
        text,
        newLine: type === 'del' ? null : next,
        oldLine: type === 'add' ? null : next,
      };
      if (type !== 'del') next += 1;
      return entry;
    }),
  };
}

function testNoSupportedFilesSkipped() {
  const decision = router.decideRoute([
    file('packages/cache.lock', 3, 1),
    file('build/generated.out', 5, 0),
  ]);
  assert.strictEqual(decision.mode, 'no-supported');
  assert.strictEqual(decision.shouldRunOcr, false);
}

function testOneLeanFileNormal() {
  const decision = router.decideRoute([
    file('Compiler/Proofs/IRGeneration/Small.lean', 120, 20),
  ]);
  assert.strictEqual(decision.mode, 'small-lean');
  assert.strictEqual(decision.shouldRunOcr, true);
  assert.strictEqual(decision.ocr.concurrency, 3);
}

function testLargeLeanPacketized() {
  const decision = router.decideRoute([
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ]);
  assert.strictEqual(decision.mode, 'large-lean-hotspots');
  assert.strictEqual(decision.shouldRunOcr, false);
  assert.ok(decision.packets.length > 0);
  assert.ok(decision.packets[0].signals.includes('introduced unsafe'));
  assert.strictEqual(decision.packets[0].end_line, 12);
}

function testLeanCommentDoesNotTriggerSorrySignal() {
  const leanFile = file('Compiler/Proofs/Comment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/Comment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', "-- Total: 0 sorry'd proofs"],
    ['add', 'theorem still_ok : True := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanBlockCommentDoesNotTriggerSorrySignal() {
  const leanFile = file('Compiler/Proofs/BlockComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/BlockComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', '/-'],
    ['add', 'This proof used to mention sorry in prose.'],
    ['add', '-/'],
    ['add', 'theorem still_ok : True := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
}

function testCodeAfterInlineBlockCommentIsScanned() {
  const leanFile = file('Compiler/Proofs/InlineBlockComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InlineBlockComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', '/- rationale -/ axiom bad : False'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced/changed axiom'));
}

function testOversizedLeanGuarded() {
  const files = Array.from({ length: 13 }, (_, i) => file(`Compiler/Proofs/Large${i}.lean`, 40, 0));
  const decision = router.decideRoute(files);
  assert.strictEqual(decision.mode, 'large-lean-hotspots');
  assert.strictEqual(decision.shouldRunOcr, false);
}

async function testLargeLeanScoutNotConfiguredFallsBack() {
  const files = [
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ];
  const decision = router.decideRoute(files);
  await router.applyScoutStage(decision, { files }, { url: '', key: '', model: '' });
  assert.strictEqual(decision.mode, 'large-lean-hotspots');
  assert.strictEqual(decision.scout.enabled, false);
  assert.strictEqual(decision.scout.status, 'not_configured');
  assert.strictEqual(decision.scout.model, 'MiniMax-M3');
  assert.strictEqual(decision.scout.strong_review_status, 'blocked_packet_input');
}

function testScoutConfigDefaultsToMiniMaxOnOcrEndpoint() {
  const config = router.resolveScoutConfig({
    OCR_LLM_URL: 'https://sandboxed.example/v1',
    OCR_LLM_KEY: 'shared-key',
  });
  assert.strictEqual(config.enabled, true);
  assert.strictEqual(config.url, 'https://sandboxed.example/v1');
  assert.strictEqual(config.key, 'shared-key');
  assert.strictEqual(config.model, 'MiniMax-M3');
  const workflow = fs.readFileSync(path.join(__dirname, '..', 'workflows', 'ocr-review.yml'), 'utf8');
  assert.ok(workflow.includes('OCR_LLM_MODEL: reviewer'));
}

function testScoutConfigCanDisableLargeLeanScout() {
  const config = router.resolveScoutConfig({
    OCR_SCOUT_ENABLED: 'false',
    OCR_LLM_URL: 'https://sandboxed.example/v1',
    OCR_LLM_KEY: 'shared-key',
  });
  assert.strictEqual(config.enabled, false);
  assert.strictEqual(config.model, 'MiniMax-M3');
}

function testScoutJsonParsingHandlesMiniMaxThinkingWrapper() {
  const parsed = router.parseScoutJson('<mm:think>ranking packets</mm:think>\n```json\n{"selected_packets":[],"residual_coverage":"none","summary":"ok"}\n```');
  assert.deepStrictEqual(parsed.selected_packets, []);
  assert.strictEqual(parsed.summary, 'ok');
}

async function testLargeLeanScoutSelectsPackets() {
  const files = [
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ];
  const decision = router.decideRoute(files);
  const targetPacket = decision.packets[1];
  const oldFetch = global.fetch;
  global.fetch = async () => ({
    ok: true,
    text: async () => JSON.stringify({
      choices: [{
        message: {
          content: JSON.stringify({
            selected_packets: [{
              id: targetPacket.packet_id,
              reason: 'The public theorem signature and unsafe helper sit in a proof hotspot.',
              risk_category: 'semantic hotspot',
              file: targetPacket.path,
              line_window: { start: targetPacket.start_line, end: targetPacket.end_line },
              question_for_stronger_reviewer: 'Does this preserve the theorem obligation under the changed helper?',
            }],
            residual_coverage: 'Other packets still require Codex/human review.',
            summary: 'One hotspot selected.',
          }),
        },
      }],
    }),
  });
  try {
    await router.applyScoutStage(decision, { files }, { url: 'https://example.invalid/v1', key: 'test-key', model: 'cheap-scout' });
  } finally {
    global.fetch = oldFetch;
  }
  assert.strictEqual(decision.scout.enabled, true);
  assert.strictEqual(decision.scout.status, 'success');
  assert.strictEqual(decision.packets.length, 1);
  assert.strictEqual(decision.packets[0].packet_id, targetPacket.packet_id);
  assert.ok(decision.packets[0].scout_question.includes('preserve'));
}

async function testLargeLeanScoutEmptySelectionIsFallback() {
  const files = [
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ];
  const decision = router.decideRoute(files);
  const originalPackets = decision.packets.map(p => p.packet_id);
  const oldFetch = global.fetch;
  global.fetch = async () => ({
    ok: true,
    text: async () => JSON.stringify({
      choices: [{
        message: {
          content: JSON.stringify({
            selected_packets: [{ id: 'missing-packet', reason: 'bad id' }],
            residual_coverage: 'Scout did not select a valid packet.',
            summary: 'No valid selection.',
          }),
        },
      }],
    }),
  });
  try {
    await router.applyScoutStage(decision, { files }, { url: 'https://example.invalid/v1', key: 'test-key', model: 'cheap-scout' });
  } finally {
    global.fetch = oldFetch;
  }
  assert.strictEqual(decision.scout.status, 'fallback_no_selection');
  assert.deepStrictEqual(decision.packets.map(p => p.packet_id), originalPackets);
  assert.strictEqual(decision.scout.raw_selected_count, 1);
}

async function testLargeLeanScoutMalformedJsonFallsBack() {
  const files = [
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ];
  const decision = router.decideRoute(files);
  const originalPackets = decision.packets.map(p => p.packet_id);
  const oldFetch = global.fetch;
  global.fetch = async () => ({
    ok: true,
    text: async () => JSON.stringify({
      choices: [{
        message: {
          content: '{"selected_packets": [',
        },
      }],
    }),
  });
  try {
    await router.applyScoutStage(decision, { files }, { enabled: true, url: 'https://example.invalid/v1', key: 'test-key', model: 'MiniMax-M3' });
  } finally {
    global.fetch = oldFetch;
  }
  assert.strictEqual(decision.scout.status, 'fallback_deterministic');
  assert.strictEqual(decision.scout.error_type, 'invalid_json');
  assert.deepStrictEqual(decision.packets.map(p => p.packet_id), originalPackets);
}

async function testLargeLeanScoutApiFailureFallsBack() {
  const files = [
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ];
  const decision = router.decideRoute(files);
  const originalPackets = decision.packets.map(p => p.packet_id);
  const oldFetch = global.fetch;
  global.fetch = async () => ({
    ok: false,
    status: 400,
    text: async () => 'model MiniMax-M3 is not available at https://sandboxed.example/v1 with token abcdefghijklmnopqrstuvwxyz1234567890',
  });
  try {
    await router.applyScoutStage(decision, { files }, { url: 'https://example.invalid/v1', key: 'test-key', model: 'cheap-scout' });
  } finally {
    global.fetch = oldFetch;
  }
  assert.strictEqual(decision.scout.status, 'fallback_deterministic');
  assert.strictEqual(decision.scout.error, 'Scout model call failed; deterministic packet ranking retained.');
  assert.strictEqual(decision.scout.error_type, 'http_error');
  assert.strictEqual(decision.scout.http_status, 400);
  assert.ok(decision.scout.error_detail.includes('MiniMax-M3'));
  assert.ok(!decision.scout.error_detail.includes('sandboxed.example'));
  // The test token is redacted by the explicit `token <value>` sanitizer path.
  assert.ok(!decision.scout.error_detail.includes('abcdefghijklmnopqrstuvwxyz'));
  assert.deepStrictEqual(decision.packets.map(p => p.packet_id), originalPackets);
}

function testScoutErrorSanitizesApiKeyPhrases() {
  const detail = router.sanitizeScoutErrorDetail(
    'Incorrect API key provided: sk-test_abcdefghijklmnopqrstuvwxyz123456. Model MiniMax-M3 rejected the request.'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('sk-test'));
}

function testScoutErrorSanitizesStructuredSecrets() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    api_key: ['abcdefghijklmnopqrstuvwxyz123456'],
    minimax_api_key: 'abcdefghijklmnopqrstuvwxyz123459',
    openaiApiKey: 'abcdefghijklmnopqrstuvwxyz123460',
    access_token: 'abcdefghijklmnopqrstuvwxyz123456',
    refreshToken: 'abcdefghijklmnopqrstuvwxyz123457',
    nested: {
      authorization: { token: 'sk-test_abcdefghijklmnopqrstuvwxyz123456' },
      client_secret: 'abcdefghijklmnopqrstuvwxyz123458',
    },
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz'));
  assert.ok(!detail.includes('sk-test'));
}

function testScoutErrorSanitizesJwtWithoutDroppingPlainDiagnostics() {
  const jwt = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
  const detail = router.sanitizeScoutErrorDetail(`token expired for MiniMax-M3. Bearer ${jwt}`);
  assert.ok(detail.includes('token expired'));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('Bearer [redacted]'));
  assert.ok(!detail.includes(jwt));
}

function testScoutErrorSanitizesBareCredentialLikeStrings() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    detail: 'credential abcdefghijklmnopqrstuvwxyz1234567890 rejected',
    commit: 'dcefe61cc822fc32c7f69d0570aa7278bec45605',
    page_token: 'next-page-for-debugging',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('dcefe61cc822fc32c7f69d0570aa7278bec45605'));
  assert.ok(detail.includes('next-page-for-debugging'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz1234567890'));
}

function testScoutErrorSanitizesQuotedFallbackDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    '400 Bad Request: {"api_key":"abcdefghijklmnopqrstuvwxyz123456","error":"invalid MiniMax-M3 request"}'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123456'));
}

function testScoutErrorSanitizesFieldValueDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    issues: [
      { field: 'api_key', value: 'abcdefghijklmnopqrstuvwxyz123456' },
      { loc: ['body', 'client_secret'], input: 'abcdefghijklmnopqrstuvwxyz123457' },
    ],
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123456'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123457'));
}

function testScoutErrorSanitizesShortQuotedProviderDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    'Incorrect API key provided: "abcdefghijklmnop123456". Model MiniMax-M3 rejected the request.'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('abcdefghijklmnop123456'));
}

function testScoutErrorSanitizesAdditionalCredentialKeys() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    credential: 'short-secret',
    passphrase: 'another-short-secret',
    authcode: 'auth-short-secret',
    client_id: 'client-short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorPreservesUuidDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 trace id 550e8400-e29a-41d4-a716-446655440000 failed'
  );
  assert.ok(detail.includes('550e8400-e29a-41d4-a716-446655440000'));
}

async function testLargeLeanScoutNoPacketsStatus() {
  const files = Array.from({ length: 13 }, (_, i) => file(`Compiler/Proofs/Large${i}.lean`, 40, 0));
  const decision = router.decideRoute(files);
  await router.applyScoutStage(decision, { files }, { url: 'https://example.invalid/v1', key: 'test-key', model: 'cheap-scout' });
  assert.strictEqual(decision.scout.enabled, true);
  assert.strictEqual(decision.scout.status, 'skipped_no_packets');
}

function testWorkflowDocsEnabled() {
  const decision = router.decideRoute([
    file('.github/workflows/ocr-review.yml', 80, 10),
    file('docs/ocr.md', 900, 4),
  ]);
  assert.strictEqual(decision.mode, 'config-docs');
  assert.strictEqual(decision.shouldRunOcr, true);
}

function testGenericScriptConfigEnabled() {
  const decision = router.decideRoute([
    file('scripts/deploy.sh', 20, 4),
    file('package.json', 6, 1),
    file('config/app.yml', 5, 2),
  ]);
  assert.strictEqual(decision.mode, 'config-docs');
  assert.strictEqual(decision.shouldRunOcr, true);
  assert.strictEqual(decision.counts.workflowScripts, 3);
}

async function testCompletedWithErrorsRetryablePreservesFindings() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-post-test-'));
  const resultPath = path.join(dir, 'result.json');
  const metricsPath = path.join(dir, 'metrics.json');
  fs.writeFileSync(resultPath, JSON.stringify({
    status: 'completed_with_errors',
    comments: [{
      path: 'Compiler/Proofs/Contract.lean',
      start_line: 42,
      content: 'Potential weakened theorem statement.',
      category: 'proof',
      severity: 'high',
    }],
    summary: { files_reviewed: 1, total_tokens: 12345 },
    tool_calls: { total: 7 },
    warnings: [{ type: 'timeout', message: 'Subtask deadline exceeded' }],
  }));
  fs.writeFileSync(metricsPath, JSON.stringify({
    started_at: new Date(Date.now() - 1000).toISOString(),
    router_version: router.ROUTER_VERSION,
    mode: 'medium-lean',
    thresholds: router.THRESHOLDS,
    changed_files: {
      counts: { total: 1, supported: 1, lean: 1, trustDocs: 0, workflowScripts: 0, contracts: 0, docs: 0 },
      total_changed_lines: 60,
      largest: [{ path: 'Compiler/Proofs/Contract.lean', added: 50, deleted: 10, changed: 60, category: 'lean' }],
    },
    ocr: { attempted: true },
  }));

  const oldEnv = { ...process.env };
  Object.assign(process.env, {
    OCR_PR_NUMBER: '123',
    OCR_HEAD_SHA: 'abc123',
    OCR_RESULT_PATH: resultPath,
    OCR_METRICS_PATH: metricsPath,
    OCR_MAX_INLINE_COMMENTS: '20',
    OCR_RULES_HASH: 'ruleshash',
    OCR_REVIEWER_VERSION: 'reviewer-v3',
    OCR_ROUTER_VERSION: router.ROUTER_VERSION,
    OCR_MODE: 'medium-lean',
  });

  let postedComment = '';
  let createReviewCalled = false;
  const github = {
    paginate: async () => [],
    rest: {
      issues: {
        listComments: async () => [],
        createComment: async ({ body }) => {
          postedComment = body;
          return { data: {} };
        },
      },
      pulls: {
        listReviews: async () => [],
        createReview: async () => {
          createReviewCalled = true;
        },
      },
    },
  };

  await postOcrReview({
    github,
    context: { repo: { owner: 'lfglabs-dev', repo: 'verity' } },
    core: { notice() {}, warning() {} },
  });

  process.env = oldEnv;
  assert.strictEqual(createReviewCalled, false);
  assert.ok(postedComment.includes('retryable-failure'));
  assert.ok(postedComment.includes('Potential weakened theorem statement.'));
  assert.ok(postedComment.includes('completed_with_errors'));
  const metrics = JSON.parse(fs.readFileSync(metricsPath, 'utf8'));
  assert.strictEqual(metrics.ocr.retryable, true);
  assert.strictEqual(metrics.ocr.comments_count, 1);
  assert.strictEqual(metrics.ocr.total_tokens, 12345);
}

async function run() {
  testNoSupportedFilesSkipped();
  testOneLeanFileNormal();
  testLargeLeanPacketized();
  testLeanCommentDoesNotTriggerSorrySignal();
  testLeanBlockCommentDoesNotTriggerSorrySignal();
  testCodeAfterInlineBlockCommentIsScanned();
  testOversizedLeanGuarded();
  testScoutConfigDefaultsToMiniMaxOnOcrEndpoint();
  testScoutConfigCanDisableLargeLeanScout();
  testScoutJsonParsingHandlesMiniMaxThinkingWrapper();
  await testLargeLeanScoutNotConfiguredFallsBack();
  await testLargeLeanScoutSelectsPackets();
  await testLargeLeanScoutEmptySelectionIsFallback();
  await testLargeLeanScoutMalformedJsonFallsBack();
  await testLargeLeanScoutApiFailureFallsBack();
  testScoutErrorSanitizesApiKeyPhrases();
  testScoutErrorSanitizesStructuredSecrets();
  testScoutErrorSanitizesJwtWithoutDroppingPlainDiagnostics();
  testScoutErrorSanitizesBareCredentialLikeStrings();
  testScoutErrorSanitizesQuotedFallbackDiagnostics();
  testScoutErrorSanitizesFieldValueDiagnostics();
  testScoutErrorSanitizesShortQuotedProviderDiagnostics();
  testScoutErrorSanitizesAdditionalCredentialKeys();
  testScoutErrorPreservesUuidDiagnostics();
  await testLargeLeanScoutNoPacketsStatus();
  testWorkflowDocsEnabled();
  testGenericScriptConfigEnabled();
  await testCompletedWithErrorsRetryablePreservesFindings();
  console.log('OCR routing tests passed');
}

run().catch(err => {
  console.error(err);
  process.exit(1);
});
