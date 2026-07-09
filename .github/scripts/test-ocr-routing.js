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
  assert.strictEqual(decision.scout.strong_review_status, 'blocked_packet_input');
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
  testOversizedLeanGuarded();
  await testLargeLeanScoutNotConfiguredFallsBack();
  await testLargeLeanScoutSelectsPackets();
  testWorkflowDocsEnabled();
  testGenericScriptConfigEnabled();
  await testCompletedWithErrorsRetryablePreservesFindings();
  console.log('OCR routing tests passed');
}

run().catch(err => {
  console.error(err);
  process.exit(1);
});
