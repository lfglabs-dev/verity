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
  };
}

function testNoSupportedFilesSkipped() {
  const decision = router.decideRoute([
    file('packages/cache.lock', 3, 1),
    file('build/generated.out', 5, 0),
  ]);
  assert.strictEqual(decision.mode, 'skipped');
  assert.strictEqual(decision.shouldRunOcr, false);
}

function testOneLeanFileNormal() {
  const decision = router.decideRoute([
    file('Compiler/Proofs/IRGeneration/Small.lean', 120, 20),
  ]);
  assert.strictEqual(decision.mode, 'normal');
  assert.strictEqual(decision.shouldRunOcr, true);
  assert.strictEqual(decision.ocr.concurrency, 3);
}

function testLargeLeanGuarded() {
  const decision = router.decideRoute([
    file('Compiler/Proofs/A.lean', 40, 0),
    file('Compiler/Proofs/B.lean', 40, 0),
    file('Compiler/Proofs/C.lean', 40, 0),
  ]);
  assert.strictEqual(decision.mode, 'guarded-large-lean');
  assert.strictEqual(decision.shouldRunOcr, false);
}

function testWorkflowDocsEnabled() {
  const decision = router.decideRoute([
    file('.github/workflows/ocr-review.yml', 80, 10),
    file('docs/ocr.md', 900, 4),
  ]);
  assert.strictEqual(decision.mode, 'normal');
  assert.strictEqual(decision.shouldRunOcr, true);
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
    mode: 'bounded-lean',
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
    OCR_MODE: 'bounded-lean',
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
  testLargeLeanGuarded();
  testWorkflowDocsEnabled();
  await testCompletedWithErrorsRetryablePreservesFindings();
  console.log('OCR routing tests passed');
}

run().catch(err => {
  console.error(err);
  process.exit(1);
});
