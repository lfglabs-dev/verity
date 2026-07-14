'use strict';

const assert = require('assert');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { execFileSync } = require('child_process');

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

function testBaseOnlyLeanChangesDoNotRouteThroughLeanPath() {
  const repo = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-merge-base-routing-'));
  const runGit = args => execFileSync('git', args, { cwd: repo, encoding: 'utf8' });
  const write = (filePath, content) => {
    const fullPath = path.join(repo, filePath);
    fs.mkdirSync(path.dirname(fullPath), { recursive: true });
    fs.writeFileSync(fullPath, content);
  };
  const commit = message => {
    runGit(['add', '.']);
    runGit(['-c', 'user.name=OCR test', '-c', 'user.email=ocr-test@example.invalid', 'commit', '-m', message]);
  };

  runGit(['init', '--initial-branch=main']);
  write('README.md', 'ancestor\n');
  commit('ancestor');
  runGit(['checkout', '-b', 'pr']);
  write('.github/workflows/ocr-review.yml', 'name: OCR config only\n');
  commit('PR workflow change');
  const prHead = runGit(['rev-parse', 'HEAD']).trim();
  runGit(['checkout', 'main']);
  write('Compiler/BaseOnly.lean', 'theorem baseOnly : True := by trivial\n');
  commit('base-only Lean change');
  runGit(['update-ref', 'refs/remotes/origin/main', runGit(['rev-parse', 'HEAD']).trim()]);
  runGit(['checkout', 'pr']);

  const previousCwd = process.cwd();
  try {
    process.chdir(repo);
    const diff = router.loadDiff('origin/main', prHead);
    const decision = router.decideRoute(diff.files);
    assert.strictEqual(diff.files.some(entry => entry.path.endsWith('.lean')), false);
    assert.strictEqual(decision.counts.lean, 0);
    assert.strictEqual(decision.mode, 'config-docs');
  } finally {
    process.chdir(previousCwd);
  }
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

function testLeanBlockCommentStateFromContextDoesNotTriggerSignals() {
  const leanFile = file('Compiler/Proofs/ContextBlockComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextBlockComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', '/-'],
    ['add', 'This explanatory note mentions sorry, axiom, and unsafe in prose.'],
    ['ctx', '-/'],
    ['add', 'theorem still_ok : True := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
  assert.ok(!packets[0].signals.includes('introduced/changed axiom'));
  assert.ok(!packets[0].signals.includes('introduced unsafe'));
}

function testLeanCodeAfterContextBlockCommentIsScanned() {
  const leanFile = file('Compiler/Proofs/ContextBlockCommentCode.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextBlockCommentCode.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', '/-'],
    ['add', 'This explanatory note mentions sorry in prose.'],
    ['ctx', '-/'],
    ['add', 'unsafe def riskyAfterComment : Nat := 0'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
  assert.ok(packets[0].signals.includes('introduced unsafe'));
}

function testLeanStringCommentDelimiterInContextDoesNotHideSignals() {
  const leanFile = file('Compiler/Proofs/StringDelimiterContext.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/StringDelimiterContext.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def marker := "/-"'],
    ['add', 'unsafe def riskyAfterString : Nat := 0'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced unsafe'));
}

function testLeanMultilineStringCommentDelimiterInContextDoesNotHideSignals() {
  const leanFile = file('Compiler/Proofs/MultilineStringDelimiterContext.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineStringDelimiterContext.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def marker := "string starts'],
    ['ctx', '/- not a block comment'],
    ['ctx', 'string ends"'],
    ['add', 'unsafe def riskyAfterMultilineString : Nat := 0'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced unsafe'));
}

function testLeanEscapedIdentifierCommentDelimiterInContextDoesNotHideSignals() {
  const leanFile = file('Compiler/Proofs/EscapedIdentifierDelimiterContext.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/EscapedIdentifierDelimiterContext.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def «/-» : Nat := 0'],
    ['add', 'unsafe def riskyAfterEscapedIdentifier : Nat := 0'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced unsafe'));
}

function testLeanStringLiteralsDoNotTriggerSignals() {
  const leanFile = file('Compiler/Proofs/StringSignalProse.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/StringSignalProse.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := "sorry axiom unsafe"'],
    ['add', 'theorem still_ok : True := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
  assert.ok(!packets[0].signals.includes('introduced/changed axiom'));
  assert.ok(!packets[0].signals.includes('introduced unsafe'));
}

function testLeanInterpolatedStringExpressionsAreScanned() {
  const leanFile = file('Compiler/Proofs/InterpolatedString.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedString.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := s!"value {(by sorry : Nat)}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringQuotedBracesDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringQuotedBrace.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringQuotedBrace.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def exact := s!"{ let c := \'}\'; (by sorry : Nat) }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringNestedQuotedBracesDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringNestedQuotedBrace.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringNestedQuotedBrace.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def nested := s!"{ let text := "}"; (by admit : Nat) }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringBlockCommentBracesDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringBlockCommentBrace.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringBlockCommentBrace.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def commented := s!"{ /- } -/ (by sorry : Nat) }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanMultilineInterpolatedStringExpressionsAreScanned() {
  const leanFile = file('Compiler/Proofs/MultilineInterpolatedString.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineInterpolatedString.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := s!"value'],
    ['add', '{(by sorry : Nat)}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanMultilineOpenInterpolationExpressionsAreScanned() {
  const leanFile = file('Compiler/Proofs/MultilineOpenInterpolation.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineOpenInterpolation.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := s!"value {'],
    ['add', '(by admit : Nat)'],
    ['add', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanMultilineInterpolationQuotedBracesDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/MultilineInterpolationQuotedBrace.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineInterpolationQuotedBrace.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def exact := s!"{'],
    ['add', 'let c := \'}\''],
    ['add', '(by sorry : Nat)'],
    ['add', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanMultilineInterpolationUnicodePrimedIdentifiersDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/MultilineInterpolationUnicodePrimedIdentifier.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineInterpolationUnicodePrimedIdentifier.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := s!"value {'],
    ['add', "let x₁' := 0"],
    ['add', '(by sorry : Nat)'],
    ['add', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationAttributesAddedCode() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolation.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolation.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value {'],
    ['add', '(by sorry : Nat)'],
    ['ctx', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextClosedInterpolationDoesNotAttributeContextCode() {
  const leanFile = file('Compiler/Proofs/ContextClosedInterpolation.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextClosedInterpolation.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value {'],
    ['add', '0'],
    ['ctx', '}"; (by sorry : Nat)'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationDoesNotAttributePriorContextCode() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationPriorCode.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationPriorCode.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value {'],
    ['ctx', '(by sorry : Nat)'],
    ['add', 'let harmless := 0'],
    ['ctx', 'harmless'],
    ['ctx', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationCommentDoesNotAttributeAddedProse() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value { /-'],
    ['add', 'prose mentioning sorry and unsafe'],
    ['ctx', '-/ 0 }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
  assert.ok(!packets[0].signals.includes('introduced unsafe'));
}

function testLeanContextOpenedInterpolationClosingChangeDoesNotAttributePriorCode() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationClosingChange.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationClosingChange.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value {'],
    ['ctx', '(by sorry : Nat)'],
    ['del', '}"'],
    ['add', '}!"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationNestedStringResumesOnAddedLine() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationNestedString.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationNestedString.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value { let s := "'],
    ['add', '"; (by sorry : Nat) }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationNestedCharResumesOnAddedLine() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationNestedChar.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationNestedChar.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value { let c := \''],
    ['add', '\'; (by admit : Nat) }"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationScansCodeAfterClosingString() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationPostStringCode.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationPostStringCode.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note : Nat := let _ := s!"value {'],
    ['add', '0 }"; (by sorry : Nat)'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedInterpolationScansSecondInterpolationInTail() {
  const leanFile = file('Compiler/Proofs/ContextOpenedInterpolationSecondTail.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedInterpolationSecondTail.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note : String := s!"value {'],
    ['add', '0 } and {(by sorry : Nat)}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanContextOpenedNestedInterpolationAttributesAddedCode() {
  const leanFile = file('Compiler/Proofs/ContextOpenedNestedInterpolation.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/ContextOpenedNestedInterpolation.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note : String := s!"outer { s!"inner {'],
    ['add', '(by sorry : Nat)'],
    ['ctx', '}"}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanUnterminatedContextOpenedInterpolationFlushesAddedCode() {
  const leanFile = file('Compiler/Proofs/UnterminatedContextOpenedInterpolation.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/UnterminatedContextOpenedInterpolation.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['ctx', 'def note := s!"value {'],
    ['add', '(by sorry : Nat)'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanMultilineInterpolationLineCommentDoesNotHideNextLine() {
  const leanFile = file('Compiler/Proofs/MultilineInterpolationLineComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/MultilineInterpolationLineComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := s!"value {'],
    ['add', '-- a comment about a proof'],
    ['add', '(by admit : Nat)'],
    ['add', '}"'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringPrimedIdentifiersDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringPrimedIdentifier.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringPrimedIdentifier.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', "def note := s!\"value { let x' := (by sorry : Nat); x' }\""],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringMultiPrimedIdentifiersDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringMultiPrimedIdentifier.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringMultiPrimedIdentifier.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', "def double := s!\"value { let h'' := (by admit : Nat); h'' }\""],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testLeanInterpolatedStringUnicodePrimedIdentifiersDoNotStopScanning() {
  const leanFile = file('Compiler/Proofs/InterpolatedStringUnicodePrimedIdentifier.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/InterpolatedStringUnicodePrimedIdentifier.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', "def note := s!\"value { let x1' := 0; let x₁' := x1'; (by sorry : Nat) }\""],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced sorry/admit'));
}

function testBangBeforeStringDoesNotEnableInterpolationScanning() {
  const leanFile = file('Compiler/Proofs/BangString.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/BangString.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', 'def note := !"literal { not interpolation"'],
    ['add', 'unsafe def riskyAfterBangString : Nat := 0'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('introduced unsafe'));
}

function testLeanNestedBlockCommentDoesNotTriggerSignals() {
  const leanFile = file('Compiler/Proofs/NestedBlockComment.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/NestedBlockComment.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['add', '/- outer /- inner -/ sorry axiom unsafe -/'],
    ['add', 'theorem still_ok : True := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(!packets[0].signals.includes('introduced sorry/admit'));
  assert.ok(!packets[0].signals.includes('introduced/changed axiom'));
  assert.ok(!packets[0].signals.includes('introduced unsafe'));
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

function testTheoremStatementStringLiteralChangesAreDetected() {
  const leanFile = file('Compiler/Proofs/TheoremStringChange.lean', 10, 0);
  leanFile.hunks = [hunk('Compiler/Proofs/TheoremStringChange.lean', 20, [
    ['ctx', 'namespace Verity'],
    ['del', 'theorem render_sound : render x = "old" := by trivial'],
    ['add', 'theorem render_sound : render x = "new" := by trivial'],
    ['ctx', 'end Verity'],
  ])];
  const packets = router.buildReviewPackets([leanFile]);
  assert.ok(packets.length > 0);
  assert.ok(packets[0].signals.includes('theorem statement changed/possibly weakened'));
}

function testLeanScannerBlockerRegressionCases() {
  const cases = [
    {
      name: 'quoted braces inside interpolation expressions',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x := s!"{ let c := \'}\'; (by sorry : Nat) }"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'Lean block comments inside interpolation are ignored and following code is scanned',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x := s!"{ /- prose sorry axiom unsafe } -/ (by admit : Nat) }"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
      excludes: ['introduced/changed axiom', 'introduced unsafe'],
    },
    {
      name: 'theorem statement comparisons preserve changed raw string literal text',
      lines: [
        ['ctx', 'namespace Verity'],
        ['del', 'theorem render_sound : render x = r#"old { sorry }"# := by trivial'],
        ['add', 'theorem render_sound : render x = r#"new { sorry }"# := by trivial'],
        ['ctx', 'end Verity'],
      ],
      includes: ['theorem statement changed/possibly weakened'],
      excludes: ['introduced sorry/admit'],
    },
    {
      name: 'theorem statement comparisons preserve raw strings with inner quotes',
      lines: [
        ['ctx', 'namespace Verity'],
        ['del', 'theorem render_sound : render x = r#"old "quoted" value"# := by trivial'],
        ['add', 'theorem render_sound : render x = r#"new "quoted" value"# := by trivial'],
        ['ctx', 'end Verity'],
      ],
      includes: ['theorem statement changed/possibly weakened'],
    },
    {
      name: 'theorem statement comparisons preserve interpolation braces',
      lines: [
        ['ctx', 'namespace Verity'],
        ['del', 'theorem render_sound : render x = s!"{x}" := by trivial'],
        ['add', 'theorem render_sound : render x = s!"x" := by trivial'],
        ['ctx', 'end Verity'],
      ],
      includes: ['theorem statement changed/possibly weakened'],
      excludes: ['introduced sorry/admit'],
    },
    {
      name: 'code after a raw string with inner quotes is scanned',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def marker := r#"said "hi""#; unsafe def riskyAfterRaw : Nat := 0'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced unsafe'],
    },
    {
      name: 'multiline interrupted interpolation keeps state from context into added line',
      lines: [
        ['ctx', 'namespace Verity'],
        ['ctx', 'def x := s!"prefix {'],
        ['ctx', 'let y := 0'],
        ['add', '(by sorry : Nat)'],
        ['ctx', '}"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'newline after interpolation line comment resumes scanning',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x := s!"{'],
        ['add', '-- comment with } sorry'],
        ['add', '(by admit : Nat)'],
        ['add', '}"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'unterminated interpolation fragments are flushed at hunk end',
      lines: [
        ['ctx', 'namespace Verity'],
        ['ctx', 'def x := s!"{'],
        ['add', '(by sorry : Nat)'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'interpolation block comment state is preserved while flushing added lines',
      lines: [
        ['ctx', 'namespace Verity'],
        ['ctx', 'def x := s!"{ /-'],
        ['add', 'prose sorry axiom unsafe'],
        ['add', '-/ (by admit : Nat)'],
        ['ctx', '}"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
      excludes: ['introduced/changed axiom', 'introduced unsafe'],
    },
    {
      name: 'code after a closed interpolation is scanned',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x : Nat := let _ := s!"{0}"; (by sorry : Nat)'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'subsequent interpolation in added tail is scanned',
      lines: [
        ['ctx', 'namespace Verity'],
        ['ctx', 'def x := s!"{'],
        ['add', '0 } and {(by admit : Nat)}"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'nested interpolated string resumes outer interpolation state',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x := s!"outer { let inner := s!"inner {(0 : Nat)}"; (by sorry : Nat) }"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'escaped identifiers containing comment delimiters do not open comments',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def «/-» := 0'],
        ['add', 'unsafe def riskyAfterEscapedIdent : Nat := 0'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced unsafe'],
    },
    {
      name: 'opening interpolation fragment from added line is buffered through later added line',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', 'def x := s!"prefix {'],
        ['ctx', 'let old := 0'],
        ['add', '(by sorry : Nat)'],
        ['ctx', '}"'],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
    {
      name: 'apostrophe after non-ASCII Lean identifier is not a char literal',
      lines: [
        ['ctx', 'namespace Verity'],
        ['add', "def x := s!\"{ let x₁' := 0; (by sorry : Nat) }\""],
        ['ctx', 'end Verity'],
      ],
      includes: ['introduced sorry/admit'],
    },
  ];

  for (const regression of cases) {
    const leanFile = file(`Compiler/Proofs/${regression.name.replace(/[^A-Za-z0-9]+/g, '')}.lean`, 10, 0);
    leanFile.hunks = [hunk(leanFile.path, 20, regression.lines)];
    const packets = router.buildReviewPackets([leanFile]);
    assert.ok(packets.length > 0, regression.name);
    const signals = packets.flatMap(packet => packet.signals);
    for (const signal of regression.includes || []) {
      assert.ok(signals.includes(signal), `${regression.name}: expected ${signal}; got ${signals.join(', ')}`);
    }
    for (const signal of regression.excludes || []) {
      assert.ok(!signals.includes(signal), `${regression.name}: unexpected ${signal}; got ${signals.join(', ')}`);
    }
  }
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
  // The test token is redacted by the generic high-entropy sanitizer path.
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
    api_token: 'abcdefghijklmnopqrstuvwxyz123461',
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

function testScoutErrorSanitizesPunctuatedBearerCredentials() {
  const detail = router.sanitizeScoutErrorDetail('MiniMax-M3 failed with Bearer abc:def+ghi/jkl~mno');
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('Bearer [redacted]'));
  assert.ok(!detail.includes('abc:def'));
}

function testScoutErrorSanitizesBasicAuthCredentials() {
  const detail = router.sanitizeScoutErrorDetail('MiniMax-M3 failed with Authorization: Basic dXNlcjpwYXNz');
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('Basic [redacted]'));
  assert.ok(!detail.includes('dXNlcjpwYXNz'));
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

function testScoutErrorSanitizesEmbeddedJsonDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    '400 Bad Request: {"api_key":"short-secret","error":"invalid MiniMax-M3 request"}'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesEmbeddedStructuredJsonDiagnostics() {
  const fieldValue = router.sanitizeScoutErrorDetail(
    '400 Bad Request: {"field":"api_key","value":"short-secret","error":"invalid MiniMax-M3 request"}'
  );
  assert.ok(fieldValue.includes('MiniMax-M3'));
  assert.ok(fieldValue.includes('[redacted]'));
  assert.ok(!fieldValue.includes('short-secret'));

  const arrayValue = router.sanitizeScoutErrorDetail(
    '400 Bad Request: [{"api_key":["short-secret"],"error":"invalid MiniMax-M3 request"}]'
  );
  assert.ok(arrayValue.includes('MiniMax-M3'));
  assert.ok(arrayValue.includes('[redacted]'));
  assert.ok(!arrayValue.includes('short-secret'));
}

function testScoutErrorSanitizesLeadingJsonWithTrailingText() {
  const detail = router.sanitizeScoutErrorDetail(
    '{"field":"api_key","value":"short-secret","error":"invalid MiniMax-M3 request"} request rejected'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('request rejected'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesRepeatedEmbeddedJson() {
  const repeated = '{"field":"api_key","value":"short-secret"}';
  const detail = router.sanitizeScoutErrorDetail(`${repeated} and ${repeated}`);
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesMultipleEmbeddedJsonFragments() {
  const detail = router.sanitizeScoutErrorDetail(
    '400 {"error":"bad MiniMax-M3 request"} details {"field":"api_key","value":"short-secret"}'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesJsonEncodedStringFields() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    message: JSON.stringify({ field: 'api_key', value: 'short-secret' }),
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesFieldValueDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    issues: [
      { field: 'api_key', value: 'abcdefghijklmnopqrstuvwxyz123456' },
      { loc: ['body', 'client_secret'], input: 'abcdefghijklmnopqrstuvwxyz123457' },
      { field: 'api_key', input_value: 'abcdefghijklmnopqrstuvwxyz123458' },
      { field: 'api_key', message: 'short-secret' },
    ],
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123456'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123457'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz123458'));
  assert.ok(!detail.includes('short-secret'));
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
    credentials: 'plural-short-secret',
    passphrase: 'another-short-secret',
    authcode: 'auth-short-secret',
    client_id: 'client-short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
  assert.ok(!detail.includes('plural-short-secret'));
}

function testScoutErrorSanitizesTupleArraySecrets() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    headers: [
      ['authorization', 'Bearer short-secret'],
      ['x-api-key', 'another-short-secret'],
    ],
    flat: ['field', 'api_key', 'value', 'flat-short-secret', 'value', 'second-flat-secret'],
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
  assert.ok(!detail.includes('another-short-secret'));
  assert.ok(!detail.includes('flat-short-secret'));
  assert.ok(!detail.includes('second-flat-secret'));
}

function testScoutErrorUsesLiteralJsonReplacement() {
  const detail = router.sanitizeScoutErrorDetail(
    '400 Bad Request: {"field":"api_key","value":"short-secret","error":"MiniMax-M3 $& scout request"}'
  );
  assert.ok(detail.includes('MiniMax-M3 $& scout request'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesPunctuatedUnquotedLabels() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 failed with api_key: key-id:secret and token=abc$defghi and api_secret: abcdefghijklmnopqrstuvwxyz1234567890:tail'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('api_key: [redacted]'));
  assert.ok(detail.includes('token=[redacted]'));
  assert.ok(!detail.includes('key-id:secret'));
  assert.ok(!detail.includes('abc$defghi'));
  assert.ok(!detail.includes('abcdefghijklmnopqrstuvwxyz'));
  assert.ok(!detail.includes(':tail'));
}

function testScoutErrorPreservesUuidDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 trace id 550e8400-e29a-41d4-a716-446655440000 failed'
  );
  assert.ok(detail.includes('550e8400-e29a-41d4-a716-446655440000'));
}

function testScoutErrorSanitizesShortUnquotedDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 failed with token: abc12345 and credentials=short8'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('token: [redacted]'));
  assert.ok(detail.includes('credentials=[redacted]'));
  assert.ok(!detail.includes('abc12345'));
  assert.ok(!detail.includes('short8'));
}

function testScoutErrorSanitizesPrefixedTextLabels() {
  const quoted = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 failed with openai_api_key: "short-secret"'
  );
  assert.ok(quoted.includes('MiniMax-M3'));
  assert.ok(quoted.includes('[redacted]'));
  assert.ok(!quoted.includes('short-secret'));

  const camel = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 failed with openaiApiKey: short8'
  );
  assert.ok(camel.includes('MiniMax-M3'));
  assert.ok(camel.includes('[redacted]'));
  assert.ok(!camel.includes('short8'));
}

function testScoutErrorSanitizesPropertyValueDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    propertyName: 'credentials',
    value: 'short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesDottedSecretKeys() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    'config.apiKey': 'short-secret',
    'openai.api_key': 'another-short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
  assert.ok(!detail.includes('another-short-secret'));
}

function testScoutErrorSanitizesLocationValueDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    location: 'api_key',
    value: 'short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
}

function testScoutErrorSanitizesGenericKeyDiagnostics() {
  const direct = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    key: 'short-secret',
  }));
  assert.ok(direct.includes('MiniMax-M3'));
  assert.ok(direct.includes('[redacted]'));
  assert.ok(!direct.includes('short-secret'));

  const field = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    field: 'key',
    value: 'another-short-secret',
  }));
  assert.ok(field.includes('MiniMax-M3'));
  assert.ok(field.includes('[redacted]'));
  assert.ok(!field.includes('another-short-secret'));
}

function testScoutErrorSanitizesWorkflowKeyDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    OCR_LLM_KEY: 'short-secret',
    OCR_LLM_TOKEN: 'another-short-secret',
    scoutKey: 'third-short-secret',
  }));
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
  assert.ok(!detail.includes('another-short-secret'));
  assert.ok(!detail.includes('third-short-secret'));
}

function testScoutErrorSanitizesWorkflowKeyTextLabels() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 rejected OCR_LLM_KEY=short-secret OCR_LLM_TOKEN="another-short-secret" scoutKey: third-short-secret'
  );
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(detail.includes('[redacted]'));
  assert.ok(!detail.includes('short-secret'));
  assert.ok(!detail.includes('another-short-secret'));
  assert.ok(!detail.includes('third-short-secret'));
}

function testScoutErrorPreservesTraceDiagnostics() {
  const detail = router.sanitizeScoutErrorDetail(
    'MiniMax-M3 request req_abcdefghijklmnopqrstuvwxyz123456 trace_id trace_abcdefghijklmnopqrstuvwxyz123456 failed'
  );
  assert.ok(detail.includes('req_abcdefghijklmnopqrstuvwxyz123456'));
  assert.ok(detail.includes('trace_abcdefghijklmnopqrstuvwxyz123456'));
}

function testScoutErrorBoundsLargeProviderBodies() {
  const detail = router.sanitizeScoutErrorDetail(`MiniMax-M3 ${'x'.repeat(5000)}`);
  assert.ok(detail.length <= 500);
  assert.ok(detail.includes('MiniMax-M3'));
}

function testScoutErrorRedactsLargeStructuredBodiesBeforeBounding() {
  const detail = router.sanitizeScoutErrorDetail(JSON.stringify({
    error: 'invalid MiniMax-M3 scout request',
    padding: 'x'.repeat(3000),
    issues: [
      { field: 'api_key', value: 'short-secret' },
    ],
  }));
  assert.ok(detail.length <= 500);
  assert.ok(detail.includes('MiniMax-M3'));
  assert.ok(!detail.includes('short-secret'));
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

  const workflow = fs.readFileSync(path.join(__dirname, '..', 'workflows', 'ocr-review.yml'), 'utf8');
  assert.ok(workflow.includes('@alibaba-group/open-code-review@1.7.9'));
  assert.ok(workflow.includes('npm install --prefix "$RUNNER_TEMP/ocr-cli"'));
  assert.ok(!workflow.includes('npm install -g @alibaba-group/open-code-review'));
  assert.ok(workflow.includes('prepare-lean-lsp.sh'));
  assert.ok(workflow.includes("steps.route.outputs.has_lean == 'true'"));
  assert.ok(workflow.includes('DIFF_BASE: ${{ steps.route.outputs.diff_base }}'));
  assert.ok(workflow.includes('--from "${DIFF_BASE}"'));
  assert.ok(workflow.includes('Number(context.payload.inputs.pr_number)'));
  assert.ok(workflow.includes('ELAN_HOME: ${{ runner.temp }}/ocr-elan'));
  assert.ok(workflow.includes('lean-lsp-mcp==${LEAN_LSP_MCP_VERSION}'));
  assert.ok(workflow.includes('"lean_diagnostic_messages","lean_file_outline","lean_hover_info"'));
  assert.ok(workflow.includes('LEAN_MCP_DISABLED_TOOLS=lean_run_code,lean_build'));
  assert.ok(workflow.includes('OCR_LLM_TOKEN='));
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

async function testInvalidJsonSkipsRetryableFailureAfterExistingSuccess() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-post-invalid-test-'));
  const resultPath = path.join(dir, 'result.json');
  const metricsPath = path.join(dir, 'metrics.json');
  fs.writeFileSync(resultPath, '{not json');
  fs.writeFileSync(metricsPath, JSON.stringify({ mode: 'large-lean-hotspots' }));

  const oldEnv = { ...process.env };
  Object.assign(process.env, {
    OCR_PR_NUMBER: '123',
    OCR_HEAD_SHA: 'abc123',
    OCR_RESULT_PATH: resultPath,
    OCR_METRICS_PATH: metricsPath,
    OCR_RULES_HASH: 'ruleshash',
    OCR_REVIEWER_VERSION: 'reviewer-v3',
    OCR_ROUTER_VERSION: router.ROUTER_VERSION,
    OCR_MODE: 'large-lean-hotspots',
  });

  const existingSuccessKey = postOcrReview.buildDedupKey({
    commit_id: 'abc123',
    rulesHash: 'ruleshash',
    reviewerVersion: 'reviewer-v3',
    routerVersion: router.ROUTER_VERSION.slice(0, 20),
    mode: 'large-lean-hotspots',
    result: { status: 'packetized_review', summary: { mode: 'large-lean-hotspots' } },
    metrics: {
      mode: 'large-lean-hotspots',
      packet_review: {
        packets_selected: 5,
        packet_budget: 7,
        scout: { enabled: true, status: 'success', model: 'reviewer_scout' },
      },
    },
  });

  let createCommentCalled = false;
  let notice = '';
  const github = {
    paginate: async route => {
      if (route === github.rest.pulls.listReviews) {
        return [{ body: `<!-- paloma-ocr-review:${existingSuccessKey}:success -->\nexisting success` }];
      }
      return [];
    },
    rest: {
      issues: {
        listComments: async () => [],
        createComment: async () => {
          createCommentCalled = true;
          return { data: {} };
        },
      },
      pulls: {
        listReviews: async () => [],
        createReview: async () => {
          throw new Error('createReview should not be called');
        },
      },
    },
  };

  await postOcrReview({
    github,
    context: { repo: { owner: 'lfglabs-dev', repo: 'verity' } },
    core: { notice(message) { notice = message; }, warning() {} },
  });

  process.env = oldEnv;
  assert.strictEqual(createCommentCalled, false);
  assert.ok(notice.includes('skipping invalid JSON failure duplicate'));
}

async function testSuccessfulDuplicateDoesNotRewriteMetrics() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-post-duplicate-test-'));
  const resultPath = path.join(dir, 'result.json');
  const metricsPath = path.join(dir, 'metrics.json');
  fs.writeFileSync(resultPath, JSON.stringify({
    status: 'packetized_review',
    comments: [],
    summary: { mode: 'large-lean-hotspots' },
  }));

  const originalMetrics = {
    mode: 'large-lean-hotspots',
    packet_review: {
      enabled: true,
      packets_selected: 5,
      packet_budget: 7,
      scout: { enabled: true, status: 'success', model: 'reviewer_scout' },
    },
  };
  fs.writeFileSync(metricsPath, JSON.stringify(originalMetrics, null, 2));

  const oldEnv = { ...process.env };
  Object.assign(process.env, {
    OCR_PR_NUMBER: '123',
    OCR_HEAD_SHA: 'abc123',
    OCR_RESULT_PATH: resultPath,
    OCR_METRICS_PATH: metricsPath,
    OCR_RULES_HASH: 'ruleshash',
    OCR_REVIEWER_VERSION: 'reviewer-v3',
    OCR_ROUTER_VERSION: router.ROUTER_VERSION,
    OCR_MODE: 'large-lean-hotspots',
  });

  const existingSuccessKey = postOcrReview.buildDedupKey({
    commit_id: 'abc123',
    rulesHash: 'ruleshash',
    reviewerVersion: 'reviewer-v3',
    routerVersion: router.ROUTER_VERSION.slice(0, 20),
    mode: 'large-lean-hotspots',
    result: { status: 'packetized_review', summary: { mode: 'large-lean-hotspots' } },
    metrics: originalMetrics,
  });

  let createReviewCalled = false;
  const github = {
    paginate: async route => {
      if (route === github.rest.pulls.listReviews) {
        return [{ body: `<!-- paloma-ocr-review:${existingSuccessKey}:success -->\nexisting success` }];
      }
      return [];
    },
    rest: {
      issues: {
        listComments: async () => [],
        createComment: async () => {
          throw new Error('createComment should not be called');
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
  assert.deepStrictEqual(JSON.parse(fs.readFileSync(metricsPath, 'utf8')), originalMetrics);
}

async function testLegacyLargeLeanBaseTagDedupsOnlyMatchingScoutConfig() {
  async function runCase({ currentModel, existingModel }) {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-post-legacy-duplicate-test-'));
    const resultPath = path.join(dir, 'result.json');
    const metricsPath = path.join(dir, 'metrics.json');
    fs.writeFileSync(resultPath, JSON.stringify({
      status: 'packetized_review',
      comments: [],
      summary: { mode: 'large-lean-hotspots' },
    }));
    fs.writeFileSync(metricsPath, JSON.stringify({
      mode: 'large-lean-hotspots',
      packet_review: {
        enabled: true,
        packets_selected: 5,
        packet_budget: 7,
        scout: { enabled: true, status: 'success', model: currentModel },
      },
    }));

    const oldEnv = { ...process.env };
    Object.assign(process.env, {
      OCR_PR_NUMBER: '123',
      OCR_HEAD_SHA: 'abc123',
      OCR_RESULT_PATH: resultPath,
      OCR_METRICS_PATH: metricsPath,
      OCR_RULES_HASH: 'ruleshash',
      OCR_REVIEWER_VERSION: 'reviewer-v3',
      OCR_ROUTER_VERSION: router.ROUTER_VERSION,
      OCR_MODE: 'large-lean-hotspots',
    });

    const legacyBaseKey = [
      'abc123',
      'ruleshash',
      'reviewer-v3',
      router.ROUTER_VERSION.slice(0, 20),
      'large-lean-hotspots',
    ].join(':');
    const legacyBody = [
      `<!-- paloma-ocr-review:${legacyBaseKey}:success -->`,
      '### Packet coverage',
      '- Packet review: enabled; selected 5/7 packet(s)',
      `- Scout: configured; status success; model ${existingModel}`,
    ].join('\n');

    let createReviewCalled = false;
    const github = {
      paginate: async route => {
        if (route === github.rest.pulls.listReviews) return [{ body: legacyBody }];
        return [];
      },
      rest: {
        issues: {
          listComments: async () => [],
          createComment: async () => {
            throw new Error('createComment should not be called');
          },
        },
        pulls: {
          listReviews: async () => [],
          createReview: async () => {
            createReviewCalled = true;
            return { data: {} };
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
    return createReviewCalled;
  }

  assert.strictEqual(await runCase({ currentModel: 'reviewer_scout', existingModel: 'reviewer_scout' }), false);
  assert.strictEqual(await runCase({ currentModel: 'reviewer_scout', existingModel: 'MiniMax-M3' }), true);
  assert.strictEqual(await runCase({ currentModel: 'gpt-4', existingModel: 'gpt-4o' }), true);
}

function testScoutProviderErrorsNeutralizeMentions() {
  const body = postOcrReview.buildReviewBody({
    tag: '<!-- test -->',
    result: { status: 'packetized_review', comments: [], summary: { mode: 'large-lean-hotspots' } },
    comments: [],
    selected: [],
    overflow: [],
    summaryOnly: [],
    warnings: [],
    stderr: '',
    metrics: {
      mode: 'large-lean-hotspots',
      router_version: router.ROUTER_VERSION,
      packet_review: {
        enabled: true,
        packets_selected: 0,
        packet_budget: 8,
        scout: {
          enabled: true,
          status: 'fallback_deterministic',
          model: 'MiniMax-M3',
          error_detail: 'provider echoed @verity-admins and @octocat',
        },
      },
    },
  });
  assert.ok(body.includes('&#64;verity-admins'));
  assert.ok(body.includes('&#64;octocat'));
  assert.ok(!body.includes('@verity-admins'));
  assert.ok(!body.includes('@octocat'));
}

function testLargeLeanScoutDedupVariesBySanitizedScoutConfig() {
  const base = {
    commit_id: 'abc123',
    rulesHash: 'ruleshash',
    reviewerVersion: 'reviewer-v3',
    routerVersion: router.ROUTER_VERSION,
    mode: 'large-lean-hotspots',
    result: { status: 'packetized_review', summary: { mode: 'large-lean-hotspots' } },
  };
  const metricsFor = (model, packetIds = []) => ({
    mode: 'large-lean-hotspots',
    packet_review: {
      enabled: true,
      packets_selected: 5,
      packet_budget: 7,
      packets: packetIds.map(packet_id => ({ packet_id })),
      scout: {
        enabled: true,
        status: 'success',
        model,
      },
    },
  });

  const minimaxKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor('MiniMax-M3') });
  const reviewerScoutKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor('reviewer_scout') });
  assert.notStrictEqual(minimaxKey, reviewerScoutKey);
  assert.ok(minimaxKey.includes('scout-v1:enabled:model-MiniMax-M3:status-success:packets-5-of-7:ids-none'));
  assert.ok(reviewerScoutKey.includes('scout-v1:enabled:model-reviewer_scout:status-success:packets-5-of-7:ids-none'));

  const packetSetAKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor('reviewer_scout', ['lean-1', 'lean-2']) });
  const packetSetBKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor('reviewer_scout', ['lean-1', 'lean-3']) });
  assert.notStrictEqual(packetSetAKey, packetSetBKey);
  assert.ok(packetSetAKey.includes(':ids-'));
  assert.ok(!packetSetAKey.includes('lean-1'));

  const unsafeModel = 'https://sandboxed.example/v1?api_key=abcdefghijklmnopqrstuvwxyz123456';
  const unsafeKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor(unsafeModel) });
  assert.ok(unsafeKey.includes('model-redacted-'));
  assert.ok(!unsafeKey.includes('sandboxed.example'));
  assert.ok(!unsafeKey.includes('abcdefghijklmnopqrstuvwxyz123456'));

  const shortTokenKey = postOcrReview.buildDedupKey({ ...base, metrics: metricsFor('abcdefghijklmnop') });
  assert.ok(shortTokenKey.includes('model-redacted-'));
  assert.ok(!shortTokenKey.includes('abcdefghijklmnop'));

  const normalKey = postOcrReview.buildDedupKey({
    ...base,
    mode: 'small-lean',
    result: { status: 'success', summary: { mode: 'small-lean' } },
    metrics: { mode: 'small-lean', packet_review: { scout: { model: 'reviewer_scout' } } },
  });
  assert.strictEqual(normalKey, `${base.commit_id}:${base.rulesHash}:${base.reviewerVersion}:${base.routerVersion}:small-lean`);
}

async function run() {
  testNoSupportedFilesSkipped();
  testOneLeanFileNormal();
  testBaseOnlyLeanChangesDoNotRouteThroughLeanPath();
  testLargeLeanPacketized();
  testLeanCommentDoesNotTriggerSorrySignal();
  testLeanBlockCommentDoesNotTriggerSorrySignal();
  testLeanBlockCommentStateFromContextDoesNotTriggerSignals();
  testLeanCodeAfterContextBlockCommentIsScanned();
  testLeanStringCommentDelimiterInContextDoesNotHideSignals();
  testLeanMultilineStringCommentDelimiterInContextDoesNotHideSignals();
  testLeanEscapedIdentifierCommentDelimiterInContextDoesNotHideSignals();
  testLeanStringLiteralsDoNotTriggerSignals();
  testLeanInterpolatedStringExpressionsAreScanned();
  testLeanInterpolatedStringQuotedBracesDoNotStopScanning();
  testLeanInterpolatedStringNestedQuotedBracesDoNotStopScanning();
  testLeanInterpolatedStringBlockCommentBracesDoNotStopScanning();
  testLeanMultilineInterpolatedStringExpressionsAreScanned();
  testLeanMultilineOpenInterpolationExpressionsAreScanned();
  testLeanMultilineInterpolationQuotedBracesDoNotStopScanning();
  testLeanMultilineInterpolationUnicodePrimedIdentifiersDoNotStopScanning();
  testLeanContextOpenedInterpolationAttributesAddedCode();
  testLeanContextClosedInterpolationDoesNotAttributeContextCode();
  testLeanContextOpenedInterpolationDoesNotAttributePriorContextCode();
  testLeanContextOpenedInterpolationCommentDoesNotAttributeAddedProse();
  testLeanContextOpenedInterpolationClosingChangeDoesNotAttributePriorCode();
  testLeanContextOpenedInterpolationNestedStringResumesOnAddedLine();
  testLeanContextOpenedInterpolationNestedCharResumesOnAddedLine();
  testLeanContextOpenedInterpolationScansCodeAfterClosingString();
  testLeanContextOpenedInterpolationScansSecondInterpolationInTail();
  testLeanContextOpenedNestedInterpolationAttributesAddedCode();
  testLeanUnterminatedContextOpenedInterpolationFlushesAddedCode();
  testLeanMultilineInterpolationLineCommentDoesNotHideNextLine();
  testLeanInterpolatedStringPrimedIdentifiersDoNotStopScanning();
  testLeanInterpolatedStringMultiPrimedIdentifiersDoNotStopScanning();
  testLeanInterpolatedStringUnicodePrimedIdentifiersDoNotStopScanning();
  testBangBeforeStringDoesNotEnableInterpolationScanning();
  testLeanNestedBlockCommentDoesNotTriggerSignals();
  testCodeAfterInlineBlockCommentIsScanned();
  testTheoremStatementStringLiteralChangesAreDetected();
  testLeanScannerBlockerRegressionCases();
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
  testScoutErrorSanitizesPunctuatedBearerCredentials();
  testScoutErrorSanitizesBasicAuthCredentials();
  testScoutErrorSanitizesBareCredentialLikeStrings();
  testScoutErrorSanitizesQuotedFallbackDiagnostics();
  testScoutErrorSanitizesEmbeddedJsonDiagnostics();
  testScoutErrorSanitizesEmbeddedStructuredJsonDiagnostics();
  testScoutErrorSanitizesLeadingJsonWithTrailingText();
  testScoutErrorSanitizesRepeatedEmbeddedJson();
  testScoutErrorSanitizesMultipleEmbeddedJsonFragments();
  testScoutErrorSanitizesJsonEncodedStringFields();
  testScoutErrorSanitizesFieldValueDiagnostics();
  testScoutErrorSanitizesShortQuotedProviderDiagnostics();
  testScoutErrorSanitizesAdditionalCredentialKeys();
  testScoutErrorSanitizesTupleArraySecrets();
  testScoutErrorUsesLiteralJsonReplacement();
  testScoutErrorSanitizesPunctuatedUnquotedLabels();
  testScoutErrorPreservesUuidDiagnostics();
  testScoutErrorSanitizesShortUnquotedDiagnostics();
  testScoutErrorSanitizesPrefixedTextLabels();
  testScoutErrorSanitizesPropertyValueDiagnostics();
  testScoutErrorSanitizesDottedSecretKeys();
  testScoutErrorSanitizesLocationValueDiagnostics();
  testScoutErrorSanitizesGenericKeyDiagnostics();
  testScoutErrorSanitizesWorkflowKeyDiagnostics();
  testScoutErrorSanitizesWorkflowKeyTextLabels();
  testScoutErrorPreservesTraceDiagnostics();
  testScoutErrorBoundsLargeProviderBodies();
  testScoutErrorRedactsLargeStructuredBodiesBeforeBounding();
  await testLargeLeanScoutNoPacketsStatus();
  testWorkflowDocsEnabled();
  testGenericScriptConfigEnabled();
  await testCompletedWithErrorsRetryablePreservesFindings();
  await testInvalidJsonSkipsRetryableFailureAfterExistingSuccess();
  await testSuccessfulDuplicateDoesNotRewriteMetrics();
  await testLegacyLargeLeanBaseTagDedupsOnlyMatchingScoutConfig();
  testScoutProviderErrorsNeutralizeMentions();
  testLargeLeanScoutDedupVariesBySanitizedScoutConfig();
  console.log('OCR routing tests passed');
}

run().catch(err => {
  console.error(err);
  process.exit(1);
});
