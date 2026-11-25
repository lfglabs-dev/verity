"""Memory-call mutants in isolated source/cache snapshots: inline-assembly `call` /
`staticcall` over memory, typed external calls without return values and the `ecrecover`
builtin, which share the closed memory-call transport, the Yul `calldataload` split of a
`bytes calldata` signature in front of it, and post-CALL state-access admission and
re-entrant callback commit semantics.

Each runtime mutant must survive an unmodified positive control of its A/B/C campaign and then
produce a divergence with a reproduced deletion-minimal witness. An admission-guard mutant must
turn a pinned located rejection (or positive/classifier check) into a failure of that exact
check. A mutant that fails to build is invalid, never detected.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import release, snapshot

IMPORT = 'Compiler/SolidityImport/Import.lean'
TRANSPORT = 'Compiler/SolidityImport/TransportBarriers.lean'
DENOTE = 'Verity/Core/Model/Denote.lean'
ECM = 'Verity/Core/Model/ECM.lean'
PRECOMPILE = 'Compiler/SolidityImport/PrecompileResponderMocks.lean'
REENTRANT_MOCK = 'Compiler/SolidityImport/ReentrantCallResponderMocks.lean'
YUL = ('solidity_differential.check_yul_memory_call', '--transactions', '64', '--seed', '2531',
       'Contracts.SolidityImportSmoke.YulMemoryCallSequenceModel')
VOID = ('solidity_differential.check_interface_void_call', '--transactions', '160', '--seed', '4219',
        'Contracts.SolidityImportSmoke.InterfaceVoidCallSequenceModel')
ECRECOVER = ('solidity_differential.check_ecrecover', '--transactions', '200', '--seed', '2698',
             'Contracts.SolidityImportSmoke.EcrecoverSequenceModel')
SIGNATURE = ('solidity_differential.check_signature_calldata', '--transactions', '200', '--seed', '2920',
             'Contracts.SolidityImportSmoke.SignatureCalldataSequenceModel')
REENTRANT_WRITE = ('solidity_differential.check_reentrant_callback', '--only', 'SyntheticPostCallWrite',
                   '--transactions', '64', '--seed', '2911',
                   'Contracts.SolidityImportSmoke.PostCallWriteSequenceModel')


def rejection_case(case):
    """An admission-guard mutant's campaign: the pinned located rejection `case` of
    `check_signature_calldata_rejections.py` must pass unmodified and fail mutated."""
    return ('rejection', 'solidity_differential.check_signature_calldata_rejections', case)


def positive_case(module, case, expected_diagnostic):
    """A positive-control admission mutant: `case` must elaborate unmodified and fail with
    `expected_diagnostic` when mutated."""
    return ('positive_control', module, case, expected_diagnostic)


def guard_check_case(lean_file, expected_expr):
    """A Lean `#guard` classifier check: `lean_file` must elaborate unmodified and fail on a
    `#guard` assertion mentioning `expected_expr` when mutated."""
    return ('guard_check', lean_file, expected_expr)


# name: (file, anchor, replacement, campaign)
MUTANTS = {
    # A `call` lowered as a `staticcall`: the responders' fallback writes storage, so it fails.
    # (The opposite mutation makes the view root write state, which compilation rejects.)
    'import-yul-call-kind': (IMPORT,
        'return { pre := #[.ecm (Compiler.ECM.YulMemoryCall.module isStatic result) xs.toList],',
        'return { pre := #[.ecm (Compiler.ECM.YulMemoryCall.module true result) xs.toList],', YUL),
    'import-yul-returndata-bubble': (IMPORT,
        'out := out.push .revertReturndata', 'out := out.push .revertEmpty', YUL),
    'denote-yul-call-copy-length': (DENOTE,
        'let copied := Nat.min outSize observed.returndata.length',
        'let copied := Nat.min outSize (observed.returndata.length - 1)', YUL),
    # An empty range at an offset past the range limit expands no memory on the EVM.
    'denote-yul-call-empty-range': (DENOTE,
        'if (inSize != 0 && yulMemoryCallRangeLimit < inOffset + inSize) ||',
        'if (yulMemoryCallRangeLimit < inOffset + inSize) ||', YUL),
    # Post-CALL committed world in Denote and in the re-entrant callback responder.
    'denote-yul-call-commit-world': (DENOTE,
        'let world := observed.world.copyPhysicalMemory (rawPhysicalByte observed.returndata)\n'
        '    outOffset 0 copied',
        'let world := state.world.copyPhysicalMemory (rawPhysicalByte observed.returndata)\n'
        '    outOffset 0 copied',
        REENTRANT_WRITE),
    'reentrant-callback-commit-world': (REENTRANT_MOCK,
        'else .success (commitCallback counted result.world) [] touched',
        'else .success counted [] touched', REENTRANT_WRITE),
    'ecm-yul-call-value': (ECM,
        'YulExpr.call "call" [gas, target, .lit 0, inOffset, inSize, outOffset, outSize]',
        'YulExpr.call "call" [gas, target, .lit 1, inOffset, inSize, outOffset, outSize]', YUL),
    'import-void-call-code-check': (IMPORT,
        '.ite (.eq (.localVar codeSize) (.literal 0)) [.revertEmpty] [],',
        '.ite (.eq (.localVar codeSize) (.literal 0)) [] [],', VOID),
    'import-void-call-forward': (IMPORT,
        '.ite (.eq (.localVar success) (.literal 0)) [.revertReturndata] [])',
        '.ite (.eq (.localVar success) (.literal 0)) [.revertEmpty] [])', VOID),
    # `try` runs the success clause on a successful call and the catch clause on a failed one.
    'import-try-call-clauses': (IMPORT,
        'return some ({ pre, expr := .localVar success }, yesStmts, noStmts)',
        'return some ({ pre, expr := .localVar success }, noStmts, yesStmts)', VOID),
    'import-void-call-selector': (IMPORT,
        '.mstore (.localVar callBase) (.literal selector),',
        '.mstore (.localVar callBase) (.literal (selector + 1)),', VOID),
    'import-void-call-calldata-start': (IMPORT,
        '.letVar dataPtr (.add (.localVar callBase) (.literal 28)),',
        '.letVar dataPtr (.add (.localVar callBase) (.literal 27)),', VOID),
    'import-void-call-calldata-size': (IMPORT,
        '.letVar dataSize (.add payloadSize (.literal 4))]',
        '.letVar dataSize (.add payloadSize (.literal 3))]', VOID),
    # `ecrecover`: the ABI words (hash, v, r, s) in order, and the 160-bit result mask.
    'import-ecrecover-word-order': (IMPORT,
        'pre := pre.push (.mstore (.add (.localVar ptr) (.literal (32 * index))) word)',
        'pre := pre.push (.mstore (.add (.localVar ptr) (.literal (32 * (3 - index)))) word)',
        ECRECOVER),
    # A plain local argument left unbound is read after a later argument reassigns it.
    'import-ecrecover-argument-copy': (IMPORT,
        'pre := pre ++ converted.pre.push (.letVar word value)\n    words := words.push (.localVar word)',
        'pre := pre ++ converted.pre\n    words := words.push value', ECRECOVER),
    # A dirty `uint8` word (assigned in inline assembly) reaches the precompile uncleaned.
    'import-ecrecover-v-cleanup': (IMPORT,
        'let value := if paramTy == "uint8" then .bitAnd converted.expr (.literal 255)',
        'let value := if paramTy == "uint8x" then .bitAnd converted.expr (.literal 255)', ECRECOVER),
    'import-ecrecover-address-mask': (IMPORT,
        '.letVar result (.bitAnd (.mload (.literal 0)) (.literal (2 ^ 160 - 1)))]',
        '.letVar result (.bitAnd (.mload (.literal 0)) (.literal (2 ^ 159 - 1)))]', ECRECOVER),
    # The harness precompile program: high `s` is accepted, `v` selects the parity of `y`.
    'mock-ecrecover-high-s': (PRECOMPILE,
        'unless (v == 27 || v == 28) && 0 < r && r < n && 0 < s && s < n do none',
        'unless (v == 27 || v == 28) && 0 < r && r < n && 0 < s && s ≤ n / 2 do none', ECRECOVER),
    'mock-ecrecover-parity': (PRECOMPILE,
        'let y := if beta % 2 == v - 27 then beta else p - beta',
        'let y := if beta % 2 != v - 27 then beta else p - beta', ECRECOVER),
    # Yul `calldataload` over a root `bytes calldata` parameter (#2920): the `add` literal is
    # dropped (r, s and v all read the first word), or the offset is the head word, not the
    # payload start.
    'import-calldataload-offset-literal': (IMPORT,
        'return some (.add base (.literal k))', 'return some base', SIGNATURE),
    'import-calldataload-offset-binding': (IMPORT,
        'e.yulNames.insert (yulCalldataOffsetKey src) (.localVar cb.dataBinding)',
        'e.yulNames.insert (yulCalldataOffsetKey src) (.localVar cb.headerBinding)', SIGNATURE),
    # Admission guards: a calldata slice's payload offset and a literal at or above 2^64.
    'import-calldataload-root-guard': (IMPORT,
        '!cb.inMemory && cb.offsetBinding != "" && cb.dataBinding != "" then',
        '!cb.inMemory && cb.dataBinding != "" then', rejection_case('slice-argument')),
    'import-calldataload-literal-bound': (IMPORT,
        'unless k < 2^64 do return none', 'unless k < 2^256 do return none',
        rejection_case('wide-literal')),
    # Post-CALL transport-barrier classifiers (`TransportBarriers.lean`):
    # 1. Dropping closed-CALL erasure in `eraseClosedInteractions` causes `write-after-call` to
    #    hit the located defense-in-depth rejection at `Import.lean`.
    'transport-erase-closed-interactions': (TRANSPORT,
        'if isClosedLowLevelCall mod then .letVar (mod.resultVars.headD "") (.literal 0)',
        'if false then .letVar (mod.resultVars.headD "") (.literal 0)',
        positive_case('solidity_differential.check_reentrant_callback_rejections',
                      'write-after-call',
                      'storage reads, storage writes and logs after an external CALL are '
                      'supported only when every external interaction of the function is a '
                      'closed transport')),
    # 2. Dropping the CEI-after-erasure conjunct in `onlyClosedCallStateWindows` causes the
    #    classifier `#guard` on `[closedCall, .internalCall "helper" [], write]` to fail.
    'transport-only-closed-call-state-windows': (TRANSPORT,
        '(Compiler.CompilationModel.stmtListCEIViolation erased false).isNone &&',
        'true &&',
        guard_check_case('Contracts/SolidityImportSmoke/PostCallStateAccessChecks.lean',
                         '!onlyClosedCallStateWindows')),
}
MODULES = ['Compiler.SolidityImport.Import', 'Compiler.SolidityImport.Differential',
           'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.CallResponderMocks',
           'Compiler.SolidityImport.ReentrantCallResponderMocks',
           'Compiler.Codegen', 'Compiler.Yul.PrettyPrint']


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, campaign, output):
    module, *options, _ = campaign
    argv = [sys.executable, '-m', module, *options, '--shrink-attempts', '40', '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'no differential report; tool failure is not detection: {output.with_suffix(".log")}')
    return result.returncode, json.loads(report_path.read_text())


def rejection(directory, campaign, output):
    module, case = campaign[1], campaign[2]
    argv = [sys.executable, '-m', module, '--only', case, '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=1800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    return result.returncode, result.stdout + result.stderr


def guard_check(directory, campaign, output):
    lean_file = campaign[1]
    artifact = output.with_suffix('.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['lake', 'env', 'lean', lean_file, '-o', str(artifact)],
                            cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=1800)
    log = result.stdout + result.stderr
    output.with_suffix('.log').write_text(log)
    return result.returncode, log


def mutation_campaign(output, selected=None):
    root = Path.cwd()
    for name in selected or MUTANTS:
        relative, before, _, _ = MUTANTS[name]
        if (root / relative).read_text().count(before) != 1:
            raise HarnessError(f'{name}: mutation anchor must occur exactly once in {relative}')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        relative, before, after, campaign = MUTANTS[name]
        kind = campaign[0] if campaign[0] in ('rejection', 'positive_control', 'guard_check') else 'runtime'
        modules = MODULES if kind != 'runtime' else [*MODULES, campaign[-1]]
        directory = output / name
        snapshot(directory)
        try:
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'baseline-build.log')
            if kind in ('rejection', 'positive_control'):
                code, log = rejection(directory, campaign, directory / '.lake/baseline-rejection')
                if code:
                    raise HarnessError(f'{name}: unmodified admission check failed\n{log[-2000:]}')
            elif kind == 'guard_check':
                code, log = guard_check(directory, campaign, directory / '.lake/baseline-guard')
                if code:
                    raise HarnessError(f'{name}: unmodified classifier guard failed\n{log[-2000:]}')
            else:
                code, baseline = runtime(directory, campaign, directory / '.lake/baseline')
                if code or baseline['divergences'] or not baseline['transactions']:
                    raise HarnessError(f'{name}: unmodified positive control failed')
            source = directory / relative
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError(f'{name}: nonunique mutation anchor')
            source.write_text(text.replace(before, after))
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'build.log')
            if kind == 'rejection':
                case = campaign[2]
                code, log = rejection(directory, campaign, directory / '.lake/mutated-rejection')
                if code == 0 or f'{case}: expected exact located rejection' not in log:
                    raise HarnessError(f'{name}: guard removal escaped the {case} near-miss check')
                entry = {'kind': 'unsupported-admission', 'case': case}
            elif kind == 'positive_control':
                case, expected_diagnostic = campaign[2], campaign[3]
                code, log = rejection(directory, campaign, directory / '.lake/mutated-rejection')
                if code == 0 or f'{case}: positive control failed' not in log or expected_diagnostic not in log:
                    raise HarnessError(f'{name}: positive control {case} did not fail with expected diagnostic')
                entry = {'kind': 'positive-control-rejection', 'case': case}
            elif kind == 'guard_check':
                expected_expr = campaign[2]
                code, log = guard_check(directory, campaign, directory / '.lake/mutated-guard')
                if code == 0 or 'did not evaluate to `true`' not in log or expected_expr not in log:
                    raise HarnessError(f'{name}: classifier guard did not detect mutation\n{log[-2000:]}')
                entry = {'kind': 'classifier-guard', 'file': campaign[1]}
            else:
                mutated = directory / '.lake/mutated'
                code, report = runtime(directory, campaign, mutated)
                if code == 0 or not report['divergences']:
                    raise HarnessError(f'{name}: mutation survived')
                reduced = json.loads((mutated / 'reduced.json').read_text())
                if not reduced['deletion_minimal'] or not reduced['transactions'] or not reduced['signature']:
                    raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
                entry = {'witness': reduced, 'campaign': str(mutated)}
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True, 'baselinePassed': True,
                        'path': relative, **entry})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', nargs='*')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    selected = None
    if args.only:
        selected = [name for name in MUTANTS if name in args.only]
        if len(selected) != len(set(args.only)):
            raise HarnessError(f'unknown mutants in --only {args.only}')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='memory-call-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
