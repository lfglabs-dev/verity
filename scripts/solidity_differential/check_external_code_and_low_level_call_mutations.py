"""Code-length and optional-bool low-level call mutants in isolated source/cache snapshots.

Runtime mutants must survive an unmodified positive control and then produce an
A/B/C divergence with a reproduced deletion-minimal witness. Admission-guard
mutants must turn a pinned located rejection into a failure of the exact
near-miss check. A mutant that fails to build is invalid, never detected.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import release, snapshot

IMPORT = 'Compiler/SolidityImport/Import.lean'
DENOTE = 'Verity/Core/Model/Denote.lean'
ECM = 'Verity/Core/Model/ECM.lean'
# name: (file, anchor, replacement, kind, rejection case)
MUTANTS = {
    'import-low-level-call-selector': (IMPORT,
        '(Compiler.ECM.SolidityLowLevelCall.optionalBoolModule result selector words.size)',
        '(Compiler.ECM.SolidityLowLevelCall.optionalBoolModule result (selector + 1) words.size)',
        'runtime', None),
    'import-low-level-call-argument-order': (IMPORT,
        '    (target.expr :: words.toList)\n',
        '    (target.expr :: words.toList.reverse)\n', 'runtime', None),
    'import-low-level-call-result-check': (IMPORT,
        'lowerRequireWith validation fun _ => pure { pre := #[], expr := .localVar result }',
        'lowerRequireWith validation fun _ => pure { pre := #[], expr := .literal 1 }',
        'runtime', None),
    'import-code-length-target': (IMPORT,
        'Stmt.ecm (Compiler.ECM.SolidityExtCodeSize.module result) [target.expr]',
        'Stmt.ecm (Compiler.ECM.SolidityExtCodeSize.module result) [.caller]', 'runtime', None),
    'denote-low-level-call-forward': (DENOTE,
        '| .forward data => return (.revertWithData data, observed.touched)',
        '| .forward data => return (.revertWithData [], observed.touched)', 'runtime', None),
    'denote-low-level-call-empty': (DENOTE,
        'else if data.isEmpty then .decoded 1',
        'else if data.isEmpty then .decoded 0', 'runtime', None),
    'denote-low-level-call-short': (DENOTE,
        'else if data.length < 32 then .malformed',
        'else if data.length < 31 then .malformed', 'runtime', None),
    'denote-low-level-call-commit': (DENOTE,
        'let allocated := observed.world.writePhysicalMemoryValue 64',
        'let allocated := prepared.world.writePhysicalMemoryValue 64', 'runtime', None),
    'denote-code-length': (DENOTE,
        'let size := DenoteExternalCode.extCodeSize state.world (Verity.Core.Address.ofNat target)',
        'let size := DenoteExternalCode.extCodeSize state.world (Verity.Core.Address.ofNat target) + 1',
        'runtime', None),
    'ecm-low-level-call-value': (ECM,
        '.call "gas" [], target, .lit 0, ptr, .lit dataSize, .lit 0, .lit 0]',
        '.call "gas" [], target, .lit 1, ptr, .lit dataSize, .lit 0, .lit 0]', 'runtime', None),
    'import-low-level-call-options-guard': (IMPORT,
        'let callee ← mField init "expression"\n  if (← mKind callee) == "FunctionCallOptions" then',
        'let callee ← mField init "expression"\n  if false then', 'admission', 'call-value'),
    'import-low-level-call-forward-guard': (IMPORT,
        'unless ← isReturndataForwarding forward successId dataId dataName do',
        'unless true do', 'admission', 'truncated-forward'),
    'import-low-level-call-validation-guard': (IMPORT,
        'unless ← isOptionalBoolValidation validation dataId do',
        'unless true do', 'admission', 'strict-bool-validation'),
    'import-low-level-call-reuse-guard': (IMPORT,
        'if jsonMentionsDecl later successId || jsonMentionsDecl later dataId then',
        'if false then', 'admission', 'returndata-reuse'),
    'import-code-length-this-guard': (IMPORT,
        'if ← isThisAddressConv account then\n    failAt code',
        'if false then\n    failAt code', 'admission', 'this-code-length'),
}


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_external_code_and_low_level_call',
            '--single', '--transactions', '64', '--seed', '2527', '--shrink-attempts', '40',
            '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'no differential report; tool failure is not detection: {output.with_suffix(".log")}')
    return result.returncode, json.loads(report_path.read_text())


def rejection(directory, case, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_external_code_and_low_level_call_rejections',
            '--only', case, '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=1800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    return result.returncode, result.stdout + result.stderr


def mutation_campaign(output, selected=None):
    root = Path.cwd()
    for name in selected or MUTANTS:
        relative, before, _, _, _ = MUTANTS[name]
        if (root / relative).read_text().count(before) != 1:
            raise HarnessError(f'{name}: mutation anchor must occur exactly once in {relative}')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        relative, before, after, kind, case = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        try:
            modules = ['Compiler.SolidityImport.Import', 'Compiler.SolidityImport.Differential',
                       'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.CallResponderMocks',
                       'Compiler.Codegen', 'Compiler.Yul.PrettyPrint']
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'baseline-build.log')
            if kind == 'runtime':
                code, baseline = runtime(directory, directory / '.lake/baseline')
                if code or baseline['divergences'] or not baseline['transactions']:
                    raise HarnessError(f'{name}: unmodified positive control failed')
            else:
                code, log = rejection(directory, case, directory / '.lake/baseline-rejection')
                if code:
                    raise HarnessError(f'{name}: unmodified located rejection failed\n{log[-2000:]}')
            source = directory / relative
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError(f'{name}: nonunique mutation anchor')
            source.write_text(text.replace(before, after))
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'build.log')
            if kind == 'runtime':
                campaign = directory / '.lake/mutated'
                code, report = runtime(directory, campaign)
                if code == 0 or not report['divergences']:
                    raise HarnessError(f'{name}: mutation survived')
                reduced = json.loads((campaign / 'reduced.json').read_text())
                if not reduced['deletion_minimal'] or not reduced['transactions'] or not reduced['signature']:
                    raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
                entry = {'witness': reduced, 'campaign': str(campaign)}
            else:
                code, log = rejection(directory, case, directory / '.lake/mutated-rejection')
                if code == 0 or f'{case}: expected exact located rejection' not in log:
                    raise HarnessError(f'{name}: guard removal escaped the {case} near-miss check')
                entry = {'kind': 'unsupported-admission', 'case': case}
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True,
                        'baselinePassed': True, 'path': relative, **entry})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    selected = None
    if args.only:
        selected = [name for name in MUTANTS if args.only == name]
        if not selected:
            raise HarnessError(f'no mutants matched --only {args.only}')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='external-code-low-level-call-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
