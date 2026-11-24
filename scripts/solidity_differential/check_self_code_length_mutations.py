"""`address(this).code.length` zero-test mutants in isolated source/cache snapshots.

Runtime mutants must survive an unmodified positive control and then make the
runtime or construction A/B/C replay diverge. Admission-guard mutants must turn a
pinned located rejection into a failure of the exact near-miss check. A mutant
that fails to build is invalid, never detected.
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
RUNNER = 'Compiler/SolidityImport/SequenceRunner.lean'
# name: (file, anchor, replacement, kind, rejection case)
MUTANTS = {
    # `== 0` and `!= 0` swap: every route still reads EXTCODESIZE(ADDRESS).
    'import-self-code-length-polarity': (IMPORT,
        'return some { pre := #[read], expr := if empty then test else .logicalNot test }',
        'return some { pre := #[read], expr := if empty then .logicalNot test else test }',
        'runtime', None),
    # The caller's code instead of the executing account's: an EOA never has code.
    'import-self-code-length-target': (IMPORT,
        'Stmt.ecm (Compiler.ECM.SolidityExtCodeSize.module size) [.contractAddress]',
        'Stmt.ecm (Compiler.ECM.SolidityExtCodeSize.module size) [.caller]',
        'runtime', None),
    # Denote never installs the executing account's code: it looks under construction.
    'sequence-self-code-ignored': (RUNNER,
        '    let address := Address.ofNat account\n'
        '    world := world.writeAccount address { world.accountWorld address with code }\n'
        '  -- Runtime code of foreign accounts',
        '    let _ := code\n  -- Runtime code of foreign accounts',
        'runtime', None),
    # A comparison that is not a zero test is admitted as one.
    'import-self-code-length-operator-gate': (IMPORT,
        'else if op == "!=" || op == ">" then some false else none)',
        'else if op == "!=" || op == ">" || op == ">=" then some false else none)',
        'admission', 'greater-or-equal-zero'),
    # Inline-assembly `extcodesize` of the executing contract imports again.
    'import-yul-extcodesize-self-guard': (IMPORT,
        '        let target ← lowerCodeReadTarget target j\n'
        '          "code length of an account that may be the executing contract is unsupported"\n',
        '', 'admission', 'yul-self'),
    'import-self-code-length-zero-gate': (IMPORT,
        'if (← isThisCodeLength left) && (← isZero right) then',
        'if (← isThisCodeLength left) then',
        'admission', 'equal-one'),
}


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_self_code_length',
            '--transactions', '48', '--seed', '2919', '--shrink-attempts', '40',
            '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    if result.returncode == 0 and (output / 'summary.json').exists():
        return 0
    if result.returncode == 1 and (output / 'divergence.json').exists():
        return 1
    raise HarnessError(f'no differential verdict; tool failure is not detection: {output.with_suffix(".log")}')


def rejection(directory, case, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_self_code_length_rejections',
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
                       'Compiler.SolidityImport.SequenceRunner', 'Compiler.Codegen', 'Compiler.Yul.PrettyPrint']
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'baseline-build.log')
            if kind == 'runtime':
                if runtime(directory, directory / '.lake/baseline'):
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
                if runtime(directory, campaign) == 0:
                    raise HarnessError(f'{name}: mutation survived')
                entry = {'divergence': json.loads((campaign / 'divergence.json').read_text()),
                         'campaign': str(campaign)}
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
              Path(tempfile.mkdtemp(prefix='self-code-length-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
