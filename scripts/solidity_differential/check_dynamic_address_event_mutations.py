"""Dynamic `T[] calldata` event-payload mutants in isolated source/cache snapshots.

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
ENCODER = 'Compiler/SolidityImport/DynamicEventAbi.lean'
# name: (file, anchor, replacement, kind, rejection case)
MUTANTS = {
    'dynamic-event-element-validator': (ENCODER,
        '(.literal (SolidityAbi.scalarBound kind)))',
        '(.literal (2 * SolidityAbi.scalarBound kind)))', 'runtime', None),
    'dynamic-event-tail-offset': (ENCODER,
        '(.sub tail base)',
        '(.sub tail (.sub base (.literal 32)))', 'runtime', None),
    'dynamic-event-length-word': (ENCODER,
        '  , .mstore tail length\n',
        '  , .mstore tail (.add length (.literal 1))\n', 'runtime', None),
    'dynamic-event-element-slot': (ENCODER,
        'let target := Expr.add (.add (.localVar names.tail) (.literal 32))',
        'let target := Expr.add (.localVar names.tail)', 'runtime', None),
    'dynamic-event-tail-end': (ENCODER,
        '.add (.localVar names.tail) (.add (.literal 32) (.mul length (.literal 32)))',
        '.add (.localVar names.tail) (.mul length (.literal 32))', 'runtime', None),
    'dynamic-event-companion-word': (ENCODER,
        '(.mstore (.add base (.literal (32 * headIndex))) value :: body, finish)',
        '(body, finish)', 'runtime', None),
    'import-dynamic-event-calldata-guard': (IMPORT,
        'unless (← mKind argument) == "Identifier" do\n'
        '        failAt argument "dynamic event array arguments must be calldata array parameters"',
        'unless true do\n'
        '        failAt argument "dynamic event array arguments must be calldata array parameters"',
        'admission', 'calldata-slice'),
    'import-dynamic-event-element-guard': (IMPORT,
        'if elementType == "bytes4" then',
        'if false then', 'admission', 'bytes4-elements'),
    'import-dynamic-event-total-companion': (IMPORT,
        '''      unless value.pre.all (fun | .letVar _ _ => true | _ => false) do
        failAt argument "event arguments currently require total scalar expressions"
      let word ← atom''',
        '''      let word ← atom''', 'admission', 'indexed-element-companion'),
}


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_dynamic_address_event', '--single',
            '--transactions', '32', '--seed', '2549', '--shrink-attempts', '60', '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'no differential report; tool failure is not detection: {output.with_suffix(".log")}')
    return result.returncode, json.loads(report_path.read_text())


def rejection(directory, case, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_dynamic_address_event_rejections',
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
              Path(tempfile.mkdtemp(prefix='dynamic-address-event-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
