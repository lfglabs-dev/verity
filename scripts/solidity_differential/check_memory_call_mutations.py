"""Memory-call mutants in isolated source/cache snapshots: inline-assembly `call` /
`staticcall` over memory through the closed memory-call transport.

Each mutant must survive an unmodified positive control of its A/B/C campaign and then
produce a divergence with a reproduced deletion-minimal witness. A mutant that fails to
build is invalid, never detected.
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
DENOTE = 'Verity/Core/Model/Denote.lean'
ECM = 'Verity/Core/Model/ECM.lean'
YUL = ('solidity_differential.check_yul_memory_call', '--transactions', '64', '--seed', '2531',
       'Contracts.SolidityImportSmoke.YulMemoryCallSequenceModel')
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
    'ecm-yul-call-value': (ECM,
        'YulExpr.call "call" [gas, target, .lit 0, inOffset, inSize, outOffset, outSize]',
        'YulExpr.call "call" [gas, target, .lit 1, inOffset, inSize, outOffset, outSize]', YUL),
}
MODULES = ['Compiler.SolidityImport.Import', 'Compiler.SolidityImport.Differential',
           'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.CallResponderMocks',
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
        modules = [*MODULES, campaign[-1]]
        directory = output / name
        snapshot(directory)
        try:
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'baseline-build.log')
            code, baseline = runtime(directory, campaign, directory / '.lake/baseline')
            if code or baseline['divergences'] or not baseline['transactions']:
                raise HarnessError(f'{name}: unmodified positive control failed')
            source = directory / relative
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError(f'{name}: nonunique mutation anchor')
            source.write_text(text.replace(before, after))
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'build.log')
            mutated = directory / '.lake/mutated'
            code, report = runtime(directory, campaign, mutated)
            if code == 0 or not report['divergences']:
                raise HarnessError(f'{name}: mutation survived')
            reduced = json.loads((mutated / 'reduced.json').read_text())
            if not reduced['deletion_minimal'] or not reduced['transactions'] or not reduced['signature']:
                raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True, 'baselinePassed': True,
                        'path': relative, 'witness': reduced, 'campaign': str(mutated)})
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
