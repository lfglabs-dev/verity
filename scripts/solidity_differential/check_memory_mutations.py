"""Real Denote memory regressions, private caches and minimal EVM witnesses.

These handwritten drivers measure semantics; they do not claim Solidity
importer admission or discharge their explicit low-level obligations.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from .engine import HarnessError, command, write_json
from .mutations import release, snapshot

MUTANTS = {
    'denote-calldata-load-selector-data': (
        '  DynamicAbi.calldataloadWord selector calldata offset\n',
        '  if offset = 0 then selectorWord selector\n'
        '  else if offset < 4 then 0\n'
        '  else DynamicAbi.calldataloadWord selector calldata offset\n'),
    'denote-calldata-copy-drop': (
        'world := state.world.copyPhysicalCalldata state.selector dst src sz',
        'world := state.world'),
}


def run(directory, output, name):
    load = name == 'denote-calldata-load-selector-data'
    fixture = 'CalldataWindowSequence' if load else 'PhysicalCopySequence'
    base = int.from_bytes(bytes(range(1, 33)), 'big')
    prefixes = [base + index for index in range(4)] if load else [base]
    argv = [sys.executable, '-m', 'solidity_differential.check_stateful',
            '--model-driver', f'Contracts/SolidityImportSmoke/{fixture}Model.lean',
            '--source-fixture', f'Contracts/SolidityImportSmoke/{fixture}.sol',
            '--argument-bits', '256', '--transactions', str(3 + len(prefixes)),
            '--seed', '2472' if load else '2471', '--shrink-attempts', '30',
            '--output', str(output), '--change-prefix', *map(str, prefixes)]
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    environment['PYTHONPATH'] = str(directory / 'scripts')
    result = subprocess.run(argv, cwd=directory, env=environment,
                            text=True, capture_output=True, timeout=600)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report = output / 'campaign.json'
    if not report.exists():
        raise HarnessError(f'{name}: no completed A/B/C comparison; see {output.with_suffix(".log")}')
    return result.returncode, json.loads(report.read_text())


def rebuild_denote(directory):
    # Only the canonical Denote implementation changes. Rebuild its actual
    # handwritten-driver dependencies serially, without a parallel Lake build.
    for module in ['Verity/Core/Model/Denote', 'Verity/Core/Model/DenoteFunctionCalls',
                   'Compiler/SolidityImport/Transactions',
                   'Compiler/SolidityImport/TransactionAccess',
                   'Compiler/SolidityImport/SequenceRunner']:
        artifact = directory / '.lake/build/lib/lean' / (module + '.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        if artifact.is_symlink():
            artifact.unlink()
        command(['lake', 'env', 'lean', '-j', '1', '-M', '8192', module + '.lean',
                 '-o', str(artifact)], cwd=directory, timeout=600,
                log=directory / (module.replace('/', '-') + '.log'))


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        directory = output / name
        snapshot(directory)
        try:
            code, baseline = run(directory, directory / '.lake/baseline', name)
            if code or not baseline['transactions'] or baseline['divergences']:
                raise HarnessError(f'{name}: unmodified positive control failed')
            source = directory / 'Verity/Core/Model/Denote.lean'
            before, after = MUTANTS[name]
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError(f'{name}: mutation anchor is not unique')
            source.write_text(text.replace(before, after))
            rebuild_denote(directory)
            campaign = directory / '.lake/mutated'
            code, result = run(directory, campaign, name)
            if code == 0 or not result['divergences']:
                raise HarnessError(f'{name}: mutation survived')
            reduced = json.loads((campaign / 'reduced.json').read_text())
            expected = [['data', False, False, True], ['storage', False, False, True]]
            if (not reduced['deletion_minimal'] or len(reduced['transactions']) != 1
                    or reduced['transactions'][0]['function'] != 'change'
                    or reduced['signature'] != expected):
                raise HarnessError(f'{name}: expected a reproduced minimal A=C/B divergence')
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True,
                        'baselinePassed': True, 'witness': reduced, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=list(MUTANTS))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix='memory-mutations-', dir='.lake'))
    mutation_campaign(output, [args.only] if args.only else None)
    print(output)


if __name__ == '__main__':
    main()
