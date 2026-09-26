"""Actual context importer mutations, with unmodified controls and reduced witnesses."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import snapshot

MUTANTS = {
    'import-msg-sender': ('pure (.expr { pre := #[], expr := .caller })', 'pure (.expr { pre := #[], expr := .literal 0 })'),
    'import-address-this': ('return { pre := #[], expr := .contractAddress }', 'return { pre := #[], expr := .literal 0 }'),
    'import-block-number': ('| "number" => pure Expr.blockNumber', '| "number" => pure (Expr.literal 0)'),
    'import-block-chainid': ('| "chainid" => pure Expr.chainid', '| "chainid" => pure (Expr.literal 0)'),
}


def run(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_stateful',
            '--model-driver', 'Contracts/SolidityImportSmoke/EnvironmentSequenceModel.lean',
            '--source-fixture', 'Contracts/SolidityImportSmoke/EnvironmentSequence.sol',
            '--transactions', '3', '--seed', '2452', '--shrink-attempts', '30',
            '--output', str(output)]
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + environment.get('PYTHONPATH', '')
    result = subprocess.run(argv, cwd=directory, env=environment,
                            text=True, capture_output=True, timeout=600)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report = json.loads((output / 'campaign.json').read_text())
    return result.returncode, report


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        before, after = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        baseline_code, baseline = run(directory, directory / '.lake/baseline')
        if baseline_code or not baseline['transactions'] or baseline['divergences']:
            raise HarnessError(f'{name}: unmodified positive control failed')
        source = directory / 'Compiler/SolidityImport/Import.lean'
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
                timeout=600, log=directory / 'build.log')
        campaign = directory / '.lake/mutated'
        code, result = run(directory, campaign)
        if code == 0 or not result['divergences']:
            raise HarnessError(f'{name}: mutation survived')
        reduced = json.loads((campaign / 'reduced.json').read_text())
        if (not reduced['deletion_minimal'] or len(reduced['transactions']) != 1 or
                reduced['signature'] != [['data', False, True, False]]):
            raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
        reports.append({'mutant': name, 'status': 'detected', 'detected': True, 'baselinePassed': True,
                        'witness': reduced, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    output = Path(tempfile.mkdtemp(prefix='environment-mutations-', dir='.lake')).resolve()
    mutation_campaign(output)
    print(output)


if __name__ == '__main__':
    main()
