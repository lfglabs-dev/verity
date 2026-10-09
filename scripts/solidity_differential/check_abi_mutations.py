"""Runtime mutations of imported scalar ABI guards with positive controls."""
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot

# Source-ordinal mutation restores one-word-per-source-parameter addressing;
# full tuple parameters must instead contribute their complete ABI head size.
MUTANTS = {'import-abi-source-offset': ('(.literal (4 + (modelParams.toList.take i).foldl (fun n p => n + '
                              'paramHeadSize p.ty) 0))',
                              '(.literal (4 + 32*((srcParams.findIdx? (·.name == p.name)).getD 0)))'),
 'import-abi-drop': ('let body := abiGuards ++ body', 'let body := body'),
 'import-abi-offset': ('(.literal (4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize '
                       'p.ty) 0))',
                       '(.literal (36 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize '
                       'p.ty) 0))'),
 'import-abi-uint-bound': ('\n            | .uintN bits => if bits < 256 then some (2^bits) else none',
                           '\n'
                           '            | .uintN bits => if bits < 256 then some (2^(bits+1)) else none'),
 'import-abi-address-bound': ('\n            | .address => some (2^160)',
                              '\n            | .address => some (2^161)'),
 'import-abi-bool-bound': ('\n            | .bool => some 2', '\n            | .bool => some 3'),
 'import-abi-inclusive': ('\n            (.lt (.calldataload', '\n            (.le (.calldataload'),
 'import-abi-revert': ('\n            [] [.revertReturndata])',
                       '\n            [] [.panic .arithmeticOverflow])')}


def run(directory, output):
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts')
    result = subprocess.run([sys.executable, '-m', 'solidity_differential.check_abi',
        '--output', str(output)], cwd=directory, env=environment,
        text=True, capture_output=True, timeout=1200)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    path = output / 'campaign.json'
    if not path.exists():
        raise HarnessError(f'ABI mutation has no runtime report: {output}; tool failure is not detection')
    return result.returncode, json.loads(path.read_text())


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        before, after = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        code, baseline = run(directory, directory / '.lake/baseline')
        if code or not baseline['transactions'] or baseline['divergences']:
            raise HarnessError(f'{name}: positive control failed')
        source = directory / 'Compiler/SolidityImport/Import.lean'
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=600, log=directory / 'build.log')
        campaign = directory / '.lake/mutated'
        code, report = run(directory, campaign)
        if not code or not report['divergences']:
            raise HarnessError(f'{name}: mutation survived')
        witness = json.loads((campaign / 'witness.json').read_text())
        if not witness['deletion_minimal'] or not witness['transactions'] or not witness['signature']:
            raise HarnessError(f'{name}: missing reproduced minimal witness')
        reports.append({'mutant': name, 'status': 'detected', 'detected': True,
            'baselinePassed': True, 'witness': witness, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}
