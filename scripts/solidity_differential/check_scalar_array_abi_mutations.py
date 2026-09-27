"""Runtime mutations of contiguous scalar-array materialization."""
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot

MUTANTS = {'import-scalar-array-source-stride': ('Compiler/SolidityImport/AbiLowering.lean', 'let value := Expr.calldataload (.add data (.mul (.localVar index) (.literal 32)))', 'let value := Expr.calldataload (.add data (.mul (.add (.localVar index) (.literal 1)) (.literal 32)))'), 'import-scalar-array-memory-stride': ('Compiler/SolidityImport/AbiLowering.lean', '(.mul (.localVar index) (.literal 32))) value])]', '(.mul (.localVar index) (.literal 64))) value])]'), 'import-scalar-array-validation': ('Compiler/SolidityImport/AbiLowering.lean', 'let checks := if bound = 2^256 then [] else [guard (.lt value (.literal bound))]\n  [.mstore', 'let checks := if bound = 2^256 then [] else [guard (.literal 1)]\n  [.mstore'), 'import-scalar-array-length': ('Compiler/SolidityImport/AbiLowering.lean', '[.mstore arrayPointer length,\n   .mstore', '[.mstore arrayPointer (.literal 0),\n   .mstore')}

def run(directory, output):
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts')
    result = subprocess.run([sys.executable, '-m', 'solidity_differential.check_scalar_array_abi',
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
        relative, before, after = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        code, baseline = run(directory, directory / '.lake/baseline')
        if code or not baseline['transactions'] or baseline['divergences']:
            raise HarnessError(f'{name}: positive control failed')
        source = directory / relative
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
