"""Runtime mutations of full static tuple binding and ordered field validation."""
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot

MUTANTS = {'import-struct-tuple-order': ('Compiler/SolidityImport/Import.lean',
                               'ty := .tuple types }',
                               'ty := .tuple types.reverse }'),
 'import-struct-memory-drop': ('Compiler/SolidityImport/Import.lean',
                               'unless mem.calldataLocation do',
                               'if false then'),
 'import-struct-calldata-eager': ('Compiler/SolidityImport/Import.lean',
                                  'unless mem.calldataLocation do',
                                  'if true then'),
 'import-struct-calldata-drop': ('Compiler/SolidityImport/Import.lean',
                                 'if mem.calldataLocation then\n      if let some bound := limit then',
                                 'if false then\n      if let some bound := limit then'),
 'import-struct-member-value': ('Compiler/SolidityImport/Import.lean',
                                's!"{mem.param}_{idx}"',
                                's!"{mem.param}_{idx-1}"'),
 'import-struct-member-offset': ('Compiler/SolidityImport/Import.lean',
                                 '(.literal (32*idx))',
                                 '(.literal (32*(idx+1)))'),
 'import-struct-head-base': ('Compiler/SolidityImport/Import.lean',
                             '(.letVar mem.headBinding (.literal offset))',
                             '(.letVar mem.headBinding (.literal (offset+32)))'),
 'import-struct-memory-offset': ('Compiler/SolidityImport/Import.lean',
                                 '(.literal (offset + 32*j))',
                                 '(.literal (offset + 32*(j+1)))'),
 'denote-struct-member-offset': ('Verity/Core/Model/DynamicAbi.lean',
                                 'let tail ← go rest (index + 1) (current + paramHeadSize elemTy)',
                                 'let tail ← go rest (index + 1) current'),
 'denote-struct-member-name': ('Verity/Core/Model/DynamicAbi.lean',
                               'let tail ← go rest (index + 1) (current + paramHeadSize elemTy)',
                               'let tail ← go rest index (current + paramHeadSize elemTy)'),
 'denote-struct-member-value': ('Verity/Core/Model/DynamicAbi.lean',
                                'some [(name, value)]\ntermination_by sizeOf ty',
                                'some [(name, 0)]\ntermination_by sizeOf ty')}


def run(directory, output):
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts')
    result = subprocess.run([sys.executable, '-m', 'solidity_differential.check_struct_abi',
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
