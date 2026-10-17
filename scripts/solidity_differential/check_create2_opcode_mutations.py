"""Replay executable opcode mutants against preserved actual EVM observations.

No source transactions are rerun. Baselines and mutants execute Lean from the
same saved opcode memory and initial account ledger. Build or instrument errors
never count as detection. This is A/B opcode calibration, not imported A/B/C.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json


MUTANTS = {
    'create2-initcode-word-cost': ('Create2ParentGas',
        '32000 + 8 * ((size + 31) / 32)', '32000 + 7 * ((size + 31) / 32)', 1),
    'create2-eip150-divisor': ('Create2Opcode',
        'value := context.value, childGas := charged.childGas,',
        'value := context.value, childGas := (context.gas - charged.opcodeGas) - (context.gas - charged.opcodeGas) / 63,', 1),
    'create2-parent-refund': ('Create2Opcode',
        'gasLeft, childGas := charged.childGas', 'gasLeft := gasLeft + 1, childGas := charged.childGas', 1),
    'create2-memory-expansion': ('Create2Opcode',
        'memory := expand memory charged.memoryWords',
        'memory := expand memory (charged.memoryWords - 1)', 1),
}


def categories(actual, expected):
    if actual['id'] != expected['id']:
        raise HarnessError('opcode witness identity differs')
    fields = ['status', 'accounts', 'childGas', 'parentGasLeft', 'memoryWords']
    if expected['status'] == 'ok':
        fields.append('address')
    if expected['childGasLeft'] is not None:
        fields.append('childGasLeft')
    # Missing fields are instrumentation errors, not semantic mismatches.
    return [field for field in fields if actual[field] != expected[field]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-campaign', type=Path, help='reuse immutable actual EVM opcode observations; otherwise generate them')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutant', action='append', choices=sorted(MUTANTS), help='run selected mutants; default is all')
    args = parser.parse_args()
    repo = Path.cwd()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('opcode mutations require a clean exact checkout')
    head = command(['git', 'rev-parse', 'HEAD']).strip()
    saved = args.source_campaign.resolve() if args.source_campaign else out / 'source'
    if args.source_campaign is None:
        # The child resolves `solidity_differential` from this checkout's scripts.
        env = dict(os.environ, PYTHONPATH=str(repo / 'scripts'))
        with (out / 'source.log').open('x') as log:
            result = subprocess.run([sys.executable, '-m', 'solidity_differential.check_deployment_world',
                                     '--parent-opcode', '--output', str(saved)], env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=MUTANT_BUILD_TIMEOUT + 300)
        if result.returncode:
            raise HarnessError('opcode source campaign failed; see source.log')
    input_data = json.loads((saved / 'input.json').read_text())
    expected = json.loads((saved / 'source-observations.json').read_text())
    request = json.loads((saved / 'source.input.json').read_text())
    fixture = repo / 'scripts/solidity_differential/fixtures/DeploymentWorld.sol'
    if request['sources']['DeploymentWorld.sol']['content'] != fixture.read_text():
        raise HarnessError('saved EVM source differs from the current fixture')
    if len(input_data['steps']) != len(expected) or not expected:
        raise HarnessError('source campaign observations are incomplete')
    if any('code' in step or 'childGas' in step for step in input_data['steps']):
        raise HarnessError('opcode inputs must contain memory and parent gas, not a child result')
    source_files = [saved / 'input.json', saved / 'source-observations.json',
                    saved / 'source.input.json', saved / 'source.output.json',
                    saved / 'node-provenance.json',
                    *sorted((saved / 'node').glob('*.create2-gas.json'))]
    if len(list((saved / 'node').glob('*.create2-gas.json'))) != len(expected):
        raise HarnessError('source campaign omits raw CREATE2 opcode traces')
    source_hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in source_files}
    write_json(out / 'source-provenance.json', {'sha256': source_hashes})
    work = out / 'work'
    command(['git', 'clone', '--shared', '--no-hardlinks', repo, work])
    command(['git', '-C', work, 'checkout', '--detach', head])
    (work / '.lake').mkdir()
    command(['cp', '-a', '--reflink=auto', repo / '.lake/build', work / '.lake/build'])
    (work / '.lake/packages').symlink_to((repo / '.lake/packages').resolve(), target_is_directory=True)
    modules = {name: work / f'Verity/Core/Model/{name}.lean'
               for name in {spec[0] for spec in MUTANTS.values()}}
    originals = {name: path.read_text() for name, path in modules.items()}
    driver = 'Contracts/SolidityImportSmoke/Create2OpcodeDriver.lean'

    def execute(directory, steps):
        directory.mkdir(parents=True, exist_ok=False)
        payload = {**input_data, 'steps': steps}
        write_json(directory / 'input.json', payload)
        with (directory / 'build.log').open('x') as log:
            built = subprocess.run(['lake', 'build', 'Verity.Core.Model.Create2Opcode'],
                                   cwd=work, stdout=log, stderr=subprocess.STDOUT,
                                   timeout=MUTANT_BUILD_TIMEOUT)
        if built.returncode:
            raise HarnessError('opcode mutant failed to build; not a detection')
        with (directory / 'execution.log').open('x') as log:
            result = subprocess.run(['lake', 'env', 'lean', '--run', driver,
                                     str(directory / 'input.json'), str(directory / 'observations.json')],
                                    cwd=work, stdout=log, stderr=subprocess.STDOUT, timeout=180)
        if result.returncode:
            raise HarnessError('opcode execution failed; not a detection')
        rows = json.loads((directory / 'observations.json').read_text())
        if len(rows) != len(steps) or [row['id'] for row in rows] != [step['id'] for step in steps]:
            raise HarnessError('opcode execution omitted or reordered observations')
        write_json(directory / 'implementation.json', {'head': head,
            'moduleSha256': {name: hashlib.sha256(path.read_bytes()).hexdigest()
                             for name, path in modules.items()}})
        return rows

    baseline = execute(out / 'baseline', input_data['steps'])
    if any(categories(actual, source) for actual, source in zip(baseline, expected)):
        raise HarnessError('opcode baseline does not match preserved real EVM')
    rows = []
    try:
        for name in args.mutant or list(MUTANTS):
            module, before, after, count = MUTANTS[name]
            original = originals[module]
            if original.count(before) != count:
                raise HarnessError('nonunique opcode mutation anchor: ' + name)
            mutated = original.replace(before, after)
            modules[module].write_text(mutated)
            full = execute(out / name / 'full', input_data['steps'])
            mismatches = [categories(actual, source) for actual, source in zip(full, expected)]
            if not mismatches[0]:
                raise HarnessError('opcode mutant has no first-call witness: ' + name)
            witness = execute(out / name / 'witness', input_data['steps'][:1])
            signature = categories(witness[0], expected[0])
            if signature != mismatches[0]:
                raise HarnessError('minimal opcode witness changed mismatch categories')
            if execute(out / name / 'delete-0', []) != []:
                raise HarnessError('single-deletion control failed')
            sha = hashlib.sha256(mutated.encode()).hexdigest()
            for phase in ['full', 'witness', 'delete-0']:
                manifest = json.loads((out / name / phase / 'implementation.json').read_text())
                if manifest['moduleSha256'][module] != sha or manifest['head'] != head:
                    raise HarnessError('executed opcode mutant provenance differs')
            rows.append({'mutant': name, 'detected': True, 'baselinePassed': True,
                         'witnessCaseIds': [expected[0]['id']], 'signature': signature,
                         'deletion_minimal': True, 'moduleSha256': sha,
                         'scope': 'Lean execution versus preserved actual EVM opcode observations; no C route'})
            write_json(out / 'mutation-results.json', rows)
            modules[module].write_text(original)
    finally:
        for name, source in originals.items():
            modules[name].write_text(source)
    if command(['git', 'rev-parse', 'HEAD']).strip() != head or command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('source checkout changed during opcode mutations')
    if source_hashes != {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in source_files}:
        raise HarnessError('preserved EVM evidence changed during mutation replay')
    write_json(out / 'complete.json', {'head': head, 'exit': 0, 'mutants': len(rows)})
    print(f'Detected {len(rows)} executable opcode mutants with one-call replay witnesses')


if __name__ == '__main__':
    main()
