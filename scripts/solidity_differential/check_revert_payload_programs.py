"""Real solc/Denote/typed Source/compiled handwritten-model payload calibration.

No importer or canonical internal-helper equivalence is claimed.
"""
import argparse
import hashlib
import json
from pathlib import Path
from .anvil import Anvil
from .engine import command, solc_compile
from .programs import revert_payload_source


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    cases = [(kind, value, variant) for kind in range(4)
             for value in (0, 1, 255, 2**256-1) for variant in range(3)]
    sources = {f'Case{i}.sol': {'content': revert_payload_source(*case)}
               for i, case in enumerate(cases)}
    settings = {'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466}, 'evmVersion': 'osaka',
                'outputSelection': {'*': {'*': ['evm.deployedBytecode.object', 'evm.methodIdentifiers']}}}
    reference = solc_compile({'language': 'Solidity', 'sources': sources, 'settings': settings}, root, job/'reference')
    selector = reference['contracts']['Case0.sol']['RevertPayload']['evm']['methodIdentifiers']['probe()']
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.SourceStatementEvaluation',
             'Compiler.Proofs.IRGeneration.DenoteFunctionAgreement', 'Compiler.CompilationModel',
             'Compiler.Codegen', 'Compiler.Yul.PrettyPrint'], cwd=root, timeout=1800, log=job/'build.log')
    template = root/'scripts/solidity_differential/revert_payload_driver.lean.txt'
    inputs = [template, Path(__file__).resolve(), root/'scripts/solidity_differential/programs.py',
              root/'Compiler/Proofs/IRGeneration/SourceSemantics.lean',
              root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/SourceExpressionOutcome.lean',
              root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/DenoteAgreement.lean',
              root/'Verity/Core/Model/Denote.lean']
    inputs = sorted(set(inputs + [p for directory in ('Compiler', 'Verity')
                                  for p in (root/directory).rglob('*.lean')] +
                        [root/'lake-manifest.json', root/'lakefile.lean']))
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    driver = template.read_text() + '\ndef main : IO Unit := do\n'
    for i, (kind, value, variant) in enumerate(cases):
        driver += f'  check {i} {kind} {value} {variant} {int(selector,16)} {json.dumps(str(job/f"model-{i}.yul"))}\n'
    (job/'Programs.lean').write_text(driver)
    lines = command(['lake', 'env', 'lean', '--run', str(job/'Programs.lean')], cwd=root,
                    timeout=1800, log=job/'semantics.log').splitlines()
    assert len(lines) == len(cases)
    semantics = []
    for i, line in enumerate(lines):
        prefix = f'OBS:{i}:'
        assert line.startswith(prefix), line
        status, data = line[len(prefix):].split(':', 1)
        assert status in ('ok', 'revert') and data.startswith('0x')
        semantics.append((status, data))
    rows = []
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        target = '0x'+'01'*20
        for i, case in enumerate(cases):
            artifact = reference['contracts'][f'Case{i}.sol']['RevertPayload']
            node.rpc('anvil_setCode', target, '0x'+artifact['evm']['deployedBytecode']['object'])
            a = node.observe(node.transact({'from': sender, 'to': target, 'data': '0x'+selector,
                                           'gas': hex(1000000)}), 'revert-payload', [])
            assert (a['status'], a['data']) == semantics[i], (i, a, semantics[i])
            assert a['events'] == [] and a['storage'] == []
            yul = job/f'model-{i}.yul'
            compiled = solc_compile({'language': 'Yul', 'sources': {yul.name: {'content': yul.read_text()}},
                                    'settings': {'optimizer': {'enabled': True, 'runs': 466}, 'evmVersion': 'osaka',
                                                 'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}},
                                    root, job/f'compiled-{i}')
            code = compiled['contracts'][yul.name]['RevertPayload']['evm']['bytecode']['object']
            deployed = node.transact({'from': sender, 'data': '0x'+code, 'gas': hex(2000000)})
            address = deployed['receipt']['contractAddress']
            assert address
            c = node.observe(node.transact({'from': sender, 'to': address, 'data': '0x'+selector,
                                           'gas': hex(1000000)}), 'revert-payload', [])
            assert a == c, (i, a, c)
            rows.append({'case': case, 'reference': a, 'compiled': c, 'semantics': semantics[i]})
    for i in range(0, len(rows), 3):
        assert rows[i]['reference'] == rows[i+1]['reference'] == rows[i+2]['reference']
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    (job/'success.json').write_text(json.dumps({'exit': 0, 'identity': identity, 'sources_unchanged': True,
        'rows': rows, 'scope': 'Root scalar payload calibration across solc, canonical Denote, staged typed Source and compiled handwritten Verity model; no importer/internal-helper/adversary/whole-function proof claim.'}, indent=2))
    print(f'{len(rows)} payload variants: exact solc/Denote/typed Source/compiled Verity observations')


if __name__ == '__main__':
    main()
