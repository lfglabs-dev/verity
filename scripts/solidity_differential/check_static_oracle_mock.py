"""Compare independently computed Lean fallback bytes/accesses with real EVM.

This is a mock-program check, not imported-function A/B/C validation.
"""
import hashlib
import argparse
import json
import os
from pathlib import Path
import tempfile

from eth_abi import encode

from .anvil import Anvil
from .engine import SOLC, command, solc_compile, write_json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--solc', type=Path, default=SOLC)
    args = parser.parse_args()
    root = Path.cwd()
    fixture = root / 'test/ByteExternalCall/RawStaticOracle.sol'
    out = Path(tempfile.mkdtemp(prefix='static-oracle-mock-', dir='.lake')).resolve()
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {fixture.name: {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True,
                     'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object', 'irOptimized']}}},
    }, fixture.parent, out / 'solc', solc=args.solc)['contracts'][fixture.name]['RawStaticOracle']
    cases = [{'value': str(v), 'length': n}
             for v in (0, 42, 2**256 - 1)
             for n in (0, 1, 4, 31, 32, 33, 63, 64, 65, 96, 97)]
    write_json(out / 'inputs.json', cases)
    os.environ['LEAN_PATH'] = (root / '.lake/physical-lean-path').read_text()
    os.environ['LEAN_NUM_THREADS'] = '1'
    command(['lean', '-j', '1', '--run', 'test/ByteExternalCall/OracleResponse.lean',
             out / 'inputs.json', out / 'lean-bytes.json'], log=out / 'lean.log')
    expected = json.loads((out / 'lean-bytes.json').read_text())
    rows = []
    with Anvil(out / 'evm') as node:
        sender = node.rpc('eth_accounts')[0]
        for case, response in zip(cases, expected, strict=True):
            for fails in (False, True):
                constructor = encode(['uint256', 'bool', 'uint256'],
                                     [int(case['value']), fails, case['length']]).hex()
                deployment = node.transact({'from': sender, 'gas': hex(4000000),
                    'data': '0x' + compiled['evm']['bytecode']['object'] + constructor})
                assert deployment['receipt']['status'] == '0x1', deployment
                account = deployment['receipt']['contractAddress']
                record = node.transact({'from': sender, 'to': account,
                                       'gas': hex(2000000), 'data': '0x12345678'})
                row = node.observe(record, str(len(rows)))
                rows.append({'case': case, 'fails': fails, 'observation': row})
                write_json(out / 'observations.json', rows)
                assert row['status'] == ('revert' if fails else 'ok'), row
                assert row['data'] == '0x' + bytes(response).hex(), (case, fails, response, row)
                assert {(int(a, 16), int(s, 16)) for a, s in row['touched']} == {
                    (int(account, 16), s) for s in range(3)}, row
                assert {int(s, 16): int(v, 16) for a, s, v in row['storage']} == {
                    0: int(case['value']), 1: int(fails), 2: case['length']}, row
                assert row['events'] == [], row
    sources = [fixture, root / 'Compiler/SolidityImport/StaticOracleMocks.lean',
               root / 'test/ByteExternalCall/OracleResponse.lean', Path(__file__)]
    write_json(out / 'summary.json', {'passed': True, 'cases': len(rows),
        'scope': 'independent mock response bytes and storage accesses versus real EVM',
        'sourceHashes': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in sources}})
    print(f'{len(rows)} raw oracle mock cases passed: {out}')


if __name__ == '__main__':
    main()
