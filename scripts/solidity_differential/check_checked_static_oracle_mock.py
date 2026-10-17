"""Compare the Lean `checked-static-oracle-v1` program with real EVM.

This is a mock-program check, not imported-function A/B/C validation: response
bytes, success, and the exact set of touched slots must agree for every
configuration/calldata pair.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile

from eth_abi import encode

from .anvil import Anvil
from .engine import SOLC, command, solc_compile, write_json

ORACLE = Path('Contracts/SolidityImportSmoke/InterfaceStaticCallOracle.sol')
DRIVER = Path('test/ByteExternalCall/CheckedOracleResponse.lean')
PRICE = 0xa035b1fe


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--solc', type=Path, default=SOLC)
    args = parser.parse_args()
    root = Path.cwd()
    out = Path(tempfile.mkdtemp(prefix='checked-static-oracle-mock-', dir='.lake')).resolve()
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {ORACLE.name: {'content': (root / ORACLE).read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
                     'metadata': {'bytecodeHash': 'none'},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, root, out / 'solc', solc=args.solc)['contracts'][ORACLE.name]['CheckedStaticOracle']
    selector = PRICE.to_bytes(4, 'big')
    calldatas = [selector, selector + bytes(32), b'', selector[:3], bytes(4),
                 (PRICE + 1).to_bytes(4, 'big'), selector + b'\x00']
    cases = []
    for value in (0, 42, 2**256 - 1):
        for failed in (0, 1):
            for length in (0, 1, 4, 31, 32, 33, 64, 65, 96, 97):
                for data in calldatas:
                    expected_length = 36 if len(data) == 36 else 4
                    cases.append({'value': str(value), 'failed': str(failed), 'length': str(length),
                                  'expected': str(PRICE << 224), 'expectedLength': str(expected_length),
                                  'calldata': '0x' + data.hex()})
    write_json(out / 'inputs.json', cases)
    command(['lake', 'env', 'lean', '--run', DRIVER, out / 'inputs.json', out / 'lean.json'],
            timeout=900, log=out / 'lean.log')
    expected = json.loads((out / 'lean.json').read_text())
    rows = []
    with Anvil(out / 'evm') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = {}
        for case, response in zip(cases, expected, strict=True):
            key = (case['value'], case['failed'], case['length'], case['expectedLength'])
            if key not in deployed:
                constructor = encode(['uint256', 'bool', 'uint256', 'uint256', 'uint256'],
                    [int(case['value']), case['failed'] == '1', int(case['length']),
                     int(case['expected']), int(case['expectedLength'])]).hex()
                deployment = node.transact({'from': sender, 'gas': hex(4000000),
                    'data': '0x' + compiled['evm']['bytecode']['object'] + constructor})
                assert deployment['receipt']['status'] == '0x1', deployment
                deployed[key] = deployment['receipt']['contractAddress']
            account = deployed[key]
            record = node.transact({'from': sender, 'to': account, 'gas': hex(2000000),
                                    'data': case['calldata']})
            row = node.observe(record, str(len(rows)))
            rows.append({'case': case, 'observation': row, 'lean': response})
            write_json(out / 'observations.json', rows)
            assert row['status'] == ('ok' if response['success'] else 'revert'), (case, response, row)
            assert row['data'] == '0x' + bytes(response['data']).hex(), (case, response, row)
            assert {(int(a, 16), int(s, 16)) for a, s in row['touched']} == {
                (int(account, 16), s) for s in response['touched']}, (case, response, row)
            assert row['events'] == [], row
    sources = [ORACLE, root / 'Compiler/SolidityImport/StaticOracleMocks.lean', DRIVER, Path(__file__)]
    write_json(out / 'summary.json', {'passed': True, 'cases': len(rows),
        'scope': 'checked oracle mock response bytes, status and storage accesses versus real EVM',
        'sourceHashes': {str(p): hashlib.sha256((root / p).read_bytes()).hexdigest() for p in sources}})
    print(f'{len(rows)} checked oracle mock cases passed: {out}')


if __name__ == '__main__':
    main()
