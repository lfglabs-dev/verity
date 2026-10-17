"""Calibrate bytes header/payload/padding against source EVM execution.

This is A/B representation evidence. It does not prove pointer equality,
allocator/gas equivalence or imported/compiled-model C behavior.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, write_json


def tail(payload):
    return len(payload).to_bytes(32, 'big') + payload + bytes((-len(payload)) % 32)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Verity.Core.Model.BytesObjectMemory'], log=out / 'build.log')
    fixture = Path(__file__).parent / 'fixtures/BytesObjectMemory.sol'
    request = {'language': 'Solidity', 'sources': {'BytesObjectMemory.sol': {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
        'metadata': {'bytecodeHash': 'none'},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    evm = solc_compile(request, fixture.parent, out / 'source')['contracts']['BytesObjectMemory.sol']['BytesObjectMemoryFixture']['evm']
    selector = bytes.fromhex(evm['methodIdentifiers']['inspect(bytes,bytes)'])
    rng = random.Random(2502)
    sizes = [0, 1, 2, 31, 32, 33, 63, 64, 65, 127, 128, 129] + [rng.randrange(257) for _ in range(16)]
    inputs = [{'id': str(i), 'payload': [rng.randrange(256) for _ in range(size)],
               'nextPayload': [rng.randrange(256) for _ in range(sizes[-i-1])]} for i, size in enumerate(sizes)]
    write_json(out / 'input.json', inputs)
    driver = Path('Contracts/SolidityImportSmoke/BytesObjectMemoryDriver.lean')
    command(['lake', 'env', 'lean', '--run', driver, out / 'input.json', out / 'lean.json'], log=out / 'lean.log')
    results = json.loads((out / 'lean.json').read_text())
    if len(results) != len(inputs):
        raise HarnessError('memory representation model omitted rows')
    observations = []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployment = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(10000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('memory representation source deployment failed')
        address = deployment['receipt']['contractAddress']
        for row, result in zip(inputs, results):
            payload, next_payload = bytes(row['payload']), bytes(row['nextPayload'])
            first = tail(payload)
            data = selector + (64).to_bytes(32, 'big') + (64 + len(first)).to_bytes(32, 'big') + first + tail(next_payload)
            execution = node.transact({'from': sender, 'to': address, 'data': '0x' + data.hex(), 'gas': hex(10000000)})
            actual = execution['call'].get('output')
            expected = '0x' + first.hex()
            observation = {'id': row['id'], 'evm': actual, 'model': result,
                           'transactionHash': execution['receipt']['transactionHash']}
            observations.append(observation)
            if (execution['receipt']['status'] != '0x1' or result['id'] != row['id'] or
                    result['before'] != list(first) or result['after'] != list(first) or actual != expected):
                write_json(out / 'divergence.json', observation)
                raise HarnessError('source/model memory object representation diverged')
        write_json(out / 'provenance.json', {'node': node.provenance, 'scope': __doc__,
            'files': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [fixture, driver, Path('Verity/Core/Model/BytesObjectMemory.lean')]}})
    write_json(out / 'observations.json', observations)
    write_json(out / 'complete.json', {'exit': 0, 'transactions': len(inputs), 'scope': __doc__})
    print(f'Memory representation: {len(inputs)} actual EVM/Lean calls agree')


if __name__ == '__main__':
    main()
