"""Compare eager memory and lazy calldata struct validation across A/B/C."""
import argparse
import json
from pathlib import Path
from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .engine import HarnessError, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes, shrink_sequence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-fixture', type=Path, default=Path('Contracts/SolidityImportSmoke/StructValidationOrder.sol'))
    parser.add_argument('--model-driver', type=Path, default=Path('Contracts/SolidityImportSmoke/StructValidationOrderModel.lean'))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = args.source_fixture.resolve()
    driver = args.model_driver.resolve()
    source = solc_compile({'language': 'Solidity', 'sources': {fixture.name: {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        fixture.parent, output / 'source')['contracts'][fixture.name]['StructValidationOrder']['evm']
    names = ['memoryUnused((uint256,uint8))', 'calldataUnused((uint256,uint8))',
             'memoryLate((uint256,uint8),uint256)', 'calldataLate((uint256,uint8),uint256)',
             'memoryKindsUnused((bool,address,uint128))', 'calldataKindsUnused((bool,address,uint128))',
             'memoryKindsLate((bool,address,uint128),uint256)', 'calldataKindsLate((bool,address,uint128),uint256)']
    selectors = {name.split('(')[0]: int(source['methodIdentifiers'][name], 16) for name in names}
    write_json(output / 'selectors.json', list(selectors.values()))
    identity = ImplementationIdentity(driver, extra_inputs=[fixture])
    write_json(output / 'implementation.json', identity.manifest)
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            log=output / 'compile.log')
    identity.verify()
    compiled = solc_compile({'language': 'Yul', 'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture.parent, output / 'compiled')
    objects = list(compiled['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('ABI fixture must compile to one object')
    source_code = '0x' + source['bytecode']['object']
    compiled_code = '0x' + objects[0]['evm']['bytecode']['object']
    with Anvil(output / 'discovery') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': source_code, 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('ABI fixture deployment failed')
        account = deployed['receipt']['contractAddress']
    transactions = []
    canonical = []
    expected_words = []
    def add(name, values, valid, returned):
        index = len(transactions)
        canonical.append(valid)
        expected_words.append(returned)
        transactions.append({'id': str(index), 'function': name, 'args': values,
            'sender': sender, 'target': account, 'value': '0x0',
            'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
            'data': '0x' + format(selectors[name], '08x') + ''.join(format(v, '064x') for v in values)})
    expected_reverts = []
    error_first = '0x08c379a0' + format(32, '064x') + format(5, '064x') + b'first'.hex().ljust(64, '0')
    for signature in names[:4]:
        name = signature.split('(')[0]
        late = name.endswith('Late')
        for small in (255, 256):
            for flag in ((0, 1) if late else (None,)):
                values = [11, small] + ([flag] if late else [])
                invalid = small >= 256
                memory = name.startswith('memory')
                rejected = (memory and invalid) or (late and (flag == 0 or invalid))
                add(name, values, not rejected, [small if late else 7])
                expected_reverts.append(error_first if late and flag == 0 and not (memory and invalid) else '0x')

    for signature in names[4:]:
        name = signature.split('(')[0]
        late = name.endswith('Late')
        for fields in ([1, 2**159 + 13, 2**127 + 5], [2, 13, 5], [1, 2**160, 5], [1, 13, 2**128]):
            for flag in ((0, 1) if late else (None,)):
                values = list(fields) + ([flag] if late else [])
                invalid = fields[0] >= 2 or fields[1] >= 2**160 or fields[2] >= 2**128
                memory = name.startswith('memory')
                rejected = (memory and invalid) or (late and (flag == 0 or invalid))
                add(name, values, not rejected, fields if late else [7])
                expected_reverts.append(error_first if late and flag == 0 and not (memory and invalid) else '0x')

    class PublicDenote:
        def __init__(self):
            self.count = 0

        def __call__(self, calls, plan):
            # This fixture only echoes scalar parameters: no persistent access
            # or events. Reject any contrary observation from the EVM routes.
            if any(plan):
                raise HarnessError('pure ABI fixture unexpectedly accesses storage')
            directory = output / 'B' / str(self.count)
            self.count += 1
            directory.mkdir(parents=True)
            write_json(directory / 'input.json', [{'function': row['function'],
                'selector': selectors[row['function']], 'words': [str(v) for v in row['args']]} for row in calls])
            identity.verify()
            command(['lake', 'env', 'lean', '--run', driver, 'observe', directory / 'input.json',
                     directory / 'output.json'], log=directory / 'lean.log')
            identity.verify()
            observed = json.loads((directory / 'output.json').read_text())
            if len(observed) != len(calls):
                raise HarnessError('public Denote ABI row count differs')
            rows = []
            for tx, row in zip(calls, observed):
                if row['events'] or (row['success'] and len(row['words']) != (3 if tx['function'].endswith('KindsLate') else 1)):
                    raise HarnessError('unexpected public Denote echo result')
                rows.append({'id': tx['id'], 'status': 'ok' if row['success'] else 'revert',
                    'data': '0x' + bytes(row['data']).hex(),
                    'storage': [], 'touched': [], 'events': []})
            return rows

    adapters = {'source': EVMAdapter(output / 'A', [source_code]),
        'model': PublicDenote(), 'compiled': EVMAdapter(output / 'C', [compiled_code])}
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, 'canonical': canonical, **result})
    for words, valid, revert_bytes, row in zip(expected_words, canonical, expected_reverts, result['observations']['source']):
        expected = ('ok', '0x' + ''.join(format(v, '064x') for v in words)) if valid else ('revert', revert_bytes)
        if (row['status'], row['data']) != expected:
            raise HarnessError('solc did not establish the expected ABI control')
    if result['divergences']:
        # A candidate single transaction is only used if real replay preserves
        # the original mismatch category. Otherwise retain the general shrinker.
        failure = result['divergences'][0]
        candidate = [transactions[failure['index']]]
        replayed = replay_three_routes(candidate, adapters)['divergences']
        seed = candidate if replayed and replayed[0]['signature'] == failure['signature'] else transactions
        witness = shrink_sequence(seed, lambda calls: replay_three_routes(calls, adapters)['divergences'], max_attempts=100)
        write_json(output / 'witness.json', witness)
        raise HarnessError(f"struct ABI divergence: {output / 'campaign.json'}")
    print(f'All {len(transactions)} canonical/noncanonical ABI cases agree: {output}')


if __name__ == '__main__':
    main()
