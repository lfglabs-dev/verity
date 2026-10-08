"""Compare complete multiple-root ABI decoding across A/B/C."""
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
    parser.add_argument('--source-fixture', type=Path, default=Path('Contracts/SolidityImportSmoke/MultipleDynamicAbi.sol'))
    parser.add_argument('--model-driver', type=Path, default=Path('Contracts/SolidityImportSmoke/MultipleDynamicAbiModel.lean'))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = args.source_fixture.resolve()
    driver = args.model_driver.resolve()
    source = solc_compile({'language': 'Solidity', 'sources': {fixture.name: {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        fixture.parent, output / 'source')['contracts'][fixture.name]['MultipleDynamicAbi']['evm']
    names = [location + suffix + '((uint128[],uint128),(uint128[],uint128),uint8)'
             for location in ('memory', 'calldata') for suffix in ('Left', 'Right')]
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
    base = [96, 224, 1, 64, 11, 1, 7, 64, 22, 1, 8]
    variants = {'canonical': base}
    for label, index, value in [('dirty-left-tag',4,2**128), ('dirty-right-tag',8,2**128),
            ('dirty-left-element',6,2**128), ('dirty-right-element',10,2**128),
            ('alias-right-left',1,96), ('empty-left',5,0), ('empty-right',9,0)]:
        words = base.copy()
        words[index] = value
        variants[label] = words
    variants['swap-roots'] = [224, 96] + base[2:]
    variants['truncated-root'] = base[:3]
    variants['truncated-right-array'] = base[:-1]
    controls = []
    for signature in names:
        name = signature.split('(')[0]
        for label, template in variants.items():
            for flag in (0, 1, 256):
                values = template.copy()
                values[2] = flag
                memory = name.startswith('memory')
                left = name.endswith('Left')
                error = None
                returned = 7 if left else 8
                if label == 'alias-right-left':
                    returned = 7
                elif label == 'swap-roots':
                    returned = 8 if left else 7
                if label == 'truncated-root' or (memory and (label.startswith('dirty-') or label == 'truncated-right-array')):
                    error = '0x'
                elif flag == 256:
                    error = '0x'
                elif flag == 0:
                    error = error_first
                elif label == ('dirty-left-element' if left else 'dirty-right-element') or (not left and label == 'truncated-right-array'):
                    error = '0x'
                elif label == ('empty-left' if left else 'empty-right'):
                    error = '0x4e487b71' + format(0x32, '064x')
                add(name, values, error is None, [returned])
                expected_reverts.append(error or '0x')
                controls.append({'function':name, 'variant':label, 'flag':flag})

    class PublicDenote:
        def __init__(self):
            self.count = 0

        def __call__(self, calls, plan):
            # The Lean driver checks actual access traces: no persistent access
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
                if row['events'] or (row['success'] and len(row['words']) != 1):
                    raise HarnessError('unexpected public Denote echo result')
                rows.append({'id': tx['id'], 'status': 'ok' if row['success'] else 'revert',
                    'data': '0x' + bytes(row['data']).hex(),
                    'storage': [], 'touched': [], 'events': []})
            return rows

    adapters = {'source': EVMAdapter(output / 'A', [source_code]),
        'model': PublicDenote(), 'compiled': EVMAdapter(output / 'C', [compiled_code])}
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, 'canonical': canonical, 'controls': controls, **result})
    for control, words, valid, revert_bytes, row in zip(controls, expected_words, canonical, expected_reverts, result['observations']['source']):
        expected = ('ok', '0x' + ''.join(format(v, '064x') for v in words)) if valid else ('revert', revert_bytes)
        if (row['status'], row['data']) != expected:
            write_json(output / 'source-control-failure.json', {'control':control, 'expected':expected, 'actual':[row['status'],row['data']]})
            raise HarnessError(f'solc did not establish expected ABI control: {control}')
    if result['divergences']:
        # A candidate single transaction is only used if real replay preserves
        # the original mismatch category. Otherwise retain the general shrinker.
        failure = result['divergences'][0]
        candidate = [transactions[failure['index']]]
        replayed = replay_three_routes(candidate, adapters)['divergences']
        seed = candidate if replayed and replayed[0]['signature'] == failure['signature'] else transactions
        witness = shrink_sequence(seed, lambda calls: replay_three_routes(calls, adapters)['divergences'], max_attempts=100)
        write_json(output / 'witness.json', witness)
        raise HarnessError(f"multiple-root ABI divergence: {output / 'campaign.json'}")
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(transactions),
        'scope': 'actual imported multiple-root source/public Denote/compiled EVM controls'})
    print(f'All {len(transactions)} multiple-root ABI cases agree: {output}')


if __name__ == '__main__':
    main()
