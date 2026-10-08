"""Compare complete full-Market ABI decoding across A/B/C."""
import argparse
import hashlib
import json
from pathlib import Path
from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .engine import HarnessError, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes, shrink_sequence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-fixture', type=Path, default=Path('Contracts/SolidityImportSmoke/MarketAbi.sol'))
    parser.add_argument('--model-driver', type=Path, default=Path('Contracts/SolidityImportSmoke/MarketAbiModel.lean'))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = args.source_fixture.resolve()
    driver = args.model_driver.resolve()
    interface = fixture.parent / 'pinned-midnight/IMidnight.sol'
    manifest = json.loads((interface.parent / 'provenance.json').read_text())
    if (manifest['repository'] != 'morpho-org/midnight'
            or manifest['sha256'] != 'b1a0cbcd9de9ce3781bd12cdd0a8665361f988fd23d0219217ff4e7981710475'
            or manifest['commit'] != '96d31343e993329e7a593dde46516a2c0cbcd142'
            or manifest['path'] != 'src/interfaces/IMidnight.sol'
            or hashlib.sha256(interface.read_bytes()).hexdigest() != manifest['sha256']):
        raise HarnessError('pinned Midnight interface identity differs')
    write_json(output / 'midnight-provenance.json', manifest)
    source = solc_compile({'language': 'Solidity', 'sources': {
        fixture.name: {'content': fixture.read_text()},
        'pinned-midnight/IMidnight.sol': {'content': interface.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        fixture.parent, output / 'source')['contracts'][fixture.name]['MarketAbi']['evm']
    market = '(uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address)'
    names = [location + suffix + '(' + market + ',uint256)'
             for location in ('memory', 'calldata')
             for suffix in ('Unused', 'Maturity', 'TokenLate', 'TokenSecond', 'Midnight', 'Length')]
    selectors = {name.split('(')[0]: int(source['methodIdentifiers'][name], 16) for name in names}
    write_json(output / 'selectors.json', [{'name': name, 'selector': selector} for name, selector in selectors.items()])
    identity = ImplementationIdentity(driver, extra_inputs=[fixture, interface, interface.parent / "provenance.json"])
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
    control_labels = []
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
    canonical_words = [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9]
    variants = {'canonical': canonical_words}
    for label, index, value in [
        ('dirty-midnight', 3, 2**160), ('dirty-unused-oracle', 14, 2**160),
        ('dirty-token', 11, 2**160), ('invalid-array-offset', 5, 2**64),
        ('backwards-array-offset', 5, 2**256-32), ('empty-array', 10, 0),
        ('length-uint64-max', 10, 2**64-1), ('length-uint64-overflow', 10, 2**64),
        ('length-allocation-overflow', 10, 2**59-1)]:
        words = canonical_words.copy()
        words[index] = value
        variants[label] = words
    variants['truncated-array'] = canonical_words[:-1]
    two = canonical_words + [17, 78, 89, 10]
    two[10] = 2
    variants['two'] = two
    variants['dirty-second-oracle'] = two[:-1] + [2**160]
    variants['dirty-second-token'] = two.copy()
    variants['dirty-second-token'][15] = 2**160
    variants['truncated-root'] = [64, 1]
    variants['backwards-root'] = canonical_words.copy()
    variants['backwards-root'][0] = 2**256-32
    variants['overlapping-root'] = [0, 1, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9]
    def panic(code):
        return '0x4e487b71' + format(code, '064x')

    for signature in names:
        name = signature.split('(')[0]
        for variant, template in variants.items():
            for flag in (0, 1):
                values = template.copy()
                values[1] = flag
                memory = name.startswith('memory')
                second = name.endswith('TokenSecond')
                token = name.endswith('TokenLate') or second
                oversized = variant.startswith('length-')
                eager_invalid = variant in ('dirty-midnight', 'dirty-unused-oracle', 'dirty-token',
                    'invalid-array-offset', 'backwards-array-offset', 'truncated-array',
                    'dirty-second-oracle', 'dirty-second-token')
                error = None
                returned = 7 if name.endswith('Unused') else 999 if name.endswith('Maturity') else 17 if second else 6
                if name.endswith('Midnight'):
                    returned = flag if variant == 'overlapping-root' else 2
                if variant in ('truncated-root', 'backwards-root'):
                    error = '0x'
                elif memory and oversized:
                    error = panic(0x41)
                elif memory and eager_invalid:
                    error = '0x'
                elif flag == 0:
                    error = error_first
                elif name.endswith('Midnight') and variant == 'dirty-midnight':
                    error = '0x'
                elif name.endswith('Length'):
                    returned = 0 if variant == 'empty-array' else 2 if variant in ('two', 'dirty-second-oracle', 'dirty-second-token') else 1
                    if oversized or variant in ('invalid-array-offset', 'truncated-array'):
                        error = '0x'
                elif token:
                    if oversized or variant in ('invalid-array-offset', 'truncated-array'):
                        error = '0x'
                    elif variant == 'empty-array' or (second and variant not in ('two', 'dirty-second-oracle', 'dirty-second-token', 'backwards-array-offset')):
                        error = panic(0x32)
                    elif (not second and variant == 'dirty-token') or (second and variant == 'dirty-second-token'):
                        error = '0x'
                    elif variant == 'backwards-array-offset':
                        # Backwards header points at the flag; with flag=1 only index0 exists.
                        if second:
                            error = panic(0x32)
                        else:
                            returned = 31337
                control_labels.append({"function": name, "variant": variant, "flag": flag})
                add(name, values, error is None, [returned])
                expected_reverts.append(error or '0x')

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
    write_json(output / 'campaign.json', {'transactions': transactions, 'canonical': canonical, 'controls': control_labels, **result})
    for label, words, valid, revert_bytes, row in zip(control_labels, expected_words, canonical, expected_reverts, result['observations']['source']):
        expected = ('ok', '0x' + ''.join(format(v, '064x') for v in words)) if valid else ('revert', revert_bytes)
        if (row['status'], row['data']) != expected:
            write_json(output / 'source-control-failure.json', {'control': label,
                'expected': expected, 'actual': [row['status'], row['data']]})
            raise HarnessError(f'solc did not establish the expected ABI control: {label}')
    if result['divergences']:
        # A candidate single transaction is only used if real replay preserves
        # the original mismatch category. Otherwise retain the general shrinker.
        failure = result['divergences'][0]
        candidate = [transactions[failure['index']]]
        replayed = replay_three_routes(candidate, adapters)['divergences']
        seed = candidate if replayed and replayed[0]['signature'] == failure['signature'] else transactions
        witness = shrink_sequence(seed, lambda calls: replay_three_routes(calls, adapters)['divergences'], max_attempts=100)
        write_json(output / 'witness.json', witness)
        raise HarnessError(f"full-Market ABI divergence: {output / 'campaign.json'}")
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(transactions),
        'scope': 'actual imported full-Market source/public Denote/compiled EVM controls'})
    print(f'All {len(transactions)} full-Market ABI cases agree: {output}')


if __name__ == '__main__':
    main()
