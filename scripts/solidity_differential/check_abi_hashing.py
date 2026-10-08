"""Compare imported ABI hash buffers against solc EVM and independent byte hashes."""
import argparse
import os
from pathlib import Path
import sys


PINNED_HASHING_FILES = {
    'libraries/IdLib.sol': 'a4fad41d5f053b6f1873c728d6531694a1c348fc3488d1ae0c1571d1765e2dfb',
    'interfaces/IMidnight.sol': 'b1a0cbcd9de9ce3781bd12cdd0a8665361f988fd23d0219217ff4e7981710475',
}


def validate_dependencies(fixture_dir):
    """The import fixture must use the actual pinned Midnight files."""
    import hashlib
    import json
    root = fixture_dir / 'pinned-midnight'
    provenance = json.loads((root / 'hashing-provenance.json').read_text())
    if provenance['repository'] != 'morpho-org/midnight' or provenance['commit'] != \
            '96d31343e993329e7a593dde46516a2c0cbcd142':
        raise ValueError('hashing dependency pin differs')
    if set(provenance['files']) != set(PINNED_HASHING_FILES):
        raise ValueError('hashing dependency inventory differs')
    for name, expected in PINNED_HASHING_FILES.items():
        if provenance['files'][name] != {'source': 'src/' + name, 'sha256': expected}:
            raise ValueError('hashing dependency provenance differs')
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError('hashing dependency bytes differ: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--fixture-dir', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--case-index', type=int, action='append', help='focused mutation corpus indices')
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    os.chdir(repo)
    sys.path.insert(0, str(repo / 'scripts'))
    from eth_hash.auto import keccak
    from eth_abi import encode
    from solidity_differential.anvil import Anvil, SequenceAdapter as EVMAdapter
    from solidity_differential.denote import SequenceAdapter as DenoteAdapter
    from solidity_differential.engine import HarnessError, command, solc_compile, write_json
    from solidity_differential.identity import ImplementationIdentity
    from solidity_differential.stateful import replay_three_routes, shrink_sequence

    output.mkdir(parents=True, exist_ok=False)
    fixture_dir = args.fixture_dir.resolve() if args.fixture_dir else repo / 'Contracts/SolidityImportSmoke'
    validate_dependencies(fixture_dir)
    fixture = fixture_dir / 'AbiHashing.sol'
    template = (fixture_dir / 'AbiHashingModel.lean').read_text()
    anchor = '"Contracts/SolidityImportSmoke"'
    if template.count(anchor) != 1:
        raise HarnessError('unique imported fixture path required')
    driver = output / 'Driver.lean'
    import json
    driver.write_text(template.replace(anchor, json.dumps(str(fixture_dir))))
    identity = ImplementationIdentity(driver, extra_inputs=[fixture, fixture_dir / "pinned-midnight/interfaces/IMidnight.sol", fixture_dir / "pinned-midnight/libraries/IdLib.sol", fixture_dir / "pinned-midnight/hashing-provenance.json", Path(__file__)])
    write_json(output / 'implementation.json', identity.manifest)
    compiled = solc_compile({'language': 'Solidity',
        'sources': {fixture.name: {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        fixture_dir, output / 'source')
    source = compiled['contracts'][fixture.name]['AbiHashing']['evm']
    signatures = ['scalar(uint128,address,bytes32,bool)', 'empty()',
                  'distinct(uint256,uint256)', 'composed(uint256,uint256)']
    market_type = '(uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address)'
    array_type = '(uint128,uint128[],uint256[])'
    signatures += [f'marketMemory({market_type},uint256)', f'marketCalldata({market_type},uint256)',
                   'staticRoot((uint128,address,bool,bytes32))',
                   f'arraysMemory({array_type})', f'arraysCalldata({array_type})']
    signatures += ['packedScalars(uint8,address,uint256,bytes32,bool)', f'idMarket({market_type})']
    signatures += [f'prefix{n}(uint256)' for n in (0,1,11,31,32,33,63,64,65)]
    signatures += ['storeDigest(uint256,uint256)', 'readDigest()']
    selectors = source['methodIdentifiers']
    # Independently check selectors; compilation must use the actual source selectors.
    if any(selectors[s] != keccak(s.encode())[:4].hex() for s in signatures):
        raise HarnessError('source selector identity mismatch')
    write_json(output / 'selectors.json', [int(selectors[s], 16) for s in signatures])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json',
             output / 'model.yul'], timeout=600, log=output / 'compile.log')
    identity.verify()
    model = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture_dir, output / 'compiled')
    objects = list(model['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('one compiled model required')
    source_code = '0x' + source['bytecode']['object']
    with Anvil(output / 'discovery') as node:
        sender = node.rpc('eth_accounts')[0]
        deployment = node.transact({'from': sender, 'data': source_code, 'gas': hex(10000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('source deployment failed')
        account = deployment['receipt']['contractAddress']
    def words(values):
        return b''.join(value.to_bytes(32, 'big') for value in values)
    vectors = []
    for values in ([0, 0, 0, 0], [1, 2, 3, 1],
                   [2**128-1, 2**160-1, 2**256-1, 1]):
        vectors.append((signatures[0], values, 'ok', keccak(words(values))))
    for index, dirty in [(0, 2**128), (1, 2**160), (3, 2)]:
        values = [1, 2, 3, 1]
        values[index] = dirty
        vectors.append((signatures[0], values, 'revert', b''))
    vectors.append((signatures[0], [1, 2, 3], 'revert', b''))
    vectors.append((signatures[1], [], 'ok', keccak(b'')))
    for values in ([0, 0], [1, 2], [2**256-1, 0], [17, 17]):
        digests = b''.join(keccak(words([value])) for value in values)
        vectors.append((signatures[2], values, 'ok', digests))
        vectors.append((signatures[3], values, 'ok', keccak(digests)))
    def as_words(data):
        assert len(data) % 32 == 0
        return [int.from_bytes(data[i:i+32], 'big') for i in range(0, len(data), 32)]
    def address(value):
        return '0x' + value.to_bytes(20, 'big').hex()
    first_error = keccak(b'Error(string)')[:4] + encode(['string'], ['first'])
    for count in (0, 1, 2):
        elements = [(address(100+i), 200+i, 300+i, address(400+i)) for i in range(count)]
        market = (11, address(12), address(13), elements, 14, 15, address(16), address(17))
        payload = as_words(encode([market_type, 'uint256'], [market, 1]))
        expected = keccak(encode([market_type], [market]))
        for sig in signatures[4:6]:
            vectors.append((sig, payload, 'ok', expected))
            # Dirty static field: memory validation precedes the source guard;
            # calldata validation happens only after the guard is executed.
            dirty = payload.copy()
            dirty[3] = 2**160
            vectors.append((sig, dirty.copy(), 'revert', b''))
            dirty[1] = 0
            vectors.append((sig, dirty, 'revert', b'' if sig.startswith('marketMemory') else first_error))
            vectors.append((sig, payload[:-1], 'revert', b''))
            if count:
                dirty_element = payload.copy()
                dirty_element[11] = 2**160
                vectors.append((sig, dirty_element, 'revert', b''))
        # Permit a noncanonical but valid tuple position with an unused gap;
        # encode(market) must produce the canonical output offsets.
        shifted = [96, 1, 999] + payload[2:]
        for sig in signatures[4:6]:
            vectors.append((sig, shifted, 'ok', expected))
    static = [123, 456, 1, 789]
    vectors.append((signatures[6], static, 'ok', keccak(words(static))))
    vectors.append((signatures[6], [2**128, 456, 1, 789], 'revert', b''))
    for left, right in [([], []), ([1], [2]), ([3, 4], [5, 6, 7])]:
        root = (99, left, right)
        payload = as_words(encode([array_type], [root]))
        for sig in signatures[7:9]:
            vectors.append((sig, payload, 'ok', keccak(encode([array_type], [root]))))
            # Point both tails at the same array. Encoding must duplicate it.
            overlap = payload.copy()
            overlap[3] = overlap[2]
            vectors.append((sig, overlap, 'ok', keccak(encode([array_type], [(99, left, left)]))))
            if left:
                dirty = payload.copy()
                dirty[5] = 2**128
                vectors.append((sig, dirty, 'revert', b''))
    for values in ([0, 0, 0, 0, 0], [255, 2**160-1, 2**256-1, 1234, 1]):
        packed = b''.join(value.to_bytes(width, 'big') for value, width in zip(values, [1,20,32,32,1]))
        vectors.append((signatures[9], values, 'ok', keccak(packed)))
    for count in (0, 1, 2):
        market = (11, address(12), address(13),
                  [(address(100+i), 200+i, 300+i, address(400+i)) for i in range(count)],
                  14, 15, address(16), address(17))
        encoded = encode([market_type], [market])
        inner = keccak(bytes.fromhex('600b380380600b5f395ff3') + encoded)
        outer = b'\xff' + bytes.fromhex(market[1][2:]) + bytes(32) + inner
        assert len(outer) == 85
        vectors.append((signatures[10], as_words(encoded), 'ok', keccak(outer)))
    for n in (0,1,11,31,32,33,63,64,65):
        prefix = bytes((i*7+3)%256 for i in range(n))
        for value in (0, 2**256-1):
            vectors.append((f'prefix{n}(uint256)', [value], 'ok', keccak(prefix + words([value]))))
    stored = keccak(b'\xff' + words([17]))
    vectors += [
        ('storeDigest(uint256,uint256)', [17, 1], 'ok', stored),
        ('storeDigest(uint256,uint256)', [19, 0], 'revert',
            keccak(b'Error(string)')[:4] + encode(['string'], ['rollback'])),
        ('readDigest()', [], 'ok', stored),
        ('storeDigest(uint256,uint256)', [23, 1], 'ok', keccak(b'\xff' + words([23]))),
        ('readDigest()', [], 'ok', keccak(b'\xff' + words([23]))),
    ]
    if args.case_index is not None:
        if not args.case_index or len(set(args.case_index)) != len(args.case_index):
            raise HarnessError('mutation case selection must be nonempty and unique')
        if any(index < 0 or index >= len(vectors) for index in args.case_index):
            raise HarnessError('mutation case index outside corpus')
        vectors = [vectors[index] for index in args.case_index]
    transactions, expectations = [], []
    storage_seen, stored_value = False, bytes(32)
    storage_slot = "0x" + bytes(32).hex()
    for index, (signature, values, status, data) in enumerate(vectors):
        transactions.append({'id': str(index), 'function': signature.split('(')[0], 'args': values,
            'sender': sender, 'target': account, 'value': '0x0',
            'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
            'data': '0x' + selectors[signature] + words(values).hex()})
        touched, storage, events = [], [], []
        if signature == 'readDigest()':
            data = stored_value
        if signature in ('storeDigest(uint256,uint256)', 'readDigest()'):
            storage_seen = True
            touched = [[account, storage_slot]]
            if signature.startswith('storeDigest') and status == 'ok':
                stored_value = data
                events = [{'address': account,
                           'topics': ['0x' + keccak(b'Hashed(bytes32)').hex(), '0x' + data.hex()],
                           'data': '0x'}]
        if storage_seen:
            storage = [[account, storage_slot, '0x' + stored_value.hex()]]
        expectations.append({'id': str(index), 'status': status, 'data': '0x' + data.hex(),
                             'touched': touched, 'storage': storage, 'events': events})
    write_json(output / 'expectations.json', expectations)
    adapters = {'source': EVMAdapter(output / 'A', [source_code]),
        'model': DenoteAdapter(output / 'B', driver, account, identity=identity),
        'compiled': EVMAdapter(output / 'C', ['0x' + objects[0]['evm']['bytecode']['object']])}
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        reduced = shrink_sequence(transactions,
            lambda txs: replay_three_routes(txs, adapters)['divergences'], max_attempts=1000)
        identity.verify()
        write_json(output / 'reduced.json', reduced)
        raise HarnessError('ABI hashing divergence; witness retained')
    if any(observations != expectations for observations in result['observations'].values()):
        raise HarnessError('ABI hashing differs from independent byte expectations')
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(vectors),
        'scope': 'scalar and complete root ABI hashes, independent bytes and A/B/C'})
    print(f'{len(vectors)} ABI hashing cases agree with independent bytes and A/B/C')


if __name__ == '__main__':
    main()
