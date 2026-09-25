"""Real-node adapter regressions. Run: PYTHONPATH=scripts python3 -m solidity_differential.check_anvil."""
import json
import random
from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter
from .engine import HarnessError, solc_compile, write_json


def main():
    output = Path(tempfile.mkdtemp(prefix='stateful-anvil-', dir='.lake')).resolve()
    fixture = Path(__file__).parent / 'fixtures/Observations.sol'
    request = {'language': 'Solidity', 'sources': {'Observations.sol': {'content': fixture.read_text()}},
               'settings': {'evmVersion': 'osaka', 'viaIR': True,
                            'optimizer': {'enabled': True, 'runs': 466},
                            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    compiled = solc_compile(request, fixture.parent, output / 'solc')
    evm = compiled['contracts']['Observations.sol']['Observations']['evm']
    observations = []
    with Anvil(output) as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(2000000)})
        assert deployed['receipt']['status'] == '0x1'
        address = deployed['receipt']['contractAddress']
        def call(signature, argument='', slots=()):
            record = node.transact({'from': sender, 'to': address, 'gas': hex(1000000),
                                    'data': '0x' + evm['methodIdentifiers'][signature] + argument})
            observed = node.observe(record, str(len(observations)), slots)
            observations.append(observed)
            return observed
        zero = '0x' + '00' * 32
        first = call('change(uint256)', format(7, '064x'))
        assert int(first['data'], 16) == 0 and int(first['storage'][0][2], 16) == 7
        assert len(first['events']) == 1 and first['events'][0]['topics'][1] == zero
        assert int(first['events'][0]['data'], 16) == 7
        second = call('change(uint256)', format(8, '064x'))
        assert int(second['data'], 16) == 7 and int(second['storage'][0][2], 16) == 8
        reverted = call('fail()')
        message = b'rolled back'
        expected = '0x08c379a0' + format(32, '064x') + format(len(message), '064x') + message.hex().ljust(64, '0')
        assert reverted['status'] == 'revert' and reverted['data'] == expected
        assert reverted['touched'] == [[address, zero]] and int(reverted['storage'][0][2], 16) == 8
        assert reverted['events'] == []
        # Each RPC transaction clears transient storage. A loop of low-level
        # calls within one Foundry test transaction would return 1 the second time.
        assert int(call('transientProbe()', slots=[(address, zero)])['data'], 16) == 0
        assert int(call('transientProbe()', slots=[(address, zero)])['data'], 16) == 0
        other = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(2000000)})
        foreign = other['receipt']['contractAddress']
        caught = call('catchFailure(address)', foreign[2:].rjust(64, '0'))
        assert caught['status'] == 'ok'
        slots = {(account, slot): int(value, 16) for account, slot, value in caught['storage']}
        assert slots[(address, zero)] == 9 and slots[(foreign, zero)] == 0
        assert [foreign, zero] in caught['touched']
        assert len(caught['events']) == 1 and caught['events'][0]['address'] == address
        # Dynamic bytes return: ABI offset, byte length, exact callee revert bytes.
        returned = bytes.fromhex(caught['data'][2:])
        payload = bytes.fromhex(expected[2:])
        assert int.from_bytes(returned[:32], 'big') == 32
        assert int.from_bytes(returned[32:64], 'big') == len(payload)
        assert returned[64:64 + len(payload)] == payload
        assert all(b == 0 for b in returned[64 + len(payload):])
        try:
            call('exceptional()')
        except HarnessError as error:
            assert 'exceptional halt' in str(error)
        else:
            raise AssertionError('invalid opcode was misclassified as a contract revert')
    transactions = [
        {'id': str(index), 'sender': sender, 'target': address, 'value': '0x0',
         'data': '0x' + evm['methodIdentifiers']['change(uint256)'] + format(value, '064x'),
         'timestamp': 1000000010 + index, 'blockNumber': 2 + index}
        for index, value in enumerate((7, 8))]
    adapter = SequenceAdapter(output / 'sequence', ['0x' + evm['bytecode']['object']])
    discovered = adapter(transactions, [[], []])
    replayed = adapter(transactions, [row['touched'] for row in discovered])
    assert discovered == replayed
    assert int(replayed[0]['data'], 16) == 0 and int(replayed[1]['data'], 16) == 7
    assert int(replayed[1]['storage'][0][2], 16) == 8
    reduced = adapter(transactions[1:], [[]])
    assert reduced[0]['id'] == '1' and int(reduced[0]['data'], 16) == 0
    assert int(reduced[0]['storage'][0][2], 16) == 8
    archived = json.loads((output / 'sequence/2/sequence.json').read_text())
    assert archived['bytecodes'] == ['0x' + evm['bytecode']['object']]
    assert archived['initialStorage'] == [] and archived['calldataKey'] == 'data'
    assert archived['node']['hardfork'] == 'osaka' and archived['node']['chainId'] == 31337
    assert archived['node']['version'].startswith('anvil Version:')
    assert archived['observations'] == reduced and archived['transactions'] == transactions[1:]
    assert archived['receipts'][0]['id'] == '1'
    receipt_path = output / 'sequence/2' / (archived['receipts'][0]['transactionHash'] + '.json')
    assert json.loads(receipt_path.read_text())['receipt']['blockNumber'] == '0x3'
    rng = random.Random(2448)
    random_transactions, expected_values = [], []
    current = 0
    for index in range(32):
        fails = rng.randrange(4) == 0
        value = rng.choice([0, 1, (1 << 256) - 1, rng.getrandbits(256)])
        data = ('0x' + evm['methodIdentifiers']['fail()'] if fails else
                '0x' + evm['methodIdentifiers']['change(uint256)'] + format(value, '064x'))
        random_transactions.append({'id': f'random-{index}', 'sender': sender,
            'target': address, 'value': '0x0', 'data': data,
            'timestamp': 1000000100 + index, 'blockNumber': 2 + index})
        expected_values.append((fails, current, current if fails else value))
        if not fails:
            current = value
    random_rows = adapter(random_transactions, [[] for _ in random_transactions])
    for row, (fails, before, after) in zip(random_rows, expected_values):
        assert row['status'] == ('revert' if fails else 'ok')
        assert row['data'] == (expected if fails else '0x' + format(before, '064x'))
        assert row['storage'] == [[address, zero, '0x' + format(after, '064x')]]
        assert len(row['events']) == (0 if fails else 1)
        if not fails:
            assert row['events'][0]['topics'][1] == '0x' + format(before, '064x')
            assert row['events'][0]['data'] == '0x' + format(after, '064x')
    assert any(item[0] for item in expected_values) and any(not item[0] for item in expected_values)
    random_replayed = adapter(random_transactions, [row['touched'] for row in random_rows])
    assert random_replayed == random_rows
    write_json(output / 'observations.json', observations)
    print('Anvil: persistence, exact return/revert bytes, reverted writes/logs, transaction-local transient storage, exceptional halt checks passed')


if __name__ == '__main__':
    main()
