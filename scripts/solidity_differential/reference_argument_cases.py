"""Independent raw ABI inputs and expectations; requires source-EVM confirmation."""
from .abi_event_cases import word, error, box

SIGNATURES = (
    'memoryRead((uint128[],uint256))',
    'calldataRead((uint128[],uint256))',
    'rightRoot((uint128[],uint256),(uint128[],uint256))',
    'sameRoot((uint128[],uint256))',
    'usingReceiver((uint128[],uint256))',
    'staticRead((uint128,uint256))',
    'guarded((uint128[],uint256),uint256)',
    'read()',
)


def roots(left, right):
    a = [64, left[1], len(left[0]), *left[0]]
    b = [64, right[1], len(right[0]), *right[0]]
    return [64, 64 + 32 * len(a), *a, *b]


def sequence(selectors, senders, account, event_topic):
    memory, calldata, right, same, receiver, static, guarded, read = SIGNATURES
    panic = '0x4e487b71' + word(0x32)
    calls = [
        ('memory-nested', memory, box([7, 8], 11), 'ok', 7, 11),
        ('calldata-helper', calldata, box([19], 12), 'ok', 19, 12),
        ('distinct-roots', right, roots(([3], 5), ([17], 23)), 'ok', 25, None),
        ('same-root-alias', same, box([29], 31), 'ok', 60, None),
        ('using-receiver', receiver, box([37], 41), 'ok', 37, None),
        ('static-struct', static, [43, 47], 'ok', 90, None),
        ('static-dirty', static, [2**128, 47], '0x', None, None),
        ('memory-dirty-unused', memory, box([7, 2**128], 53), '0x', None, None),
        ('calldata-dirty-unused', calldata, box([59, 2**128], 61), 'ok', 59, 61),
        ('calldata-dirty-accessed', calldata, box([2**128], 67), '0x', None, None),
        ('guard-before-dirty', guarded, box([2**128], 71, 0), error('first'), None, None),
        ('guard-dirty-accessed', guarded, box([2**128], 71, 1), '0x', None, None),
        ('guard-valid', guarded, box([73], 79, 1), 'ok', 73, None),
        ('memory-empty', memory, box([], 83), panic, None, None),
        ('calldata-empty', calldata, box([], 89), panic, None, None),
        ('truncated-memory', memory, box([97], 101)[:-1], '0x', None, None),
        ('truncated-calldata', calldata, box([103], 107)[:-1], '0x', None, None),
        ('overlapping-tail', receiver, [32, 32, 1, 109], 'ok', 109, None),
        ('max-word', same, box([2**128 - 1], 0), 'ok', 2**128 - 1, None),
        ('read-after-failures', read, [], 'ok', 59, None),
    ]
    rows, stored = [], 0
    slot = '0x' + word(0)
    for index, (label, signature, args, outcome, value, tag) in enumerate(calls):
        success = outcome == 'ok'
        events = []
        if success and tag is not None:
            stored = value
            events = [{'address': account, 'topics': [event_topic, '0x' + word(tag)],
                       'data': '0x' + word(value)}]
        name = signature.split('(')[0]
        touched = success and (tag is not None or name == 'read')
        tx = {'id': str(index), 'function': name, 'args': args,
              'sender': senders[index % len(senders)], 'target': account, 'value': '0x0',
              'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
              'data': '0x' + selectors[signature] + ''.join(map(word, args))}
        rows.append({'case': label, 'transaction': tx, 'expected': {
            'id': str(index), 'status': 'ok' if success else 'revert',
            'data': '0x' + word(value) if success else outcome,
            'touched': [[account, slot]] if touched else [],
            'storage': [[account, slot, '0x' + word(stored)]], 'events': events}})
    return rows
