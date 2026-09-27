"""Raw ABI sequence and independent expected observations for composition tests.

No EVM result is asserted by generating these cases. The campaign must compare
these expectations to source EVM first, then require full A/B/C agreement.
"""

SIGNATURES = (
    'memoryChange((uint128[],uint256),uint8)',
    'calldataChange((uint128[],uint256),uint8)',
    'failAfterEvent((uint128[],uint256))',
    'read()',
)


def word(value):
    if type(value) is not int or not 0 <= value < 2**256:
        raise ValueError('ABI word outside uint256')
    return f'{value:064x}'


def error(message):
    payload = message.encode('utf-8')
    padded = payload + bytes((-len(payload)) % 32)
    return '0x08c379a0' + word(32) + word(len(payload)) + padded.hex()


def box(values, tag, flag=None):
    # Root offset points past all root heads. Array offset is relative to box.
    heads = [32] if flag is None else [64, flag]
    return heads + [64, tag, len(values)] + list(values)


def sequence(selectors, senders, account, event_topic):
    if len(senders) < 2:
        raise ValueError('composition requires at least two senders')
    memory, calldata, fail, read = SIGNATURES
    calls = [
        ('memory-write', memory, box([7, 8], 11, 1), 'ok', 7, True),
        ('calldata-write', calldata, box([19], 12, 1), 'ok', 19, True),
        ('event-rollback', fail, box([99], 13), error('after'), None, True),
        ('read-after-rollback', read, [], 'ok', 19, True),
        ('memory-dirty-before-guard', memory, box([2**128], 14, 0), '0x', None, False),
        ('calldata-guard-before-dirty', calldata, box([2**128], 15, 0), error('first'), None, False),
        ('calldata-dirty-read', calldata, box([2**128], 16, 1), '0x', None, False),
        ('memory-empty', memory, box([], 17, 1), '0x4e487b71' + word(0x32), None, False),
        ('calldata-empty', calldata, box([], 18, 1), '0x4e487b71' + word(0x32), None, False),
        ('dirty-root-flag', calldata, box([31], 19, 256), '0x', None, False),
        ('truncated-root', memory, [64], '0x', None, False),
        ('truncated-array', memory, box([41], 20, 1)[:-1], '0x', None, False),
        # Non-strict ABI: the array length aliases the tag word inside the tuple.
        # Tuple starts at root word 2; relative offset 32 selects word 3 (tag=1),
        # and the sole array element is word 4. No canonical tail is required.
        ('memory-aliased-tail', memory, [64, 1, 32, 1, 47], 'ok', 47, True),
        ('calldata-aliased-tail', calldata, [64, 1, 32, 1, 53], 'ok', 53, True),
        ('max-element', calldata, box([2**128 - 1], 21, 1), 'ok', 2**128 - 1, True),
        ('final-read', read, [], 'ok', 2**128 - 1, True),
    ]
    rows = []
    stored = 0
    slot = '0x' + word(0)
    for index, (label, signature, args, outcome, value, touched) in enumerate(calls):
        sender = senders[index % len(senders)]
        name = signature.split('(')[0]
        success = outcome == 'ok'
        events = []
        if success and name != 'read':
            stored = value
            tag = args[3]  # Both successful mutators have the two-word root head.
            events = [{'address': account,
                       'topics': [event_topic, '0x' + word(int(sender, 16)), '0x' + word(tag)],
                       'data': '0x' + word(value)}]
        tx = {'id': str(index), 'function': name, 'args': args, 'sender': sender,
              'target': account, 'value': '0x0', 'timestamp': 1000000100 + index,
              'blockNumber': 2 + index,
              'data': '0x' + selectors[signature] + ''.join(map(word, args))}
        rows.append({'case': label, 'transaction': tx, 'expected': {
            'id': str(index), 'status': 'ok' if success else 'revert',
            'data': '0x' + word(value) if success else outcome,
            'touched': [[account, slot]] if touched else [],
            # Observe slot zero after every transaction, even an early decoder revert.
            'storage': [[account, slot, '0x' + word(stored)]], 'events': events}})
    return rows
