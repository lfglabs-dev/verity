"""Explicit code/nonce observations for deployment validation.

This instrument does not implement CREATE2 or supply a Denote deployment oracle.
Creator bytecode differs by construction between source and compiled routes;
compare its nonce and balance, and compare complete code for created accounts.
Every route must provide every explicitly planned account, including nonexistent
accounts and deployments rolled back by the parent. Missing data is an error.
"""
import copy

from .engine import HarnessError, write_json
from .stateful import ROUTES, _bytes, compare_sequences, validate_observation


def _word(value):
    if type(value) is not int or not 0 <= value < 2**256:
        raise HarnessError('account quantity must be an unsigned 256-bit integer')
    return value


def validate_accounts(row):
    if not isinstance(row, dict) or set(row) != {'creator', 'accounts'}:
        raise HarnessError('complete deployment observations required')
    creator = row['creator']
    if not isinstance(creator, dict) or set(creator) != {'address', 'nonce', 'balance'}:
        raise HarnessError('complete creator observation required')
    _bytes(creator['address'], 20)
    _word(creator['nonce'])
    _word(creator['balance'])
    if not isinstance(row['accounts'], list):
        raise HarnessError('account observation array required')
    accounts = {}
    for account in row['accounts']:
        if not isinstance(account, dict) or set(account) != {'address', 'code', 'nonce', 'balance'}:
            raise HarnessError('complete created-account observation required')
        address = _bytes(account['address'], 20)
        if address == creator['address'] or address in accounts:
            raise HarnessError('duplicate or creator deployment account')
        accounts[address] = (_bytes(account['code']), _word(account['nonce']), _word(account['balance']))
    return creator, accounts


def observe_accounts(node, record, creator, addresses):
    """Sample exact post-state at the transaction's mined block, never latest."""
    addresses = list(addresses)
    if len(set(addresses)) != len(addresses):
        raise HarnessError('duplicate deployment observation address')
    block = record['receipt']['blockNumber']
    def quantities(address):
        return {'address': address,
                'nonce': int(node.rpc('eth_getTransactionCount', address, block), 16),
                'balance': int(node.rpc('eth_getBalance', address, block), 16)}
    result = {'creator': quantities(creator),
              'accounts': [{**quantities(address), 'code': node.rpc('eth_getCode', address, block)}
                           for address in sorted(addresses)]}
    validate_accounts(result)
    return result


def discover_create2_accounts(node, record):
    """Recover attempted CREATE2 addresses, including missing call-tracer `to`.

    Foundry's call tracer omits `to` on collisions and invalid runtime code.
    Pair its ordered creation frames with opcode trace CREATE2 operands and
    memory, check the actual initcode, then apply EIP-1014 using real Keccak.
    Any disagreement or missing trace is an instrument error, never an empty
    account set. CREATE requires a separate nonce-based discovery rule.
    """
    frames = []
    def visit(frame):
        if not isinstance(frame, dict) or not isinstance(frame.get('calls', []), list):
            raise HarnessError('incomplete creation call trace')
        if frame.get('type') == 'CREATE':
            raise HarnessError('CREATE account discovery is not implemented')
        if frame.get('type') == 'CREATE2':
            frames.append(frame)
        for child in frame.get('calls', []):
            visit(child)
    visit(record['call'])
    trace = node.rpc('debug_traceTransaction', record['receipt']['transactionHash'],
                     {'disableStorage': True, 'disableStack': False, 'enableMemory': True})
    write_json(node.directory / (record['receipt']['transactionHash'] + '.create2-raw-trace.json'), trace)
    if not isinstance(trace, dict) or not isinstance(trace.get('structLogs'), list):
        raise HarnessError('creation opcode trace required')
    instructions = [step for step in trace['structLogs'] if step.get('op') == 'CREATE2']
    if len(instructions) != len(frames):
        raise HarnessError('opcode and call trace creation counts differ')
    def word(text, padded=False):
        if not isinstance(text, str):
            raise HarnessError('trace word must be hex')
        raw = text.removeprefix('0x')
        # Foundry serializes stack words as short hex quantities, while memory
        # chunks are full 32-byte words. Both decode exactly; reject overflow.
        if not 1 <= len(raw) <= 64 or (padded and len(raw) != 64) or any(c not in '0123456789abcdef' for c in raw):
            raise HarnessError('noncanonical trace word')
        return raw
    addresses = set()
    for frame, instruction in zip(frames, instructions):
        stack, memory = instruction.get('stack'), instruction.get('memory')
        if not isinstance(stack, list) or len(stack) < 4 or not isinstance(memory, list):
            raise HarnessError('CREATE2 stack and memory required')
        _, offset, size, salt = (int(word(v), 16) for v in reversed(stack[-4:]))
        # The Osaka size limit bounds accepted initcode, and this instrument's
        # own allocation. Oversize exceptional calls need a separate observer.
        if size > 49152:
            raise HarnessError('oversize CREATE2 opcode observation is not implemented')
        data = bytes.fromhex(''.join(word(v, padded=True) for v in memory))
        # EVM reads expand memory with zeros. Avoid allocating up to offset.
        initcode = data[offset:offset + size]
        initcode += bytes(size - len(initcode))
        if frame.get('input') != '0x' + initcode.hex():
            raise HarnessError('CREATE2 opcode memory and call initcode differ')
        creator = _bytes(frame.get('from'), 20)
        digest = _bytes(node.rpc('web3_sha3', '0x' + initcode.hex()), 32)
        address = '0x' + _bytes(node.rpc('web3_sha3',
            '0xff' + creator[2:] + format(salt, '064x') + digest[2:]), 32)[-40:]
        if 'to' in frame and frame['to'] != address:
            raise HarnessError('CREATE2 trace address differs from EIP-1014')
        addresses.add(address)
    write_json(node.directory / (record['receipt']['transactionHash'] + '.create2-trace.json'),
               {'trace': trace, 'frames': frames, 'addresses': sorted(addresses)})
    return addresses


class DeploymentSequenceAdapter:
    """Actual EVM discovery/replay with bytecode and environment pinned."""
    def __init__(self, directory, bytecodes, creator, initial_storage=()):
        from .anvil import SequenceAdapter
        self.creator = _bytes(creator, 20)
        self.account_plan = None
        self.indices = {}
        self.adapter = SequenceAdapter(directory, bytecodes, initial_storage=initial_storage,
                                       observer=self.observe)

    def observe(self, node, record, ident, slots):
        row = node.observe(record, ident, slots)
        addresses = discover_create2_accounts(node, record)
        addresses.update(self.account_plan[self.indices[ident]])
        row['deployment'] = observe_accounts(node, record, self.creator, addresses)
        return row

    def __call__(self, transactions, slot_plan, account_plan):
        if len(transactions) != len(account_plan):
            raise HarnessError('deployment adapter requires complete account plan')
        self.indices = {tx['id']: index for index, tx in enumerate(transactions)}
        if len(self.indices) != len(transactions):
            raise HarnessError('unique deployment transaction ids required')
        self.account_plan = copy.deepcopy(account_plan)
        return self.adapter(transactions, slot_plan)


def replay_deployment_routes(transactions, adapters):
    """Discover cross-route slots/accounts and replay from each pinned prestate."""
    if not isinstance(transactions, list) or not transactions or set(adapters) != set(ROUTES):
        raise HarnessError('nonempty transactions and all deployment adapters required')
    ids = [tx.get('id') if isinstance(tx, dict) else None for tx in transactions]
    if any(not isinstance(ident, str) or not ident for ident in ids) or len(set(ids)) != len(ids):
        raise HarnessError('unique deployment transaction identities required')
    def run(route, slots, accounts):
        rows = adapters[route](copy.deepcopy(transactions), copy.deepcopy(slots), copy.deepcopy(accounts))
        if not isinstance(rows, list) or len(rows) != len(ids):
            raise HarnessError('deployment adapter omitted results')
        for ident, row in zip(ids, rows):
            if not isinstance(row, dict) or row.get('id') != ident or 'deployment' not in row:
                raise HarnessError('incomplete deployment adapter observation')
            validate_observation({k: v for k, v in row.items() if k != 'deployment'})
            validate_accounts(row['deployment'])
        return copy.deepcopy(rows)
    empty = [[] for _ in ids]
    discovery = {route: run(route, empty, empty) for route in ROUTES}
    slots, accounts, cumulative_slots, cumulative_accounts = [], [], set(), set()
    for index in range(len(ids)):
        for route in ROUTES:
            row = discovery[route][index]
            touched, storage = validate_observation({k: v for k, v in row.items() if k != 'deployment'})
            _, states = validate_accounts(row['deployment'])
            cumulative_slots.update(touched)
            cumulative_slots.update(storage)
            cumulative_accounts.update(states)
        slots.append([list(key) for key in sorted(cumulative_slots)])
        accounts.append(sorted(cumulative_accounts))
    observations = {route: run(route, slots, accounts) for route in ROUTES}
    for route in ROUTES:
        for before, after in zip(discovery[route], observations[route]):
            for key in ('id', 'status', 'data', 'events'):
                if before[key] != after[key]:
                    raise HarnessError('deployment execution changed between discovery and replay')
            bt, bs = validate_observation({k: v for k, v in before.items() if k != 'deployment'})
            at, ast = validate_observation({k: v for k, v in after.items() if k != 'deployment'})
            bc, ba = validate_accounts(before['deployment'])
            ac, aa = validate_accounts(after['deployment'])
            if bt != at or any(ast.get(k) != v for k, v in bs.items()) or bc != ac or any(aa.get(k) != v for k, v in ba.items()):
                raise HarnessError('deployment state changed between discovery and replay')
    return {'discovery': discovery, 'observations': observations, 'slots': slots, 'accounts': accounts,
            'divergences': compare_deployment_sequences(ids, observations, accounts)}


def compare_deployment_sequences(ids, traces, account_plan):
    """Compare base observations plus code/nonces/balances on an explicit plan.

    A discovery adapter must build the cumulative cross-route account union;
    supplying only each route's locally created accounts is not sufficient.
    This API requires that plan instead of inferring empty account state.
    """
    if len(account_plan) != len(ids):
        raise HarnessError('deployment plan does not cover all transactions')
    if not isinstance(traces, dict) or set(traces) != set(ROUTES):
        raise HarnessError('all three deployment routes required')
    if any(not isinstance(traces[r], list) or len(traces[r]) != len(ids) for r in ROUTES):
        raise HarnessError('incomplete deployment sequence')
    base = {route: [] for route in ROUTES}
    parsed = {route: [] for route in ROUTES}
    cumulative = set()
    for index, plan in enumerate(account_plan):
        if not isinstance(plan, list) or len(set(plan)) != len(plan):
            raise HarnessError('unique deployment address plan required')
        expected = {_bytes(address, 20) for address in plan}
        if not cumulative <= expected:
            raise HarnessError('deployment plan dropped a previously observed account')
        cumulative = expected
        for route in ROUTES:
            row = traces[route][index]
            if not isinstance(row, dict) or 'deployment' not in row:
                raise HarnessError('missing deployment state; base-only observations are insufficient')
            creator, accounts = validate_accounts(row['deployment'])
            if set(accounts) != expected:
                raise HarnessError('deployment account observation differs from explicit plan')
            parsed[route].append((creator, accounts))
            base[route].append({key: value for key, value in row.items() if key != 'deployment'})
    divergences = compare_sequences(ids, base)
    for index, ident in enumerate(ids):
        rows = [parsed[route][index] for route in ROUTES]
        if len({row[0]['address'] for row in rows}) != 1:
            raise HarnessError('creator identity differs across routes')
        values = {
            'creatorNonce': [row[0]['nonce'] for row in rows],
            'creatorBalance': [row[0]['balance'] for row in rows],
            'code': [tuple(row[1][a][0] for a in sorted(row[1])) for row in rows],
            'accountNonce': [tuple(row[1][a][1] for a in sorted(row[1])) for row in rows],
            'accountBalance': [tuple(row[1][a][2] for a in sorted(row[1])) for row in rows],
        }
        signature = tuple((key, v[0] == v[1], v[1] == v[2], v[0] == v[2])
                          for key, v in values.items() if not v[0] == v[1] == v[2])
        if signature:
            divergences.append({'id': ident, 'index': index, 'signature': signature,
                                'accounts': sorted(rows[0][1])})
    return sorted(divergences, key=lambda row: row['index'])
