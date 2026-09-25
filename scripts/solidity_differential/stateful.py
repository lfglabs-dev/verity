"""Exact transaction observations and replay-based sequence reduction.

Execution adapters must replay against the union of slots touched by all three
routes. Access traces themselves may differ after optimization; final values,
including values of slots touched only on a reverted path, may not. This module
does not execute or approximate Solidity and is not yet a campaign adapter.
"""
from __future__ import annotations

import copy
import re

from .engine import HarnessError

ROUTES = ('source', 'model', 'compiled')
_HEX = re.compile(r'0x(?:[0-9a-f]{2})*\Z')


def _bytes(value, length=None):
    if not isinstance(value, str) or not _HEX.fullmatch(value):
        raise HarnessError('invalid canonical hex bytes')
    if length is not None and len(value) != 2 + 2 * length:
        raise HarnessError('invalid byte width')
    return value


def _slot(row):
    if not isinstance(row, list) or len(row) != 2:
        raise HarnessError('slot identity requires account and slot')
    return (_bytes(row[0], 20), _bytes(row[1], 32))


def validate_observation(row):
    """Validate a complete post-transaction observation; never infer defaults."""
    required = {'id', 'status', 'data', 'touched', 'storage', 'events'}
    if not isinstance(row, dict) or set(row) != required:
        raise HarnessError('incomplete or unknown transaction observation fields')
    if not isinstance(row['id'], str) or not row['id']:
        raise HarnessError('missing transaction identity')
    if row['status'] not in ('ok', 'revert'):
        raise HarnessError('execution failure is not a contract revert')
    _bytes(row['data'])
    if not all(isinstance(row[k], list) for k in ('touched', 'storage', 'events')):
        raise HarnessError('observation arrays required')
    touched = [_slot(s) for s in row['touched']]
    if len(set(touched)) != len(touched):
        raise HarnessError('duplicate touched slot')
    storage = {}
    for entry in row['storage']:
        if not isinstance(entry, list) or len(entry) != 3:
            raise HarnessError('storage entry requires account, slot and value')
        key = _slot(entry[:2])
        if key in storage:
            raise HarnessError('duplicate storage observation')
        storage[key] = _bytes(entry[2], 32)
    if not set(touched) <= storage.keys():
        raise HarnessError('missing touched storage observation')
    for event in row['events']:
        if not isinstance(event, dict) or set(event) != {'address', 'topics', 'data'}:
            raise HarnessError('incomplete event observation')
        _bytes(event['address'], 20)
        _bytes(event['data'])
        if not isinstance(event['topics'], list) or len(event['topics']) > 4:
            raise HarnessError('invalid EVM event topics')
        for topic in event['topics']:
            _bytes(topic, 32)
    if row['status'] == 'revert' and row['events']:
        raise HarnessError('reverted transaction retained emitted events')
    return set(touched), storage


def compare_sequences(transaction_ids, traces):
    """Compare exact A/B/C observations after each transaction.

    All routes must sample the cumulative union of touched slots after every
    transaction. They may include additional configured observation slots;
    those also must be sampled by every route and are compared. An adapter
    obtains this by discovery followed by deterministic replay. Discovery is
    never itself evidence of agreement.
    """
    if (not transaction_ids or any(not isinstance(i, str) or not i for i in transaction_ids)
            or len(set(transaction_ids)) != len(transaction_ids)):
        raise HarnessError('nonempty unique transaction identities required')
    if not isinstance(traces, dict) or set(traces) != set(ROUTES):
        raise HarnessError('all three execution routes required')
    if any(not isinstance(traces[r], list) or len(traces[r]) != len(transaction_ids) for r in ROUTES):
        raise HarnessError('missing or extra transaction results')
    cumulative = set()
    divergences = []
    for index, ident in enumerate(transaction_ids):
        rows = [traces[r][index] for r in ROUTES]
        parsed = [validate_observation(row) for row in rows]
        if any(row['id'] != ident for row in rows):
            raise HarnessError('transaction result identity mismatch')
        for touched, storage in parsed:
            cumulative.update(touched)
            cumulative.update(storage)
        if any(not cumulative <= storage.keys() for _, storage in parsed):
            raise HarnessError('missing cross-route or prior touched storage observation; replay required')
        values = [tuple(storage[key] for key in sorted(cumulative)) for _, storage in parsed]
        observations = {
            'status': [r['status'] for r in rows],
            'data': [r['data'] for r in rows],
            'storage': values,
            'events': [r['events'] for r in rows],
        }
        mismatch = tuple((key, v[0] == v[1], v[1] == v[2], v[0] == v[2])
                         for key, v in observations.items() if not v[0] == v[1] == v[2])
        if mismatch:
            divergences.append({'id': ident, 'index': index, 'signature': mismatch,
                                'slots': [list(k) for k in sorted(cumulative)],
                                **dict(zip(ROUTES, copy.deepcopy(rows)))})
    return divergences


def shrink_sequence(transactions, replay, max_attempts=1000):
    """Find a deletion-1-minimal sequence preserving the first mismatch category.

    `replay` runs the entire candidate from the original pre-state, including
    slot discovery/replay, and returns compare_sequences' divergences. Resource
    or instrumentation failures propagate; they can never preserve a failure.
    A budget-limited result expressly does not claim deletion minimality.
    """
    if not transactions or type(max_attempts) is not int or max_attempts < 2:
        raise HarnessError('nonempty sequence and at least two replays required')
    best = copy.deepcopy(transactions)
    initial = replay(copy.deepcopy(best))
    if not initial:
        raise HarnessError('sequence has no divergence')
    target = initial[0]['signature']
    attempts = 1
    index = 0
    while index < len(best) and len(best) > 1 and attempts < max_attempts - 1:
        candidate = best[:index] + best[index + 1:]
        result = replay(copy.deepcopy(candidate))
        attempts += 1
        if result and result[0]['signature'] == target:
            best = candidate
            index = 0  # Removing a later setup transaction can make an earlier one removable.
        else:
            index += 1
    minimal = len(best) == 1 or index == len(best)
    final = replay(copy.deepcopy(best))
    attempts += 1
    if not final or final[0]['signature'] != target:
        raise HarnessError('final replay did not reproduce the original divergence')
    return {'transactions': best, 'signature': target, 'attempts': attempts,
            'deletion_minimal': minimal}


def replay_three_routes(transactions, adapters):
    """Discover accesses, then replay all routes with one cumulative slot plan.

    Each adapter takes (transactions, per-transaction slots), starts from its
    pinned original world, and returns observations. Both passes execute real
    transactions; changing behavior between passes is an instrumentation error.
    """
    if not isinstance(transactions, list) or not transactions:
        raise HarnessError('nonempty transaction sequence required')
    if set(adapters) != set(ROUTES):
        raise HarnessError('all three execution adapters required')
    if any(not isinstance(tx, dict) or not isinstance(tx.get('id'), str) for tx in transactions):
        raise HarnessError('transaction identities required')
    ids = [tx['id'] for tx in transactions]
    if not all(ids) or len(set(ids)) != len(ids):
        raise HarnessError('unique transaction identities required')

    def run(route, plan):
        rows = adapters[route](copy.deepcopy(transactions), copy.deepcopy(plan))
        if not isinstance(rows, list) or len(rows) != len(ids):
            raise HarnessError('adapter omitted transaction results')
        for ident, row in zip(ids, rows):
            validate_observation(row)
            if row['id'] != ident:
                raise HarnessError('adapter transaction identity mismatch')
        return copy.deepcopy(rows)

    discovery = {route: run(route, [[] for _ in ids]) for route in ROUTES}
    plans, cumulative = [], set()
    for index in range(len(ids)):
        for route in ROUTES:
            touched, storage = validate_observation(discovery[route][index])
            cumulative.update(touched)
            cumulative.update(storage)
        plans.append([list(key) for key in sorted(cumulative)])
    traces = {route: run(route, plans) for route in ROUTES}
    for route in ROUTES:
        for before, after in zip(discovery[route], traces[route]):
            for key in ('id', 'status', 'data', 'events'):
                if before[key] != after[key]:
                    raise HarnessError('execution changed between discovery and replay')
            before_touched, before_storage = validate_observation(before)
            after_touched, after_storage = validate_observation(after)
            if before_touched != after_touched or any(after_storage.get(k) != v for k, v in before_storage.items()):
                raise HarnessError('storage behavior changed between discovery and replay')
    return {'discovery': discovery, 'observations': traces, 'slots': plans,
            'divergences': compare_sequences(ids, traces)}
