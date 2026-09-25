"""Stateful observation protocol and deterministic sequence reduction tests."""
import unittest

from solidity_differential.engine import HarnessError
from solidity_differential.stateful import ROUTES, compare_sequences, shrink_sequence, replay_three_routes

ACCOUNT = '0x' + '12' * 20
SLOT = '0x' + '00' * 32
VALUE = '0x' + '00' * 31 + '01'


def row(ident='tx'):
    return {'id': ident, 'status': 'ok', 'data': '0x', 'touched': [[ACCOUNT, SLOT]],
            'storage': [[ACCOUNT, SLOT, VALUE]], 'events': []}


def traces():
    return {r: [row()] for r in ROUTES}


class StatefulTests(unittest.TestCase):
    def test_agreement_allows_different_optimized_accesses(self):
        data = traces()
        data['compiled'][0]['touched'] = []
        self.assertEqual(compare_sequences(['tx'], data), [])

    def test_every_observable_and_route_is_compared(self):
        for route in ROUTES:
            for field, value in [('status', 'revert'), ('data', '0x01'),
                                 ('storage', [[ACCOUNT, SLOT, SLOT]]),
                                 ('events', [{'address': ACCOUNT, 'topics': [VALUE], 'data': '0x01'}])]:
                with self.subTest(route=route, field=field):
                    data = traces()
                    data[route][0][field] = value
                    mismatch = compare_sequences(['tx'], data)
                    self.assertEqual(mismatch[0]['signature'][0][0], field)

    def test_exact_revert_bytes(self):
        data = traces()
        for route in ROUTES:
            data[route][0].update(status='revert', data='0x4e487b71' + '00' * 31 + '11')
        self.assertEqual(compare_sequences(['tx'], data), [])
        data['model'][0]['data'] = '0x4e487b71' + '00' * 31 + '12'
        self.assertEqual(compare_sequences(['tx'], data)[0]['signature'][0][0], 'data')

    def test_missing_cross_route_observation_requires_replay(self):
        data = traces()
        data['compiled'][0].update(touched=[], storage=[])
        with self.assertRaisesRegex(HarnessError, 'replay required'):
            compare_sequences(['tx'], data)

    def test_previous_slots_remain_observed(self):
        data = traces()
        for route in ROUTES:
            data[route].append({**row('next'), 'touched': [], 'storage': []})
        with self.assertRaisesRegex(HarnessError, 'prior touched'):
            compare_sequences(['tx', 'next'], data)

    def test_rejects_incomplete_unknown_duplicate_and_malformed_results(self):
        variants = []
        for field in row():
            variant = row()
            del variant[field]
            variants.append(variant)
        variants += [{**row(), 'status': 'timeout'}, {**row(), 'status': 'unsupported'},
                     {**row(), 'data': '0x0'}, {**row(), 'extra': True},
                     {**row(), 'storage': row()['storage'] * 2},
                     {**row(), 'touched': row()['touched'] * 2},
                     {**row(), 'events': [{'address': ACCOUNT, 'topics': [VALUE] * 5, 'data': '0x'}]},
                     {**row(), 'status': 'revert', 'events': [{'address': ACCOUNT, 'topics': [], 'data': '0x'}]}]
        for variant in variants:
            data = traces()
            data['model'][0] = variant
            with self.subTest(variant=variant), self.assertRaises(HarnessError):
                compare_sequences(['tx'], data)
        for ids in ([], ['tx', 'tx'], ['wrong']):
            with self.assertRaises(HarnessError):
                compare_sequences(ids, traces())

    def test_discovery_replay_collects_every_routes_slots(self):
        calls = []
        def adapter(txs, slots):
            calls.append(slots)
            return [row(tx['id']) for tx in txs]
        result = replay_three_routes([{'id': 'tx'}], {r: adapter for r in ROUTES})
        self.assertEqual(result['divergences'], [])
        self.assertEqual(calls[:3], [[[]]] * 3)
        self.assertEqual(calls[3:], [[[[ACCOUNT, SLOT]]]] * 3)

    def test_discovery_replay_rejects_nondeterministic_execution(self):
        counts = {r: 0 for r in ROUTES}
        def adapter(route):
            def run(txs, slots):
                counts[route] += 1
                observed = row()
                if route == 'model' and counts[route] == 2:
                    observed['data'] = '0x01'
                return [observed]
            return run
        with self.assertRaisesRegex(HarnessError, 'changed between discovery'):
            replay_three_routes([{'id': 'tx'}], {r: adapter(r) for r in ROUTES})

    def test_shrink_preserves_setup_and_failure(self):
        def replay(xs):
            return [{'signature': ('storage',)}] if 'set' in xs and 'read' in xs and xs.index('set') < xs.index('read') else []
        result = shrink_sequence(['noise', 'set', 'noise', 'read', 'noise'], replay)
        self.assertEqual(result['transactions'], ['set', 'read'])
        self.assertTrue(result['deletion_minimal'])

    def test_shrink_does_not_change_category_or_swallow_infrastructure_failure(self):
        def replay(xs):
            return [{'signature': ('storage',) if 'set' in xs else ('data',)}]
        self.assertEqual(shrink_sequence(['set', 'read'], replay)['transactions'], ['set'])
        def failed(xs):
            if len(xs) == 1:
                raise HarnessError('out of fuel')
            return [{'signature': ('storage',)}]
        with self.assertRaisesRegex(HarnessError, 'out of fuel'):
            shrink_sequence(['set', 'read'], failed)

    def test_final_replay_must_reproduce(self):
        calls = []
        def replay(xs):
            calls.append(xs)
            return [{'signature': ('storage',)}] if len(calls) == 1 else []
        with self.assertRaisesRegex(HarnessError, 'final replay'):
            shrink_sequence(['set', 'read'], replay, max_attempts=2)

    def test_budget_and_mutating_adapter_cannot_overstate_minimality(self):
        original = ['set', 'read']
        def replay(xs):
            xs.clear()
            return [{'signature': ('storage',)}]
        result = shrink_sequence(original, replay, max_attempts=2)
        self.assertFalse(result['deletion_minimal'])
        self.assertEqual(result['transactions'], original)
        self.assertEqual(original, ['set', 'read'])


if __name__ == '__main__':
    unittest.main()
