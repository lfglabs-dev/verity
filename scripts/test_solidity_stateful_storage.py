"""Metamorphic comparison preserves all observable differences."""
import copy
import unittest

from solidity_differential.check_storage import canonical_observations
from solidity_differential.engine import HarnessError


class StorageObservationTests(unittest.TestCase):
    def setUp(self):
        address = '0x' + '11' * 20
        self.keys = [[address, '0x' + format(i, '064x')] for i in range(2)]
        self.rows = {'model': [{'id': '0', 'status': 'ok', 'data': '0x',
            'touched': self.keys, 'storage': [[*key, '0x' + '00' * 32] for key in self.keys],
            'events': []}]}

    def test_slot_order_only(self):
        other = copy.deepcopy(self.rows)
        other['model'][0]['touched'].reverse()
        other['model'][0]['storage'].reverse()
        self.assertEqual(canonical_observations(self.rows), canonical_observations(other))

    def test_changed_value_is_observable(self):
        other = copy.deepcopy(self.rows)
        other['model'][0]['storage'][0][2] = '0x' + '01' * 32
        self.assertNotEqual(canonical_observations(self.rows), canonical_observations(other))

    def test_return_bytes_are_observable(self):
        other = copy.deepcopy(self.rows)
        other['model'][0]['data'] = '0x01'
        self.assertNotEqual(canonical_observations(self.rows), canonical_observations(other))

    def test_duplicate_and_missing_slots_rejected(self):
        for duplicate in (False, True):
            other = copy.deepcopy(self.rows)
            rows = other['model'][0]['storage']
            if duplicate:
                rows.append(rows[0])
            else:
                rows.pop()
            with self.assertRaises(HarnessError):
                canonical_observations(other)


if __name__ == '__main__':
    unittest.main()
