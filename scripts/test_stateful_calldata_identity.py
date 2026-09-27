"""Reject A/B payload mismatches before invoking the stateful Denote runner."""
import unittest
from solidity_differential.denote import _calldata
from solidity_differential.engine import HarnessError

class StatefulCalldataIdentityTests(unittest.TestCase):
    def test_dynamic_tail_and_selector(self):
        words = [32, 64, 9, 2, 7, 8]
        tx = {'args': words, 'data': '0xdeadbeef' + ''.join(f'{w:064x}' for w in words)}
        self.assertEqual(_calldata(tx), str(0xdeadbeef))

    def test_zero_arguments(self):
        self.assertEqual(_calldata({'args': [], 'data': '0x00000000'}), '0')

    def test_different_word_rejected(self):
        with self.assertRaisesRegex(HarnessError, 'differs'):
            _calldata({'args': [2], 'data': '0x12345678' + f'{1:064x}'})

    def test_partial_word_rejected(self):
        with self.assertRaisesRegex(HarnessError, 'word-aligned'):
            _calldata({'args': [], 'data': '0x1234567800'})

    def test_missing_selector_rejected(self):
        with self.assertRaisesRegex(HarnessError, 'word-aligned'):
            _calldata({'args': [], 'data': '0x123456'})

    def test_boolean_is_not_a_word(self):
        with self.assertRaisesRegex(HarnessError, 'differs'):
            _calldata({'args': [True], 'data': '0x12345678' + f'{1:064x}'})
