"""All three routes must receive the encoder's complete ABI payload."""
import hashlib
import sys
import types
import unittest
from unittest.mock import patch

from solidity_differential.cases import materialize


class FullCalldataCasesTests(unittest.TestCase):
    def setUp(self):
        self.abi = {'name': 'f', 'inputs': [
            {'name': 'm', 'type': 'tuple', 'components': [
                {'name': 'unused', 'type': 'uint256'},
                {'name': 'items', 'type': 'uint128[]'},
                {'name': 'maturity', 'type': 'uint256'}]},
            {'name': 'user', 'type': 'address'}]}
        self.metadata = {'params': ['m', 'user'], 'projections': []}
        self.config = {'arguments': {'m.maturity': 'maturity', 'user': 'user'}}
        self.values = {'maturity': 51, 'user': 7}

    def materialize(self, payload):
        # The independent eth_abi encoder is the boundary under test here.
        # Runtime A/B/C campaigns exercise that actual encoder separately.
        encoder = types.SimpleNamespace(encode=lambda _types, _values: payload)
        with patch.dict(sys.modules, {'eth_abi': encoder}), patch(
                'solidity_differential.cases.keccak',
                side_effect=lambda data: hashlib.sha256(data).digest()):
            return materialize(self.config, self.metadata, self.abi, {}, self.values, 'tuple')

    def test_dynamic_tail_is_preserved_on_all_routes(self):
        words = [64, 7, 123, 96, 51, 2, 5, 9]
        payload = b''.join(n.to_bytes(32, 'big') for n in words)
        case = self.materialize(payload)
        self.assertEqual(case['args'], [str(n) for n in words])
        self.assertEqual(bytes.fromhex(case['sourceCalldata'][2:])[4:], payload)
        self.assertEqual(bytes.fromhex(case['compiledCalldata'][2:]),
                         bytes.fromhex('12345678') + payload)

    def test_stale_projection_is_rejected(self):
        self.metadata['projections'] = [{'parameter': 'm', 'member': 'maturity',
                                        'modelParam': 'm_maturity'}]
        with self.assertRaisesRegex(ValueError, 'projected ABI metadata'):
            self.materialize(bytes(32))

    def test_parameter_identity_mismatch_is_rejected(self):
        self.metadata['params'] = ['m_maturity', 'user']
        with self.assertRaisesRegex(ValueError, 'parameter identities differ'):
            self.materialize(bytes(32))

    def test_partial_encoder_word_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'complete words'):
            self.materialize(bytes(33))


if __name__ == '__main__':
    unittest.main()
