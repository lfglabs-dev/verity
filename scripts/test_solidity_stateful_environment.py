"""Equivalent context programs must agree across variants, not only within A/B/C."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential.check_environment import main


class EnvironmentVariantTests(unittest.TestCase):
    def campaign(self, output, diverge):
        def execute(argv, **kwargs):
            campaign = Path(argv[-1])
            campaign.mkdir()
            value = '0x02' if diverge and campaign.parent.name == 'bindings' else '0x01'
            # All three routes agree locally, even in the bad variant.
            report = {'transactions': [{'id': '0'}], 'observations': {
                route: [{'id': '0', 'data': value}]
                for route in ('source', 'model', 'compiled')}}
            (campaign / 'campaign.json').write_text(json.dumps(report))
        with patch('sys.argv', ['check_environment', '--output', str(output)]), \
             patch('solidity_differential.check_environment.command', side_effect=execute):
            main()

    def test_equivalent_variants_complete(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            self.campaign(output, False)
            self.assertEqual(json.loads((output / 'completed.json').read_text()),
                             ['baseline', 'bindings', 'helpers'])
            self.assertFalse((output / 'metamorphic-divergence.json').exists())

    def test_locally_agreeing_but_changed_variant_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            with self.assertRaisesRegex(RuntimeError, 'changed observable behavior'):
                self.campaign(output, True)
            evidence = json.loads((output / 'metamorphic-divergence.json').read_text())
            self.assertEqual(evidence['variant'], 'bindings')
            self.assertNotEqual(evidence['baseline'], evidence['actual'])
            self.assertEqual(json.loads((output / 'completed.json').read_text()), ['baseline'])


if __name__ == '__main__':
    unittest.main()
