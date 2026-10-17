"""Reject source drift and check complete transaction inputs before execution."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential import check_midnight_admin as campaign
from solidity_differential.engine import HarnessError


class MidnightInputs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        (self.root / 'src').mkdir()
        (self.root / 'src/Midnight.sol').write_text('contract Midnight {}\n')
        self.git('add', 'src')
        tree = self.git('write-tree')
        # Ephemeral raw Git objects, never publication commits.
        commit = self.git('hash-object', '-t', 'commit', '-w', '--stdin', data=(
            f'tree {tree}\nauthor Fixture <test@example.invalid> 1 +0000\n'
            'committer Fixture <test@example.invalid> 1 +0000\n\nfixture\n'))
        self.git('update-ref', 'HEAD', commit)
        pin = patch.object(campaign, 'PIN', commit)
        pin.start()
        self.addCleanup(pin.stop)

    def git(self, *args, data=None):
        return subprocess.check_output(['git', '-C', str(self.root), *args],
            input=data, text=True).strip()

    def test_exact_source_and_tracked_edit(self):
        sources, _ = campaign.pinned_sources(self.root)
        self.assertEqual(sources['src/Midnight.sol']['content'], 'contract Midnight {}\n')
        (self.root / 'src/Midnight.sol').write_text('contract Changed {}\n')
        with self.assertRaisesRegex(HarnessError, 'dirty'):
            campaign.pinned_sources(self.root)

    def test_untracked_production_input_is_rejected(self):
        (self.root / 'src/Injected.sol').write_text('contract Injected {}\n')
        with self.assertRaisesRegex(HarnessError, 'dirty'):
            campaign.pinned_sources(self.root)

    def test_wrong_revision_is_rejected(self):
        with patch.object(campaign, 'PIN', '0' * 40):
            with self.assertRaisesRegex(HarnessError, 'revision'):
                campaign.pinned_sources(self.root)

    def test_transactions_reproduce_and_retain_complete_payload(self):
        target = '0x' + '12' * 20
        rows = campaign.transactions_for(64, 7, target)
        self.assertEqual(rows, campaign.transactions_for(64, 7, target))
        self.assertNotEqual(rows, campaign.transactions_for(64, 8, target))
        self.assertEqual(len({row['id'] for row in rows}), 64)
        self.assertEqual({row['function'] for row in rows},
                         {s.split('(')[0] for s in campaign.SIGNATURES})
        for row in rows:
            data = bytes.fromhex(row['data'][2:])
            self.assertEqual([int.from_bytes(data[i:i + 32], 'big')
                              for i in range(4, len(data), 32)], row['args'])
            self.assertEqual(row['target'], target)
        # A reduced sequence preserves the original environment and calldata.
        self.assertEqual(rows[12]['blockNumber'], 14)
        self.assertEqual(rows[12]['sender'], campaign.SENDERS[1])

    def test_deterministic_prefix_cannot_be_truncated(self):
        with self.assertRaisesRegex(HarnessError, 'at least 20'):
            campaign.transactions_for(19, 7, '0x' + '12' * 20)


if __name__ == '__main__':
    unittest.main()
