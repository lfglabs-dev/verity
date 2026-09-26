"""Mutation snapshots retain the source revision independently of output location."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential.mutations import snapshot


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def initialize(root, content):
    root.mkdir()
    git(root, 'init', '-q')
    (root / 'source.lean').write_text(content)
    (root / 'deleted.lean').write_text('tracked, then deleted')
    git(root, 'add', '.')
    git(root, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
        'commit', '-qm', 'fixture')
    return git(root, 'rev-parse', 'HEAD')


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = self.root / 'candidate'
        self.head = initialize(self.source, 'def value := 1')
        (self.source / 'source.lean').write_text('def value := 2')
        (self.source / 'deleted.lean').unlink()
        (self.source / 'untracked.lean').write_text('def extra := 3')
        cache = self.source / '.lake'
        (cache / 'packages').mkdir(parents=True)
        (cache / 'build').mkdir()
        (cache / 'build/test.olean').write_bytes(b'original cache')
        (cache / 'solidity-import').mkdir()
        (cache / 'solidity-import/solc-0.8.34').write_bytes(b'test solc')
        (self.source / '.git/info/exclude').write_text('.lake/\n')

    def check_snapshot(self, destination):
        with patch('solidity_differential.mutations.ROOT', self.source), \
             patch('solidity_differential.mutations.WORKSPACE', self.source):
            snapshot(destination)
        self.assertEqual(git(destination, 'rev-parse', 'HEAD'), self.head)
        self.assertEqual(Path(git(destination, 'rev-parse', '--show-toplevel')), destination)
        self.assertEqual((destination / 'source.lean').read_text(), 'def value := 2')
        self.assertEqual((destination / 'untracked.lean').read_text(), 'def extra := 3')
        self.assertFalse((destination / 'deleted.lean').exists())
        (destination / '.lake/build/test.olean').write_bytes(b'mutated cache')
        self.assertEqual((self.source / '.lake/build/test.olean').read_bytes(), b'original cache')
        self.assertIn('deleted.lean', git(destination, 'ls-files'))

    def test_external_output_has_own_revision(self):
        self.check_snapshot(self.root / 'external-output')

    def test_output_inside_unrelated_repository_uses_source_revision(self):
        unrelated = self.root / 'unrelated'
        other_head = initialize(unrelated, 'different repository')
        self.assertNotEqual(other_head, self.head)
        self.check_snapshot(unrelated / 'output')


if __name__ == '__main__':
    unittest.main()
