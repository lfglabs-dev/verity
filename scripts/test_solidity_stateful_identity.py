"""Concurrent edits and rebuilt Lean artifacts must invalidate replay identity."""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential.engine import HarnessError
from solidity_differential.identity import ImplementationIdentity


class IdentityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.source = self.root / 'Compiler/Test.lean'
        self.source.parent.mkdir()
        self.source.write_text('def value := 1\n')
        self.artifact = self.root / '.lake/build/lib/Compiler/Test.olean'
        self.artifact.parent.mkdir(parents=True)
        self.artifact.write_bytes(b'compiled fixture')
        self.toolchain = self.root / 'toolchain'
        self.old_cwd = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, self.old_cwd)
        self.addCleanup(self.temp.cleanup)
        with patch('solidity_differential.identity.command', side_effect=lambda args:
                   str(self.toolchain) if '--print-prefix' in args else 'test-revision'):
            self.identity = ImplementationIdentity(self.source)

    def test_unchanged(self):
        self.identity.verify()
        self.assertEqual(self.identity.manifest['revision'], 'test-revision')

    def test_source_edit_with_preserved_mtime(self):
        stat = self.source.stat()
        self.source.write_text('def value := 2\n')
        os.utime(self.source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        with self.assertRaisesRegex(HarnessError, 'implementation changed'):
            self.identity.verify()

    def test_replaced_artifact(self):
        replacement = self.artifact.with_suffix('.new')
        replacement.write_bytes(self.artifact.read_bytes())
        replacement.replace(self.artifact)
        with self.assertRaisesRegex(HarnessError, 'implementation changed'):
            self.identity.verify()

    def test_added_module(self):
        (self.source.parent / 'New.lean').write_text('def fresh := 0\n')
        with self.assertRaisesRegex(HarnessError, 'implementation changed'):
            self.identity.verify()

    def test_missing_artifact(self):
        self.artifact.unlink()
        with self.assertRaisesRegex(HarnessError, 'implementation changed'):
            self.identity.verify()


if __name__ == '__main__':
    unittest.main()
