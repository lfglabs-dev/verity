"""Concurrent edits and rebuilt Lean artifacts must invalidate replay identity."""
import os
import subprocess
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
        self.revision = 'test-revision'
        mock_command = patch('solidity_differential.identity.command', side_effect=lambda args:
            str(self.toolchain) if '--print-prefix' in args else self.revision)
        mock_command.start()
        self.addCleanup(mock_command.stop)
        self.identity = ImplementationIdentity(self.source)

    def test_imported_solidity_input_is_hashed_and_edits_rejected(self):
        source = self.root / 'Generated.sol'
        source.write_text('contract Generated { }')
        with patch('solidity_differential.identity.command', side_effect=lambda args:
                   str(self.toolchain) if '--print-prefix' in args else 'test-revision'):
            identity = ImplementationIdentity(self.source, extra_inputs=[source])
        self.assertIn(str(source.resolve()), identity.manifest['files'])
        identity.verify()
        stat = source.stat()
        source.write_text('contract Corrupted { }')
        os.utime(source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        with self.assertRaisesRegex(HarnessError, 'implementation changed'):
            identity.verify()

    def test_missing_imported_solidity_input_invalidates_identity(self):
        source = self.root / 'Generated.sol'
        source.write_text('contract Generated { }')
        with patch('solidity_differential.identity.command', side_effect=lambda args:
                   str(self.toolchain) if '--print-prefix' in args else 'test-revision'):
            identity = ImplementationIdentity(self.source, extra_inputs=[source])
        source.unlink()
        with self.assertRaisesRegex(HarnessError, 'snapshot became unavailable'):
            identity.verify()

    def test_unchanged(self):
        self.identity.verify()
        self.assertEqual(self.identity.manifest['revision'], 'test-revision')

    def test_revision_change_without_source_or_artifact_changes(self):
        self.revision = 'other-revision'
        with self.assertRaisesRegex(HarnessError, 'Git revision changed'):
            self.identity.verify()

    def test_missing_revision_is_an_instrumentation_error(self):
        with patch('solidity_differential.identity.command',
                   side_effect=HarnessError('git HEAD unavailable')):
            with self.assertRaisesRegex(HarnessError, 'HEAD unavailable'):
                self.identity.verify()

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



class GitRevisionTests(unittest.TestCase):
    def test_real_git_head_switch_with_identical_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            def git(*args, data=None):
                return subprocess.check_output(['git', '-C', str(root), *args],
                    input=data, text=True).strip()
            tree = git('mktree', data='')
            # Raw objects are ephemeral Git fixtures, never publication commits.
            def commit(message):
                return git('hash-object', '-t', 'commit', '-w', '--stdin', data=(
                    f'tree {tree}\n'
                    'author Fixture <fixture@example.invalid> 1 +0000\n'
                    'committer Fixture <fixture@example.invalid> 1 +0000\n\n'
                    + message + '\n'))
            first, second = commit('first'), commit('second')
            git('update-ref', 'HEAD', first)
            source = root / 'Driver.lean'
            source.write_text('def unchanged := 1\n')
            old_cwd = Path.cwd()
            try:
                os.chdir(root)
                def command(argv):
                    if '--print-prefix' in argv:
                        return str(root / 'toolchain')
                    return subprocess.check_output(list(map(str, argv)), text=True).strip()
                with patch('solidity_differential.identity.command', side_effect=command), \
                        patch.object(ImplementationIdentity, '_inventory', return_value=[source]):
                    identity = ImplementationIdentity(source)
                    self.assertEqual(identity.manifest['revision'], first)
                    identity.verify()
                    git('update-ref', 'HEAD', second)
                    with self.assertRaisesRegex(HarnessError, 'Git revision changed'):
                        identity.verify()
                    self.assertEqual(source.read_text(), 'def unchanged := 1\n')
            finally:
                os.chdir(old_cwd)

if __name__ == '__main__':
    unittest.main()
