"""Cache lifecycle/provenance controls; real cold/warm campaigns remain separate."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential.denote import SequenceAdapter
from solidity_differential.engine import HarnessError


class Identity:
    def verify(self):
        pass


class CachedDenoteTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.driver = self.root / 'Driver.lean'
        self.driver.write_text('def main : IO Unit := pure ()\n')
        self.commands = []
        self.adapter = SequenceAdapter(self.root / 'B', self.driver,
            '0x' + '12' * 20, identity=Identity(), cached_driver=True)

    def command(self, argv, **kwargs):
        self.commands.append(list(map(str, argv)))
        if '-o' in argv:
            Path(argv[argv.index('-o') + 1]).write_bytes(b'compiled driver')
            Path(kwargs['log']).write_text('compiled\n')
            return ''
        if argv[-2:] == ['printenv', 'LEAN_PATH']:
            return '/existing/lean/modules\n'
        raise AssertionError(argv)

    def prepare(self):
        with patch('solidity_differential.denote.command', self.command):
            return self.adapter._cached_command()

    def test_compiles_once_and_records_exact_original_source(self):
        first = self.prepare()
        self.assertEqual(first, self.prepare())
        self.assertEqual(len(self.commands), 2)
        cache = self.adapter.cache
        source = next(p for p in cache['paths'] if p.name != 'Replay.lean' and p.suffix == '.lean')
        self.assertEqual(source.read_bytes(), self.driver.read_bytes())
        manifest = json.loads((cache['directory'] / 'manifest.json').read_text())
        self.assertEqual(manifest['originalDriverSha256'], self.adapter.digest)
        self.assertEqual(manifest['files'], cache['hashes'])
        self.assertIn('/existing/lean/modules', str(first))
        self.assertTrue((cache['directory'] / 'Replay.lean').read_text().startswith('import SolidityDenoteCache'))

    def test_original_driver_edit_invalidates_cache(self):
        self.prepare()
        self.driver.write_text('def main : IO Unit := IO.println "changed"\n')
        with self.assertRaisesRegex(HarnessError, 'model driver changed'):
            self.prepare()

    def test_cached_artifact_edit_or_removal_invalidates_cache(self):
        self.prepare()
        artifact = next(p for p in self.adapter.cache['paths'] if p.suffix == '.olean')
        artifact.write_bytes(b'changed artifact')
        with self.assertRaisesRegex(HarnessError, 'cached Lean driver changed'):
            self.prepare()
        artifact.unlink()
        with self.assertRaisesRegex(HarnessError, 'cached Lean driver changed'):
            self.prepare()

    def test_cached_wrapper_edit_invalidates_cache(self):
        self.prepare()
        (self.adapter.cache['directory'] / 'Replay.lean').write_text('import AnotherModule\n')
        with self.assertRaisesRegex(HarnessError, 'cached Lean driver changed'):
            self.prepare()

    def test_added_shadow_module_invalidates_cache(self):
        self.prepare()
        (self.adapter.cache['directory'] / 'Shadow.olean').write_bytes(b'shadow')
        with self.assertRaisesRegex(HarnessError, 'cached Lean driver changed'):
            self.prepare()

    def test_failed_compilation_does_not_become_cache_success(self):
        with patch('solidity_differential.denote.command', side_effect=HarnessError('compile failed')):
            with self.assertRaisesRegex(HarnessError, 'compile failed'):
                self.adapter._cached_command()
        self.assertIsNone(self.adapter.cache)

    def test_missing_compiler_artifact_is_failure(self):
        with patch('solidity_differential.denote.command', return_value=''):
            with self.assertRaisesRegex(HarnessError, 'artifact missing'):
                self.adapter._cached_command()
        self.assertIsNone(self.adapter.cache)


if __name__ == '__main__':
    unittest.main()
