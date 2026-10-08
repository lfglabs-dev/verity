"""Prevent source/provenance substitution in the pinned IdLib hash campaign."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from solidity_differential.check_abi_hashing import validate_dependencies


class HashingIdentityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.fixture = Path(self.temp.name)
        source = Path(__file__).resolve().parents[1] / 'Contracts/SolidityImportSmoke/pinned-midnight'
        shutil.copytree(source, self.fixture / 'pinned-midnight')

    def test_exact_pin(self):
        validate_dependencies(self.fixture)

    def test_source_tampering(self):
        path = self.fixture / 'pinned-midnight/libraries/IdLib.sol'
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            validate_dependencies(self.fixture)

    def test_manifest_hash_cannot_authorize_tampering(self):
        import hashlib
        root = self.fixture / 'pinned-midnight'
        path = root / 'libraries/IdLib.sol'
        path.write_bytes(path.read_bytes() + b'\n')
        manifest = root / 'hashing-provenance.json'
        record = json.loads(manifest.read_text())
        record['files']['libraries/IdLib.sol']['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        manifest.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'provenance differs'):
            validate_dependencies(self.fixture)

    def test_commit_substitution(self):
        manifest = self.fixture / 'pinned-midnight/hashing-provenance.json'
        record = json.loads(manifest.read_text())
        record['commit'] = '0' * 40
        manifest.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'pin differs'):
            validate_dependencies(self.fixture)


if __name__ == '__main__':
    unittest.main()
