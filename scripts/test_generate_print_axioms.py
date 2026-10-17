"""Regression: an absent registered module must not vanish from the axiom audit."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import generate_print_axioms as generator


class TrustBoundaryInventoryTests(unittest.TestCase):
    def test_missing_registered_module_fails_generation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            present = root / "Present.lean"
            missing = root / "Absent.lean"
            present.write_text("theorem present : True := True.intro\n")
            with patch.object(generator, "ROOT", root), \
                 patch.object(generator, "TRUST_BOUNDARY_FILES", [present, missing]), \
                 patch.object(generator, "PROOF_DIRS", []):
                with self.assertRaisesRegex(FileNotFoundError, "Absent.lean"):
                    generator.generate()

    def test_directory_cannot_replace_registered_proof_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = root / "Replaced.lean"
            module.mkdir()
            with patch.object(generator, "ROOT", root), \
                 patch.object(generator, "TRUST_BOUNDARY_FILES", [module]), \
                 patch.object(generator, "PROOF_DIRS", []):
                with self.assertRaisesRegex(FileNotFoundError, "Replaced.lean"):
                    generator.generate()


if __name__ == "__main__":
    unittest.main()
