#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_trust_surface_registry


class CheckTrustSurfaceRegistryTests(unittest.TestCase):
    def test_collects_mechanisms_and_ecm_axioms(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True)
            (root / "Compiler" / "A.lean").write_text(
                "\n".join(
                    [
                        "@[implemented_by fastFoo]",
                        "def foo : True := by native_decide",
                        "partial def walk : Nat -> Nat | n => n",
                        'def mod where axioms := ["external_surface"]',
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            mechanisms, ecm_axioms = check_trust_surface_registry.collect_trust_surface(root)

        self.assertEqual(mechanisms["native_decide"], 1)
        self.assertEqual(mechanisms["@[implemented_by"], 1)
        self.assertEqual(mechanisms["partial def"], 1)
        self.assertEqual(ecm_axioms, {"external_surface": ("Compiler/A.lean", 4)})

    def test_collects_benchmark_tree_when_present(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Benchmark").mkdir(parents=True)
            (root / "Benchmark" / "Case.lean").write_text(
                'def mod where axioms := ["benchmark_external_surface"]\n',
                encoding="utf-8",
            )

            _, ecm_axioms = check_trust_surface_registry.collect_trust_surface(root)

        self.assertEqual(
            ecm_axioms,
            {"benchmark_external_surface": ("Benchmark/Case.lean", 1)},
        )


if __name__ == "__main__":
    unittest.main()
