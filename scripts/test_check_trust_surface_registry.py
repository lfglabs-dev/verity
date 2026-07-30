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
    def _write_valid_string_boundary(self, root: Path) -> None:
        boundary = root / check_trust_surface_registry.LEAN431_STRING_FACTS
        boundary.parent.mkdir(parents=True, exist_ok=True)
        boundary.write_text(
            "\n".join(
                [
                    "theorem compatScratch_startsWith_reserved : True := by trivial",
                    "theorem compatScratch_not_internalImmutable : True := by trivial",
                ]
            )
            + "\n",
            encoding="utf-8",
        )

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

    def test_collects_multiline_ecm_axioms(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True)
            (root / "Compiler" / "A.lean").write_text(
                "\n".join(
                    [
                        "def mod where",
                        "  axioms := [",
                        '    "first_surface",',
                        '    "second_surface"',
                        "  ]",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            _, ecm_axioms = check_trust_surface_registry.collect_trust_surface(root)

        self.assertEqual(
            ecm_axioms,
            {
                "first_surface": ("Compiler/A.lean", 2),
                "second_surface": ("Compiler/A.lean", 2),
            },
        )

    def test_accepts_exact_lean431_string_kernel_facts(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_valid_string_boundary(root)

            errors = check_trust_surface_registry.check_lean431_string_kernel_facts(root)

        self.assertEqual(errors, [])

    def test_rejects_native_decide_in_compiler_proofs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_valid_string_boundary(root)
            proof = root / "Compiler" / "Proofs" / "Bad.lean"
            proof.parent.mkdir(parents=True)
            proof.write_text("theorem bad : True := by native_decide\n", encoding="utf-8")

            errors = check_trust_surface_registry.check_lean431_string_kernel_facts(root)

        self.assertTrue(any("outside non-test Compiler/Proofs" in error for error in errors))

    def test_rejects_relocated_string_boundary_theorem(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_valid_string_boundary(root)
            duplicate = root / "Compiler" / "Elsewhere.lean"
            duplicate.write_text(
                "theorem compatScratch_startsWith_reserved : True := by trivial\n",
                encoding="utf-8",
            )

            errors = check_trust_surface_registry.check_lean431_string_kernel_facts(root)

        self.assertTrue(
            any("compatScratch_startsWith_reserved" in error for error in errors)
        )


if __name__ == "__main__":
    unittest.main()
