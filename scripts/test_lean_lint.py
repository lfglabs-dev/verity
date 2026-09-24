"""Tests for lean_lint.py (P7 Cluster E consolidation)."""

from __future__ import annotations

import importlib
import unittest
from unittest import mock

import lean_lint


class TestRuleRegistry(unittest.TestCase):
    def test_expected_rules_registered(self) -> None:
        self.assertEqual(
            set(lean_lint.RULES),
            {
                "contract_structure",
                "paths",
                "compilationmodel_split",
                "axioms",
                "trust_surface_registry",
                "storage_layout",
                "lean_hygiene",
                "split_compiler_test_artifacts",
                "rewrite_proof_metadata",
                "proof_length",
            },
        )

    def test_rule_modules_expose_main(self) -> None:
        for module_name in lean_lint.RULES.values():
            module = importlib.import_module(module_name)
            self.assertTrue(callable(module.main), module_name)


class TestDispatch(unittest.TestCase):
    def test_rejects_unknown_rule(self) -> None:
        with self.assertRaises(SystemExit) as ctx:
            lean_lint.main(["--only", "nonsense"])
        self.assertEqual(ctx.exception.code, 2)

    def test_forwarded_args_require_single_only(self) -> None:
        with self.assertRaises(SystemExit) as ctx:
            lean_lint.main(["--format=markdown"])
        self.assertEqual(ctx.exception.code, 2)

    def test_stops_at_first_failing_rule(self) -> None:
        calls: list[str] = []

        def fake_run(name: str, extra_args=None) -> int:
            calls.append(name)
            return 1 if name == "paths" else 0

        with mock.patch.object(lean_lint, "run_rule", side_effect=fake_run):
            rc = lean_lint.main([])
        self.assertEqual(rc, 1)
        self.assertEqual(calls, ["contract_structure", "paths"])

    def test_skip_excludes_rule(self) -> None:
        calls: list[str] = []
        with mock.patch.object(
            lean_lint, "run_rule", side_effect=lambda name, extra_args=None: calls.append(name) or 0
        ):
            rc = lean_lint.main(["--skip", "proof_length"])
        self.assertEqual(rc, 0)
        self.assertNotIn("proof_length", calls)
        self.assertEqual(len(calls), len(lean_lint.RULES) - 1)

    def test_run_rule_converts_system_exit(self) -> None:
        fake_module = mock.Mock()
        fake_module.main.side_effect = SystemExit(1)
        with mock.patch.object(lean_lint.importlib, "import_module", return_value=fake_module):
            self.assertEqual(lean_lint.run_rule("paths"), 1)
        fake_module.main.side_effect = SystemExit(None)
        with mock.patch.object(lean_lint.importlib, "import_module", return_value=fake_module):
            self.assertEqual(lean_lint.run_rule("paths"), 0)


if __name__ == "__main__":
    unittest.main()
