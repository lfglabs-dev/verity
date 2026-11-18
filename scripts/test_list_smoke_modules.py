#!/usr/bin/env python3
"""Tests for list_smoke_modules on throwaway test trees."""

from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import list_smoke_modules as tool

SINGLE_LINE = """\
contract A is YulTestBase {
    function setUp() public {
        a = deployCompiledVerityModule("Contracts.Smoke.B", "B", _smokeYulDir());
        _ensureVerityModuleYul("Contracts.Smoke.A", "A", _smokeYulDir());
    }
}
"""

MULTI_LINE = """\
contract C is YulTestBase {
    function setUp() public {
        c = deployCompiledVerityModule(
            "Contracts.Smoke.C",
            "C",
            _smokeYulDir()
        );
        again = deployCompiledVerityModule("Contracts.Smoke.A", "A", _smokeYulDir());
    }
}
"""

IGNORED = """\
contract Base {
    function deployCompiledVerityModule(
        string memory moduleName,
        string memory contractName,
        string memory outDir
    ) internal returns (address) {
        _ensureVerityModuleYul(moduleName, contractName, outDir);
    }
    // deployCompiledVerityModule("Contracts.Commented.Line", "X", d);
    /* _ensureVerityModuleYul("Contracts.Commented.Block", "X", d); */
    string constant URL = "https://example.org"; // keeps the string
}
"""


class ListSmokeModulesTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def run_main(self, min_modules: int = 1) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = tool.main(["--test-dir", str(self.root), "--min-modules", str(min_modules)])
        return code, out.getvalue(), err.getvalue()

    def test_single_line_both_helpers(self) -> None:
        self.write("A.t.sol", SINGLE_LINE)
        self.assertEqual(tool.list_smoke_modules(self.root), ["Contracts.Smoke.A", "Contracts.Smoke.B"])

    def test_multi_line_call_nested_dir_dedupe_sort(self) -> None:
        self.write("A.t.sol", SINGLE_LINE)
        self.write("nested/C.t.sol", MULTI_LINE)
        code, out, err = self.run_main()
        self.assertEqual(code, 0, err)
        self.assertEqual(out, "Contracts.Smoke.A\nContracts.Smoke.B\nContracts.Smoke.C\n")

    def test_non_literal_and_commented_calls_ignored(self) -> None:
        self.write("yul/Base.sol", IGNORED)
        self.assertEqual(tool.list_smoke_modules(self.root), [])

    def test_non_sol_files_ignored(self) -> None:
        self.write("notes.md", SINGLE_LINE)
        self.assertEqual(tool.list_smoke_modules(self.root), [])

    def test_empty_tree_fails_loudly(self) -> None:
        self.write("yul/Base.sol", IGNORED)
        code, out, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertEqual(out, "")
        self.assertIn("found 0 on-demand Verity module(s)", err)

    def test_fewer_than_floor_fails(self) -> None:
        self.write("A.t.sol", SINGLE_LINE)
        code, out, err = self.run_main(min_modules=3)
        self.assertEqual(code, 1)
        self.assertEqual(out, "")
        self.assertIn("found 2 on-demand Verity module(s)", err)
        self.assertIn("expected at least 3", err)

    def test_repository_has_at_least_the_floor(self) -> None:
        # The real test tree: the scan must find at least MIN_MODULES distinct modules
        # (the 26 of the hand-maintained lists it replaced).
        modules = tool.list_smoke_modules(tool.ROOT / "test")
        self.assertEqual(len(modules), len(set(modules)))
        self.assertGreaterEqual(len(modules), tool.MIN_MODULES)
        self.assertGreaterEqual(tool.MIN_MODULES, 26)


if __name__ == "__main__":
    unittest.main()
