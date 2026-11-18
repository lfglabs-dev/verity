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

    def run_main(self) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = tool.main(["--test-dir", str(self.root)])
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
        self.assertIn("no on-demand Verity module", err)


if __name__ == "__main__":
    unittest.main()
