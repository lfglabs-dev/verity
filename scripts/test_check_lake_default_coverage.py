#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_lake_default_coverage as check


def _tree(root: Path, lakefile: str, files: dict[str, str]) -> None:
    (root / "lakefile.lean").write_text(textwrap.dedent(lakefile))
    for rel, body in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body)


FILES = {
    "Verity.lean": "import Verity.Core\n",
    "Verity/Core.lean": "-- import Verity.Commented\n",
    "Verity/Commented.lean": "",
    "Contracts/Smoke/A.lean": "import Contracts.Smoke.B\n",
    "Contracts/Smoke/B.lean": "",
    "Contracts/Orphan.lean": "",
}


class LakeDefaultCoverageTests(unittest.TestCase):
    def _uncovered(self, lakefile: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _tree(root, lakefile, FILES)
            return check.uncovered_modules(root)

    def test_non_default_library_is_not_built(self) -> None:
        # The Contracts library exists but is not a default target: none of it is built.
        missing = self._uncovered("""
            @[default_target]
            lean_lib «Verity» where
              globs := #[.one `Verity]

            lean_lib «Contracts» where
              globs := #[.andSubmodules `Contracts.Smoke]
            """)
        self.assertEqual(missing, ["Contracts.Orphan", "Contracts.Smoke.A",
                                   "Contracts.Smoke.B", "Verity.Commented"])

    def test_full_coverage_is_silent(self) -> None:
        missing = self._uncovered("""
            @[default_target]
            lean_lib «Verity» where
              globs := #[.one `Verity, .one `Verity.Commented]

            @[default_target]
            lean_lib «Contracts» where
              globs := #[.submodules `Contracts.Smoke, .one `Contracts.Orphan]
            """)
        self.assertEqual(missing, [])

    def test_transitive_import_counts_and_comment_does_not(self) -> None:
        # Contracts.Smoke.B is covered only through A's import; Verity.Commented is only
        # mentioned in a comment, so it stays uncovered.
        missing = self._uncovered("""
            @[default_target]
            lean_lib «Verity» where
              globs := #[.one `Verity]

            @[default_target]
            lean_lib «Contracts» where
              globs := #[.one `Contracts.Smoke.A, .one `Contracts.Orphan]
            """)
        self.assertEqual(missing, ["Verity.Commented"])

    def test_main_reports_and_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _tree(root, """
                @[default_target]
                lean_lib «Verity» where
                """, FILES)
            self.assertEqual(check.main(["--root", str(root)]), 1)


if __name__ == "__main__":
    unittest.main()
