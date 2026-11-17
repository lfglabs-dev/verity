#!/usr/bin/env python3
from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import update_doc_numbers
import verification_metrics


class UpdateDocNumbersTests(unittest.TestCase):
    def test_committed_quick_facts_block_is_empty(self) -> None:
        body = update_doc_numbers.quick_facts_body(update_doc_numbers.LLMS_TXT.read_text(encoding="utf-8"))
        self.assertIsNotNone(body, "llms.txt lost its GENERATED QUICK FACTS markers")
        self.assertEqual(
            body.strip(),
            "",
            "docs-site/public/llms.txt: the quick-facts block is filled at docs build time and must be "
            "committed empty (git checkout docs-site/public/llms.txt after a local npm run build)",
        )

    def test_write_fills_current_foundry_test_count(self) -> None:
        foundry_functions, _ = verification_metrics.get_test_counts()
        with tempfile.TemporaryDirectory() as tmpdir:
            llms = Path(tmpdir) / "llms.txt"
            shutil.copy2(update_doc_numbers.LLMS_TXT, llms)
            result = subprocess.run(
                [sys.executable, str(SCRIPT_DIR / "update_doc_numbers.py"), "--write", "--llms", str(llms)],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            body = update_doc_numbers.quick_facts_body(llms.read_text(encoding="utf-8"))
        self.assertIsNotNone(body)
        self.assertIn(f"- **Tests**: {foundry_functions} Foundry tests, ", body)

    def test_fill_is_idempotent_and_requires_markers(self) -> None:
        metrics = {
            "theorems": {"per_contract": {"Counter": 2}, "total": 2, "categories": 1, "proven": 2},
            "proofs": {"axioms": 0},
            "tests": {"foundry_functions": 10, "property_functions": 3},
            "codebase": {"core_lines": 100},
            "toolchain": {"lean": "leanprover/lean4:v4.31.0"},
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            llms = Path(tmpdir) / "llms.txt"
            llms.write_text(
                "x\n<!-- BEGIN GENERATED QUICK FACTS -->\n<!-- END GENERATED QUICK FACTS -->\ny\n",
                encoding="utf-8",
            )
            self.assertTrue(update_doc_numbers.update_llms_txt(metrics, llms))
            self.assertFalse(update_doc_numbers.update_llms_txt(metrics, llms))
            text = llms.read_text(encoding="utf-8")
            self.assertIn("- **Language**: Lean 4.31.0\n", text)
            self.assertTrue(text.endswith("<!-- END GENERATED QUICK FACTS -->\ny\n"))
            llms.write_text("no markers\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "missing GENERATED QUICK FACTS markers"):
                update_doc_numbers.update_llms_txt(metrics, llms)


if __name__ == "__main__":
    unittest.main()
