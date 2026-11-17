#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import update_doc_numbers

METRICS = {
    "theorems": {"per_contract": {"Counter": 2}, "total": 2, "categories": 1, "proven": 2},
    "proofs": {"axioms": 0},
    "tests": {"foundry_functions": 10, "property_functions": 3},
    "codebase": {"core_lines": 100},
    "toolchain": {"lean": "leanprover/lean4:v4.31.0"},
}


class UpdateDocNumbersTests(unittest.TestCase):
    def test_committed_template_quick_facts_block_is_empty(self) -> None:
        body = update_doc_numbers.quick_facts_body(update_doc_numbers.LLMS_TEMPLATE.read_text(encoding="utf-8"))
        self.assertIsNotNone(body, "llms.template.txt lost its GENERATED QUICK FACTS markers")
        self.assertEqual(body.strip(), "", "llms.template.txt: the quick-facts block must be committed empty")

    def test_rendered_llms_txt_is_ignored_build_output(self) -> None:
        root = update_doc_numbers.ROOT
        if not (root / ".git").exists():
            self.skipTest("not a git checkout")
        rel = str(update_doc_numbers.LLMS_TXT.relative_to(root))
        tracked = subprocess.run(["git", "-C", str(root), "ls-files", "--error-unmatch", rel], capture_output=True, check=False)
        self.assertNotEqual(tracked.returncode, 0, f"{rel} must not be committed")
        ignored = subprocess.run(["git", "-C", str(root), "check-ignore", "-q", rel], check=False)
        self.assertEqual(ignored.returncode, 0, f"{rel} must be git-ignored")

    def test_write_renders_template_with_injected_metrics(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            template = Path(tmpdir) / "llms.template.txt"
            output = Path(tmpdir) / "public" / "llms.txt"
            template.write_text(update_doc_numbers.LLMS_TEMPLATE.read_text(encoding="utf-8"), encoding="utf-8")
            saved = update_doc_numbers.current_metrics
            update_doc_numbers.current_metrics = lambda: METRICS
            try:
                update_doc_numbers.main(["--write", "--template", str(template), "--output", str(output)])
            finally:
                update_doc_numbers.current_metrics = saved
            body = update_doc_numbers.quick_facts_body(output.read_text(encoding="utf-8"))
            self.assertEqual(update_doc_numbers.quick_facts_body(template.read_text(encoding="utf-8")).strip(), "")
        self.assertIsNotNone(body)
        self.assertIn("- **Tests**: 10 Foundry tests, 3 property tests\n", body)
        self.assertIn("- **Language**: Lean 4.31.0\n", body)

    def test_render_is_idempotent_and_requires_markers(self) -> None:
        template = "x\n<!-- BEGIN GENERATED QUICK FACTS -->\n<!-- END GENERATED QUICK FACTS -->\ny\n"
        once = update_doc_numbers.render_llms_txt(template, METRICS)
        self.assertEqual(update_doc_numbers.render_llms_txt(once, METRICS), once)
        self.assertTrue(once.endswith("<!-- END GENERATED QUICK FACTS -->\ny\n"))
        with self.assertRaisesRegex(ValueError, "missing GENERATED QUICK FACTS markers"):
            update_doc_numbers.render_llms_txt("no markers\n", METRICS)


if __name__ == "__main__":
    unittest.main()
