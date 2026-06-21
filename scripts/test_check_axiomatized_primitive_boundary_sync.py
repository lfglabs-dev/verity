from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import docsync


class AxiomatizedPrimitiveBoundarySyncTests(unittest.TestCase):
    def _write_fixture_tree(
        self,
        root: Path,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> None:
        matrix = {
            "expr_features": [
                {
                    "feature": "keccak256",
                    "proof_status": proof_status,
                    "SourceInterpreter_basic": basic_status,
                    "SourceInterpreter_fuel": fuel_status,
                }
            ],
            "stmt_features": [],
        }
        feature_matrix = root / "artifacts" / "interpreter_feature_matrix.json"
        feature_matrix.parent.mkdir(parents=True, exist_ok=True)
        feature_matrix.write_text(json.dumps(matrix), encoding="utf-8")

        edsl_path = root / "docs-site" / "content" / "edsl" / "external-calls.mdx"
        edsl_path.parent.mkdir(parents=True, exist_ok=True)
        edsl_path.write_text(edsl_doc, encoding="utf-8")

        compiler_path = root / "docs-site" / "content" / "compiler.mdx"
        compiler_path.parent.mkdir(parents=True, exist_ok=True)
        compiler_path.write_text(compiler_doc, encoding="utf-8")

        guide_path = root / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx"
        guide_path.parent.mkdir(parents=True, exist_ok=True)
        guide_path.write_text(solidity_guide, encoding="utf-8")

    def _run_check(
        self,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(
                root,
                proof_status=proof_status,
                basic_status=basic_status,
                fuel_status=fuel_status,
                edsl_doc=edsl_doc,
                compiler_doc=compiler_doc,
                solidity_guide=solidity_guide,
            )

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = docsync.run_entry("axiomatized_primitive_boundary", root=root)
            return rc, stdout.getvalue() + stderr.getvalue()
