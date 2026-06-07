#!/usr/bin/env python3
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

import check_layer_import_boundaries as checker


class CheckLayerImportBoundariesTests(unittest.TestCase):
    def _run_check(self, files: dict[str, str]) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            for rel_path, contents in files.items():
                path = root / rel_path
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents, encoding="utf-8")

            rules = tuple(
                checker.ImportRule(
                    name=rule.name,
                    root=root / rule.root.relative_to(checker.ROOT),
                    forbidden=rule.forbidden,
                    message=rule.message,
                    allowed_imports=rule.allowed_imports,
                    allowed_path_imports=rule.allowed_path_imports,
                )
                for rule in checker.RULES
            )

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = checker.main_for_rules(rules)
            return rc, stdout.getvalue(), stderr.getvalue()

    def test_accepts_allowed_macro_compiler_imports(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Macro/Types.lean": (
                    "import Compiler.CompilationModel.Types\n"
                    "import Compiler.Selectors\n"
                    "import Compiler.ECM\n"
                    "import Verity.Macro.Syntax\n"
                    "import Verity.Core\n"
                )
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Layer import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_macro_importing_general_compiler_code(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Macro/Types.lean": "import Compiler.Modules.ERC20\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("macro-to-compiler", stderr)
        self.assertIn("Compiler.Modules.ERC20", stderr)

    def test_allows_current_translate_legacy_choke_point(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Macro/Translate.lean": "import Compiler.Modules.ERC20\n",
                "Verity/Macro/Translate/Expr.lean": "import Compiler.Keccak.Sponge\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Layer import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_compilation_model_importing_macro_code(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/CompilationModel/Types.lean": "import Verity.Macro.Translate\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertIn("compilationmodel-no-macro", stderr)

    def test_accepts_ir_generation_bridge_imports(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Proofs/IRGeneration/FunctionBody.lean": (
                    "import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas\n"
                    "import Compiler.Proofs.YulGeneration.IRFuel\n"
                )
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Layer import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_ir_generation_importing_native_backend_proofs(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Proofs/IRGeneration/FunctionBody.lean": (
                    "import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness\n"
                )
            }
        )
        self.assertEqual(rc, 1)
        self.assertIn("ir-proofs-no-native-backend", stderr)
        self.assertIn("EvmYulLeanNativeHarness", stderr)

    def test_rejects_yul_generation_importing_macro_syntax(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Proofs/YulGeneration/RuntimeTypes.lean": "import Verity.Macro.Syntax\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertIn("yul-proofs-no-macro", stderr)

    def test_quarantines_test_modules(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Proofs/YulGeneration/BridgeTest.lean": "import Verity.Macro.Syntax\n",
                "Compiler/Proofs/IRGeneration/FunctionBodyTest.lean": (
                    "import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness\n"
                ),
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Layer import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_ignores_comment_decoys(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/CompilationModel/Types.lean": "-- import Verity.Macro.Translate\n",
                "Compiler/Proofs/YulGeneration/RuntimeTypes.lean": "/- import Verity.Macro.Syntax -/\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Layer import boundary check passed.", stdout)
        self.assertEqual(stderr, "")


if __name__ == "__main__":
    unittest.main()
