#!/usr/bin/env python3
"""Reproduce the exact captured prologue's unsupported memoryguard boundary."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

import generate_ast_bridge as generate
from check_arithmetic import ALLOWED_AXIOMS, check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIN = "f7e4ee0dc8f8d5265ce822a937ab5be771f182e9"
PROLOGUE_PATH = ["subObjects", 0, "code", "block", "statements", 0, "statements", 0]


def render():
    # Also verifies both complete optimized artifact hashes.
    generate.render()
    ast = json.loads((HERE / "MulDivDown.optimized-ast.json").read_text())
    node = generate.get(ast, PROLOGUE_PATH)
    if node["nativeSrc"] != "629:27:0":
        raise SystemExit("unexpected captured prologue source span")
    return "\n".join([
        "-- Generated from the unchanged pinned optimized AST by check_dispatcher_boundary.py.",
        "import TranslationValidationAstDecoder",
        "namespace SolidityTranslationValidation.AstBridge",
        "-- JSON path: " + json.dumps(PROLOGUE_PATH),
        "-- nativeSrc 629:27:0: let _1 := memoryguard(0x80)",
        "def capturedPointerDeclarationJson : Lean.Json := " + generate.quote_json(node),
        "theorem captured_pointer_declaration_rejected :",
        "    decodeDeclaration 20 capturedPointerDeclarationJson =",
        '      .error "unsupported Yul builtin memoryguard" := by rfl',
        "#print axioms captured_pointer_declaration_rejected",
        "end SolidityTranslationValidation.AstBridge", "",
    ])


def main():
    source = HERE / "DispatcherBoundary.lean"
    if source.read_text() != render():
        raise SystemExit("dispatcher-boundary quotation differs from pinned AST")
    dependency = ROOT / ".lake/packages/evmyul"
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=dependency, text=True).strip()
    if actual != PIN:
        raise SystemExit("EVMYulLean pin differs from inspected boundary")
    baseline = check(HERE / "AstDecoder.lean",
                     ROOT / ".lake/build/lib/lean/TranslationValidationAstDecoder.olean")
    if baseline.returncode:
        raise SystemExit(baseline.stdout + baseline.stderr)
    result = check(source)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.AstBridge\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    )
    if len(receipts) != 1 or receipts[0][0] != "captured_pointer_declaration_rejected":
        raise SystemExit("missing dispatcher-boundary rejection receipt")
    if not {x.strip() for x in receipts[0][1].split(",") if x.strip()} <= ALLOWED_AXIOMS:
        raise SystemExit("unexpected dispatcher-boundary axiom")
    print(result.stdout, end="")
    with tempfile.TemporaryDirectory(prefix="dispatcher-boundary-", dir=HERE) as work:
        work = Path(work)
        # This checks native AST vocabulary, independently of our deliberately
        # narrow decoder. There is no native memoryguard operation constructor.
        path = work / "MissingPrimitive.lean"
        path.write_text("import EvmYul.Yul.Ast\n"
                        "example : EvmYul.Operation .Yul := .MEMORYGUARD\n")
        missing = check(path)
        if missing.returncode == 0 or "Unknown constant `EvmYul.Operation.MEMORYGUARD`" not in missing.stdout:
            raise SystemExit("expected native MEMORYGUARD constructor absence was not observed")
        print("native MEMORYGUARD constructor absent at " + PIN)
        # A near miss cannot be silently identified with the captured node.
        path = work / "WrongBuiltin.lean"
        path.write_text(source.read_text().replace('.str "memoryguard"', '.str "calldataload"'))
        mutant = check(path)
        if mutant.returncode == 0 or "rfl" not in mutant.stdout:
            raise SystemExit("changed-prologue rejection receipt was not invalidated")
        print("changed captured builtin invalidates exact rejection theorem")


if __name__ == "__main__":
    main()
