#!/usr/bin/env python3
"""Check pinned AST quotations, kernel decoder/execution proofs, and near misses."""
import copy
import json
from pathlib import Path
import re
import tempfile

import generate_ast_bridge as generate
from check_arithmetic import ALLOWED_AXIOMS, check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    if (HERE / "CapturedNodes.lean").read_text() != generate.render():
        raise SystemExit("captured node quotations differ from pinned artifacts")
    for source, module in [
        ("AstDecoder", "TranslationValidationAstDecoder"),
        ("CapturedNodes", "TranslationValidationCapturedNodes"),
    ]:
        result = check(HERE / (source + ".lean"),
                       ROOT / ".lake/build/lib/lean" / (module + ".olean"))
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    result = check(HERE / "CapturedExecution.lean",
                   ROOT / ".lake/build/lib/lean/TranslationValidationCapturedExecution.olean")
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.AstBridge\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    )
    expected = {"decodeProduct", "decodeQuotient", "decoded_product_executes",
                "decoded_quotient_executes", "captured_quotient_success",
                "decodeProductDeclaration", "exec_captured_product_declaration"}
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing AST bridge axiom receipts")
    for name, axioms in receipts:
        found = {entry.strip() for entry in axioms.split(",") if entry.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axioms for {name}: {found}")
    print(result.stdout, end="")

    guarded = check(HERE / "GuardedExecution.lean")
    if guarded.returncode:
        raise SystemExit(guarded.stdout + guarded.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.AstBridge\.(\w+)' depends on axioms: \[([^]]*)\]",
        guarded.stdout,
    )
    expected = {"eval_overflow_condition", "overflow_guard_passes", "denominator_guard_passes",
                "captured_guarded_prefix_success", "captured_guarded_prefix_continuation",
                "exec_captured_return_store", "exec_captured_return", "captured_arithmetic_body_success",
                "decodeOverflowGuard", "decodeDenominatorGuard", "decodeReturnStore", "decodeReturn"}
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing composed-body axiom receipts")
    for name, axioms in receipts:
        found = {entry.strip() for entry in axioms.split(",") if entry.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axioms for {name}: {found}")
    print(guarded.stdout, end="")

    ast = json.loads((HERE / "MulDivDown.optimized-ast.json").read_text())
    product = generate.get(ast, generate.BODY_PATH + [5, "value"])
    variants = []
    node = copy.deepcopy(product)
    node["nodeType"] = "YulAssignment"
    variants.append((node, 8, "unsupported Yul expression YulAssignment"))
    node = copy.deepcopy(product)
    node["functionName"]["name"] = "sdiv"
    variants.append((node, 8, "unsupported Yul builtin sdiv"))
    node = copy.deepcopy(product)
    node["arguments"].pop()
    variants.append((node, 8, "wrong arity for mul: 1"))
    node = copy.deepcopy(product)
    node["semanticOverride"] = "unchecked"
    variants.append((node, 8, "unknown AST field semanticOverride"))
    node = copy.deepcopy(product)
    node["functionName"]["nodeType"] = "YulLiteral"
    variants.append((node, 8, "Yul callee is not an identifier"))
    variants.append((product, 0, "AST decoding fuel exhausted"))
    node = copy.deepcopy(product)
    node["functionName"]["name"] = "iszero"
    variants.append((node, 8, "wrong arity for iszero: 2"))
    node = copy.deepcopy(product)
    node["functionName"]["name"] = "mstore"
    variants.append((node, 8, "unsupported Yul builtin mstore"))
    literal = generate.get(ast, generate.BODY_PATH + [6, "body", "statements", 0,
                                                   "expression", "arguments", 0])
    for key, value, message in [
        ("kind", "bool", "unsupported Yul literal kind"),
        ("value", "0xg", "invalid Yul numeral digit"),
        ("value", str(2**256), "Yul numeral exceeds one word"),
        ("value", "0x", "empty Yul numeral"),
        ("type", "u256", "unsupported Yul literal type"),
    ]:
        node = copy.deepcopy(literal)
        node[key] = value
        variants.append((node, 8, message))
    with tempfile.TemporaryDirectory(prefix="ast-near-misses-", dir=HERE) as work:
        path = Path(work) / "Rejections.lean"
        lines = ["import TranslationValidationAstDecoder",
                 "open SolidityTranslationValidation.AstBridge",
                 "set_option maxRecDepth 10000"]
        for node, fuel, error in variants:
            lines.append(f"example : decodeExpr {fuel} {generate.quote_json(node)} = "
                         f".error {json.dumps(error)} := by rfl")
        declaration = generate.get(ast, generate.BODY_PATH + [5])
        bad_declarations = []
        node = copy.deepcopy(declaration)
        node["variables"].append(copy.deepcopy(node["variables"][0]))
        bad_declarations.append((node, "expected one Yul declaration variable"))
        node = copy.deepcopy(declaration)
        node["variables"][0]["type"] = "bool"
        bad_declarations.append((node, "unsupported Yul declaration type"))
        node = copy.deepcopy(declaration)
        node["nodeType"] = "YulAssignment"
        bad_declarations.append((node, "unsupported Yul statement"))
        for node, error in bad_declarations:
            lines.append(f"example : decodeDeclaration 8 {generate.quote_json(node)} = "
                         f".error {json.dumps(error)} := by rfl")
        effect_statement = generate.get(ast, generate.BODY_PATH + [8])
        bad_statements = [(effect_statement, 0, "statement decoding fuel exhausted")]
        node = copy.deepcopy(effect_statement)
        node["nodeType"] = "YulFor"
        bad_statements.append((node, 20, "unsupported Yul statement YulFor"))
        node = copy.deepcopy(effect_statement)
        node["expression"]["functionName"]["name"] = "sstore"
        bad_statements.append((node, 20, "unsupported Yul effect sstore"))
        node = copy.deepcopy(effect_statement)
        node["expression"]["arguments"].pop()
        bad_statements.append((node, 20, "wrong effect arity for mstore"))
        for node, fuel, error in bad_statements:
            lines.append(f"example : decodeStmt {fuel} {generate.quote_json(node)} = "
                         f".error {json.dumps(error)} := by rfl")
        path.write_text("\n".join(lines) + "\n")
        rejected = check(path)
        if rejected.returncode:
            raise SystemExit(rejected.stdout + rejected.stderr)
    print(f"{len(variants) + len(bad_declarations) + len(bad_statements)} unsupported/near-miss AST variants "
          "rejected by kernel-checked decoder equations")

    source = (HERE / "GuardedExecution.lean").read_text()
    mutations = {
        "wrong-overflow-disjunction": (
            "UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.ofNat x))",
            "UInt256.isZero (UInt256.land (UInt256.isZero (UInt256.ofNat x))",
        ),
        "wrong-returned-quotient": (
            "let memoryState := shared.toMachineState.mstore (UInt256.ofNat 128) (UInt256.ofNat (x * y / d))",
            "let memoryState := shared.toMachineState.mstore (UInt256.ofNat 128) (UInt256.ofNat (x * y / d + 1))",
        ),
    }
    with tempfile.TemporaryDirectory(prefix="guarded-mutants-", dir=HERE) as work:
        for name, (before, after) in mutations.items():
            if source.count(before) != 1:
                raise SystemExit("mutation anchor is not unique: " + name)
            path = Path(work) / (name + ".lean")
            path.write_text(source.replace(before, after))
            mutant = check(path)
            if mutant.returncode == 0:
                raise SystemExit("incorrect composed-body theorem accepted: " + name)
            if not any(marker in mutant.stdout for marker in ("unsolved goals", "Type mismatch", "rfl", "failed")):
                raise SystemExit(f"unexpected mutant failure: {name}\n{mutant.stdout}{mutant.stderr}")
            print("rejected " + name)

    # Corruption checks use isolated files, never alter the captured artifacts.
    with tempfile.TemporaryDirectory(prefix="ast-corruption-", dir=HERE) as work:
        work = Path(work)
        original_here = generate.HERE
        try:
            generate.HERE = work
            for target in ("MulDivDown.optimized-ast.json", "MulDivDown.optimized.yul"):
                for name in ("MulDivDown.optimized-ast.json", "MulDivDown.optimized.yul"):
                    data = (HERE / name).read_bytes()
                    (work / name).write_bytes(data + (b" " if name == target else b""))
                try:
                    generate.render()
                except ValueError as error:
                    if "artifacts differ" not in str(error):
                        raise
                else:
                    raise SystemExit("corrupted artifact accepted: " + target)
        finally:
            generate.HERE = original_here
    print("both optimized artifact corruption checks rejected; captured arithmetic-body success verified")


if __name__ == "__main__":
    main()
