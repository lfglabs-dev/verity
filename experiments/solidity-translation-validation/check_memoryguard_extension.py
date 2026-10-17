#!/usr/bin/env python3
"""Check the explicit memoryguard dialect extension without changing native semantics."""
import copy
import json
import re
import tempfile
from pathlib import Path

import check_dispatcher_boundary as boundary
import check_return_observation
import generate_ast_bridge as generate
from check_arithmetic import ALLOWED_AXIOMS, check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    check_return_observation.main()
    boundary.main()
    for source, module in [("DispatcherBoundary", "TranslationValidationDispatcherBoundary"),
                           ("MemoryGuardExtension", "TranslationValidationMemoryGuardExtension")]:
        result = check(HERE / (source + ".lean"),
                       ROOT / ".lake/build/lib/lean" / (module + ".olean"))
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.AstBridge\.MemoryGuard\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    )
    expected = {"native_conservative", "lowering_preserves_execution", "decode_captured_memoryguard",
                "captured_pointer_binding", "captured_node_executes", "captured_pointer_frame"}
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing memoryguard-extension axiom receipts")
    for name, axioms in receipts:
        found = {x.strip() for x in axioms.split(",") if x.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axioms for {name}: {found}")
    print(result.stdout, end="")
    ast = json.loads((HERE / "MulDivDown.optimized-ast.json").read_text())
    original = generate.get(ast, boundary.PROLOGUE_PATH)
    variants = []
    node = copy.deepcopy(original)
    node["value"]["functionName"]["name"] = "calldataload"
    variants.append((node, "expected memoryguard builtin"))
    node = copy.deepcopy(original)
    node["value"]["arguments"] = []
    variants.append((node, "expected one memoryguard literal"))
    node = copy.deepcopy(original)
    node["value"]["arguments"][0] = {"nodeType": "YulIdentifier", "name": "x", "src": "0:1:0", "nativeSrc": "0:1:0"}
    variants.append((node, "memoryguard requires literal"))
    for key, value, error in [("kind", "string", "unsupported Yul literal kind"),
                              ("value", str(2**256), "Yul numeral exceeds one word"),
                              ("value", "0x", "empty Yul numeral"),
                              ("type", "u256", "unsupported Yul literal type")]:
        node = copy.deepcopy(original)
        node["value"]["arguments"][0][key] = value
        variants.append((node, error))
    node = copy.deepcopy(original)
    node["semanticOverride"] = "identity"
    variants.append((node, "unknown memoryguard AST field semanticOverride"))
    node = copy.deepcopy(original)
    node["variables"].append(copy.deepcopy(node["variables"][0]))
    variants.append((node, "expected one memoryguard binding"))
    node = copy.deepcopy(original)
    node["variables"][0]["name"] = ""
    variants.append((node, "empty memoryguard binding"))
    with tempfile.TemporaryDirectory(prefix="memoryguard-rejections-", dir=HERE) as work:
        path = Path(work) / "Rejections.lean"
        lines = ["import TranslationValidationMemoryGuardExtension",
                 "open SolidityTranslationValidation.AstBridge.MemoryGuard",
                 "set_option maxRecDepth 10000"]
        for node, error in variants:
            lines.append(f"example : decodeDeclaration {generate.quote_json(node)} = "
                         f".error {json.dumps(error)} := by rfl")
        path.write_text("\n".join(lines) + "\n")
        result = check(path)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    print(f"{len(variants)} memoryguard near misses rejected by kernel-checked equations")
    source = (HERE / "MemoryGuardExtension.lean").read_text()
    mutants = {
        "wrong-memoryguard-value": ("=> .ok (state.insert name literal)",
                                    "=> .ok (state.insert name (UInt256.add literal (UInt256.ofNat 1)))"),
        "wrong-lowered-value": ("=> .Let [name] (some (.Lit literal))",
                                "=> .Let [name] (some (.Lit (UInt256.ofNat 0)))"),
        "native-fuel-changed": ("=> Yul.exec (fuel + 1) statement code state",
                                "=> Yul.exec (fuel + 2) statement code state"),
    }
    with tempfile.TemporaryDirectory(prefix="memoryguard-mutants-", dir=HERE) as work:
        for name, (before, after) in mutants.items():
            if source.count(before) != 1:
                raise SystemExit("nonunique mutation anchor: " + name)
            path = Path(work) / (name + ".lean")
            path.write_text(source.replace(before, after))
            result = check(path)
            if result.returncode == 0 or not any(x in result.stdout for x in ("unsolved goals", "rfl", "failed", "Type mismatch")):
                raise SystemExit(f"unexpected memoryguard mutation result {name}:\n{result.stdout}{result.stderr}")
            print("rejected " + name)


if __name__ == "__main__":
    main()
