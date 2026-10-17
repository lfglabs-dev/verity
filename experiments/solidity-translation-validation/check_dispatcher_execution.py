#!/usr/bin/env python3
"""Check exact dispatcher decoding and the successful ABI branch byte theorem."""
import argparse
import copy
import json
import re
import tempfile
from pathlib import Path

import check_memoryguard_extension
import generate_ast_bridge as base
import generate_dispatcher_bridge as generate
from check_arithmetic import ALLOWED_AXIOMS, check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def audit(result, expected):
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    receipts = re.findall(r"'SolidityTranslationValidation\.AstBridge\.Dispatcher\.(\w+)' depends on axioms: \[([^]]*)\]", result.stdout)
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing dispatcher receipts")
    for name, axioms in receipts:
        if not {x.strip() for x in axioms.split(",") if x.strip()} <= ALLOWED_AXIOMS:
            raise SystemExit("unexpected dispatcher axiom: " + name)
    print(result.stdout, end="")


def check_dispatcher():
    if (HERE / "DispatcherNodes.lean").read_text() != generate.render():
        raise SystemExit("dispatcher quotation differs from pinned AST")
    for name in ["ReturnObservation", "DispatcherDecoder"]:
        result = check(HERE / (name + ".lean"), ROOT / ".lake/build/lib/lean" / ("TranslationValidation" + name + ".olean"))
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    audit(check(HERE / "DispatcherNodes.lean", ROOT / ".lake/build/lib/lean/TranslationValidationDispatcherNodes.olean"),
          {"decode" + n for n in ["FreeMemoryStore", "CalldataGate", "Fallback", "SelectorGate",
                                  "ValueGuard", "LengthGuard", "LoadX", "LoadY", "LoadD", "FunctionBody", "CapturedRuntime"]})
    audit(check(HERE / "DispatcherExecution.lean"),
          {"abi_branch_bytes_match_imported", "calldata_gate_true", "initial_selector_gate_true",
           "initial_calldata_size", "value_guard_passes", "length_guard_passes", "captured_loads_continuation",
           "loaded_bindings", "initial_abi_words"})
    ast = json.loads((HERE / "MulDivDown.optimized-ast.json").read_text())
    template = base.get(ast, base.BODY_PATH + [2, "value"])
    variants = []
    arities = {"calldataload": 1, "calldatasize": 0, "callvalue": 0, "lt": 2,
               "slt": 2, "shr": 2, "add": 2, "not": 1}
    for name, arity in arities.items():
        node = copy.deepcopy(template)
        node["functionName"]["name"] = name
        node["arguments"] = [copy.deepcopy(template["arguments"][0])] * (arity + 1)
        variants.append((node, f"wrong arity for {name}: {arity + 1}"))
    for name in ["memoryguard", "sload", "gas", "call"]:
        node = copy.deepcopy(template)
        node["functionName"]["name"] = name
        variants.append((node, "unsupported Yul builtin " + name))
    with tempfile.TemporaryDirectory(prefix="dispatcher-rejections-", dir=HERE) as work:
        path = Path(work) / "Rejections.lean"
        lines = ["import TranslationValidationDispatcherDecoder", "open SolidityTranslationValidation.AstBridge.Dispatcher"]
        lines += [f"example : decodeExpr 10 {base.quote_json(node)} = .error {json.dumps(error)} := by rfl"
                  for node, error in variants]
        path.write_text("\n".join(lines) + "\n")
        result = check(path)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    print(f"{len(variants)} dispatcher decoder near misses rejected")
    check_mutations()


def check_mutations():
    decoder = (HERE / "DispatcherDecoder.lean").read_text()
    # Preserve every original decoder equation for each opcode mutant while
    # reusing the already kernel-checked quotations. Re-elaborating the entire
    # 107KB JSON/AST source for every mutant can exhaust the unchanged timeout.
    # A fresh namespace prevents the mutated decoder from shadowing the baseline.
    mutant_decoder = decoder.replace("SolidityTranslationValidation.AstBridge.Dispatcher",
                                     "SolidityTranslationValidation.AstBridge.DispatcherMutant")
    obligations = ["namespace SolidityTranslationValidation.AstBridge.DispatcherMutant",
                   "set_option maxRecDepth 10000"]
    for name in ["FreeMemoryStore", "CalldataGate", "Fallback", "SelectorGate", "ValueGuard",
                 "LengthGuard", "LoadX", "LoadY", "LoadD", "FunctionBody"]:
        obligations.append(f"example : decodeStmt 40 Dispatcher.captured{name}Json = "
                           f".ok Dispatcher.captured{name} := by rfl")
    obligations.append("example : decodeRuntime 40 Dispatcher.capturedRuntimeJson = "
                       ".ok Dispatcher.capturedRuntime := by rfl")
    obligations.append("end SolidityTranslationValidation.AstBridge.DispatcherMutant")
    with tempfile.TemporaryDirectory(prefix="dispatcher-mutants-", dir=HERE) as work:
        # Check the unmutated renamed decoder through the same imports and all
        # equations first, so a namespace/import mistake cannot count as a kill.
        control = Path(work) / "Control.lean"
        control.write_text("import TranslationValidationDispatcherNodes\n" +
                           mutant_decoder + "\n" + "\n".join(obligations) + "\n")
        result = check(control)
        if result.returncode:
            raise SystemExit("dispatcher mutation control failed:\n" + result.stdout + result.stderr)
        print("dispatcher mutation control passed all 11 decoder obligations")
        for op, wrong in [("CALLDATALOAD", "MLOAD"), ("CALLDATASIZE", "CALLVALUE"), ("CALLVALUE", "CALLDATASIZE"),
                          ("LT", "GT"), ("SLT", "SGT"), ("SHR", "SHL"), ("ADD", "SUB"), ("NOT", "ISZERO")]:
            before = "pure (." + op + ","
            if decoder.count(before) != 1:
                raise SystemExit("nonunique decoder mutation: " + op)
            source = ("import TranslationValidationDispatcherNodes\n" +
                      mutant_decoder.replace(before, "pure (." + wrong + ",") +
                      "\n" + "\n".join(obligations) + "\n")
            path = Path(work) / (op + ".lean")
            path.write_text(source)
            result = check(path)
            if result.returncode == 0 or "rfl" not in result.stdout:
                raise SystemExit("incorrect decoder mutant result: " + op + "\n" + result.stdout + result.stderr)
            print("rejected dispatcher opcode mutant " + op)
        source = (HERE / "DispatcherExecution.lean").read_text()
        before = "(fun word => (UInt256.ofNat word.val).toByteArray)"
        if source.count(before) != 1:
            raise SystemExit("nonunique returned-byte mutation")
        path = Path(work) / "WrongReturn.lean"
        path.write_text(source.replace(before, "(fun word => (UInt256.ofNat (word.val + 1)).toByteArray)"))
        result = check(path)
        if result.returncode == 0 or not any(x in result.stdout for x in ("unsolved goals", "failed", "Type mismatch")):
            raise SystemExit("incorrect returned-byte mutation result:\n" + result.stdout + result.stderr)
        print("rejected dispatcher return-byte mutant")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dispatcher-only", action="store_true",
                        help="run the dispatcher checks only; does not certify inherited checkers")
    args = parser.parse_args()
    if not args.dispatcher_only:
        check_memoryguard_extension.main()
    else:
        print("Focused dispatcher checks: inherited checkers are not rerun")
    check_dispatcher()


if __name__ == "__main__":
    main()
