#!/usr/bin/env python3
"""Check exact native return bytes against the actual imported wrapper result."""
from pathlib import Path
import re
import tempfile

import check_arithmetic
import check_ast_bridge
from check_arithmetic import ALLOWED_AXIOMS, check

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    # Re-run all previous baselines, rejection cases and mutations before using
    # their proof artifacts; stale local oleans cannot establish this check.
    check_arithmetic.main()
    check_ast_bridge.main()
    for source, module in [("Imported", "TranslationValidationImported"),
                           ("GuardedExecution", "TranslationValidationGuardedExecution")]:
        result = check(HERE / (source + ".lean"),
                       ROOT / ".lake/build/lib/lean" / (module + ".olean"))
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    source_path = HERE / "ReturnObservation.lean"
    result = check(source_path)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.AstBridge\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    )
    expected = {"write128_return32", "successfulBodyState_bytes", "captured_body_bytes_match_imported"}
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing exact-return axiom receipts")
    for name, axioms in receipts:
        found = {entry.strip() for entry in axioms.split(",") if entry.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axioms for {name}: {found}")
    print(result.stdout, end="")
    source = source_path.read_text()
    mutations = {
        "wrong-return-offset": (".readWithPadding 128 32 = source", ".readWithPadding 129 32 = source"),
        "wrong-imported-return-word": ("(fun word => (UInt256.ofNat word.val).toByteArray)",
                                       "(fun word => (UInt256.ofNat (word.val + 1)).toByteArray)"),
        "wrong-success-status": ("if status = UInt256.ofNat 1 then", "if status = UInt256.ofNat 0 then"),
    }
    with tempfile.TemporaryDirectory(prefix="return-mutants-", dir=HERE) as work:
        for name, (before, after) in mutations.items():
            if source.count(before) != 1:
                raise SystemExit("mutation anchor is not unique: " + name)
            path = Path(work) / (name + ".lean")
            path.write_text(source.replace(before, after))
            mutant = check(path)
            if mutant.returncode == 0:
                raise SystemExit("incorrect return-byte theorem accepted: " + name)
            if not any(marker in mutant.stdout for marker in ("unsolved goals", "Type mismatch", "rewrite", "failed")):
                raise SystemExit(f"unexpected mutant failure: {name}\n{mutant.stdout}{mutant.stderr}")
            print("rejected " + name)


if __name__ == "__main__":
    main()
