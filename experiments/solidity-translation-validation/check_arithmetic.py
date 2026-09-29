#!/usr/bin/env python3
"""Kernel-check the intermediate lemmas and reject incorrect guard variants."""

from pathlib import Path
import hashlib
import re
import subprocess
import tempfile

from capture import BLOB, WRAPPER, SOURCE as SOLIDITY_SOURCE

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = HERE / "Arithmetic.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = {
    "mul_overflow_guard_iff",
    "denote_word_mul_overflow_guard_iff",
    "native_mul_overflow_guard_iff",
    "native_product",
    "native_mul_div_success",
    "denote_mul_div_success",
}


def check(path, output=None):
    command = ["lake", "env", "lean"]
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        command.extend(["-o", str(output)])
    return subprocess.run(
        command + [str(path)], cwd=ROOT,
        text=True, capture_output=True, timeout=120,
    )


def main():
    solidity = (HERE / "sources" / SOLIDITY_SOURCE).read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(solidity)).encode() + b"\0" + solidity).hexdigest()
    if blob != BLOB or (HERE / "sources/MulDivDown.sol").read_text() != WRAPPER:
        raise SystemExit("materialized Solidity source differs from the pinned capture")
    baseline = check(SOURCE, ROOT / ".lake/build/lib/lean/TranslationValidationArithmetic.olean")
    if baseline.returncode:
        raise SystemExit(baseline.stdout + baseline.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.(\w+)' depends on axioms: \[([^]]*)\]",
        baseline.stdout,
    )
    if {name for name, _ in receipts} != THEOREMS:
        raise SystemExit("missing or unexpected theorem axiom receipts")
    for name, axioms in receipts:
        found = {entry.strip() for entry in axioms.split(",") if entry.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axiom dependencies for {name}: {found}")
    print(baseline.stdout, end="")
    source = SOURCE.read_text()
    mutations = {
        "missing-zero-product-case": (
            "(x = 0 ∨ (x * y % modulus) / x = y)",
            "((x * y % modulus) / x = y)",
        ),
        "wrong-word-modulus": (
            "(x = 0 ∨ (x * y % modulus) / x = y)",
            "(x = 0 ∨ (x * y % (modulus + 1)) / x = y)",
        ),
        "native-product-is-division": (
            'evalPureBuiltinViaEvmYulLean "mul" [x, y] =',
            'evalPureBuiltinViaEvmYulLean "div" [x, y] =',
        ),
    }
    with tempfile.TemporaryDirectory(prefix="arithmetic-mutants-", dir=HERE) as work:
        for name, (before, after) in mutations.items():
            if source.count(before) != 1:
                raise SystemExit(f"mutation anchor is not unique: {name}")
            path = Path(work) / (name + ".lean")
            path.write_text(source.replace(before, after))
            mutant = check(path)
            if mutant.returncode == 0:
                raise SystemExit(f"incorrect arithmetic variant accepted: {name}")
            if "unsolved goals" not in mutant.stdout and "Type mismatch" not in mutant.stdout:
                raise SystemExit(f"unexpected failure for {name}:\n{mutant.stdout}{mutant.stderr}")
            print(f"rejected {name}")
    print("six intermediate theorems kernel-checked; three incorrect variants rejected")
    imported = check(HERE / "Imported.lean")
    if imported.returncode:
        raise SystemExit(imported.stdout + imported.stderr)
    receipts = re.findall(
        r"'SolidityTranslationValidation\.(\w+)' depends on axioms: \[([^]]*)\]",
        imported.stdout,
    )
    expected = {"captured_success", "captured_success_matches_native_arithmetic"}
    if {name for name, _ in receipts} != expected:
        raise SystemExit("missing imported-model proof receipts")
    for name, axioms in receipts:
        found = {entry.strip() for entry in axioms.split(",") if entry.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise SystemExit(f"unexpected axiom dependencies for {name}: {found}")
    print(imported.stdout, end="")
    print("actual imported-wrapper success and native-arithmetic corollary kernel-checked")


if __name__ == "__main__":
    main()
