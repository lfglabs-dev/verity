#!/usr/bin/env python3
"""Acceptance checks for the Solidity importer structs slice."""

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]


def lake_binary() -> str:
    version = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    candidates = [
        Path.home() / ".elan/toolchains" / f"leanprover--lean4---{version}" / "bin/lake",
        Path("/var/lib/opencode/.elan/toolchains") / f"leanprover--lean4---{version}" / "bin/lake",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    found = shutil.which("lake")
    if found:
        return found
    raise RuntimeError("lake executable not found")


LAKE = lake_binary()
ENV = dict(os.environ)
SMOKE = "Contracts/SolidityImportSmoke/Structs"
TARGET = "SolidityImportSmokeStructs"
NS = "Contracts.SolidityImportSmoke.Structs.Store"
PROOF = f"{SMOKE}/Proofs.lean"


def check(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)
    print("PASS " + message, flush=True)


def run(root: Path, args: list[str], success: bool = True, contains: str | None = None) -> str:
    process = subprocess.run(
        args, cwd=root, env=ENV, text=True, capture_output=True, timeout=300
    )
    output = process.stdout + process.stderr
    if (process.returncode == 0) != success or (contains and contains not in output) or "PANIC" in output:
        raise AssertionError(f"{args}: exit {process.returncode}\n{output}")
    return output


def main() -> None:
    importer_path = ROOT / "Contracts/VaultFromSolidity/Importer/Importer.lean"
    syntax_path = ROOT / "Contracts/VaultFromSolidity/Importer/Syntax.lean"
    importer_text = importer_path.read_text()
    syntax_text = syntax_path.read_text()
    check("| pair " in syntax_text and "| fst " in syntax_text and "| snd " in syntax_text,
          "user structs are Expr.pair / fst / snd")
    check("StructDefinition" in importer_text and "UserDefinedTypeName" in importer_text,
          "importer accepts struct AST nodes")
    check("structConstructorCall" in importer_text,
          "importer encodes struct constructors")
    check("| pairRev " in syntax_text and ".pairRev " in importer_text,
          "named Acc({who, amount}) uses pairRev after source-order eval")
    check(".pairRev a b =>" in (ROOT / "Contracts/VaultFromSolidity/Importer/Semantics.lean").read_text(),
          "pairRev evaluates who then amount and packs uint-then-addr")
    check("struct with a dynamic member" in importer_text and "mapping with struct key" in importer_text,
          "importer rejects dynamic members and struct mapping keys")

    with tempfile.TemporaryDirectory(prefix="verity-struct-check-", dir=ROOT.parent) as directory:
        root = Path(directory)
        for name in ("Verity", "Compiler", "Contracts", "scripts"):
            shutil.copytree(ROOT / name, root / name)
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            shutil.copy2(ROOT / name, root / name)
        shutil.copytree(ROOT / ".lake/build", root / ".lake/build")
        (root / ".lake/solidity-import").mkdir(parents=True)
        shutil.copy2(ROOT / ".lake/solidity-import/solc", root / ".lake/solidity-import/solc")
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)

        source = root / SMOKE / "Structs.sol"
        original = source.read_bytes()
        source_stamp = source.stat()
        importer = root / "Contracts/VaultFromSolidity/Importer/Importer.lean"
        importer_original = importer.read_bytes()
        importer_stamp = importer.stat()
        proof = root / PROOF
        proof_text = proof.read_text()
        theorem_names = re.findall(r"^theorem\s+(\w+)", proof_text, re.M)

        def edit_source(data: bytes) -> None:
            source.write_bytes(data)
            os.utime(source, ns=(source_stamp.st_atime_ns, source_stamp.st_mtime_ns))

        def build(success: bool = True, contains: str | None = None) -> str:
            return run(root, [LAKE, "build", TARGET], success, contains)

        def artifacts() -> dict[str, tuple[int, str]]:
            paths = list((root / ".lake/build/lib/lean/Contracts/SolidityImportSmoke/Structs").rglob("*.olean"))
            return {
                str(path.relative_to(root)): (
                    path.stat().st_mtime_ns,
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in paths
            }

        def print_names(*names: str) -> str:
            probe = root / ".lake/solidity-import/StructPrint.lean"
            try:
                probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Structs\n"
                    + "".join(f"#print {NS}.{name}\n" for name in names)
                )
                return run(root, [LAKE, "env", "lean", str(probe)])
            finally:
                probe.unlink(missing_ok=True)

        def slot_numbers() -> str:
            slot_probe = root / ".lake/solidity-import/StructSlotProbe.lean"
            try:
                slot_probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Structs\n"
                    f"#eval [{NS}.data_amountSlot.slot, {NS}.data_whoSlot.slot, {NS}.otherSlot.slot]\n"
                )
                found = re.findall(r"\[\d+(?:, \d+)*\]", run(root, [LAKE, "env", "lean", str(slot_probe)]))
                if not found:
                    raise AssertionError("slot probe produced no list")
                return found[0]
            finally:
                slot_probe.unlink(missing_ok=True)

        build()
        check(True, "baseline lake build SolidityImportSmokeStructs")

        audit_file = root / ".lake/solidity-import/StructAxiomAudit.lean"
        try:
            audit_file.write_text(
                f"import {SMOKE.replace('/', '.')}.Proofs\n"
                + "\n".join(
                    f"#print axioms {SMOKE.replace('/', '.')}.Proofs.{name}"
                    for name in theorem_names
                )
                + "\n"
            )
            audit = run(root, [LAKE, "env", "lean", str(audit_file)])
        finally:
            audit_file.unlink(missing_ok=True)
        entries = re.findall(
            r"'Contracts.SolidityImportSmoke.Structs.Proofs.(\w+)' depends on axioms: \[([^\]]*)\]",
            audit,
        )
        check(set(theorem_names) == {name for name, _ in entries},
              "every struct theorem appears in #print axioms output")
        axioms = {a.strip() for _, values in entries for a in values.split(",") if a.strip()}
        check(axioms <= {"propext", "Quot.sound"},
              "no project axioms or sorryAx: " + ", ".join(sorted(axioms)))

        printed = print_names("set", "get", "make", "makeRev")
        check(".fst" in printed and ".snd" in printed,
              "#print Store.set decodes struct members")
        check(".pair" in printed,
              "#print Store.make / Store.get encode the user struct")
        check(".pairRev" in printed,
              "#print Store.makeRev encodes named Acc({who, amount})")
        check(slot_numbers() == "[0, 1, 2]",
              "struct members occupy consecutive solc slots [amount, who, other]")

        def broken_theorems(output: str) -> set[str]:
            error_lines = [int(value) for value in re.findall(rf"{PROOF}:(\d+):", output)]
            starts = [
                (match.group(1), line_no)
                for line_no, line in enumerate(proof_text.splitlines(), 1)
                if (match := re.match(r"theorem\s+([A-Za-z0-9_']+)", line.strip()))
            ]
            ranges = {
                name: (start, starts[index + 1][1] - 1 if index + 1 < len(starts)
                       else len(proof_text.splitlines()))
                for index, (name, start) in enumerate(starts)
            }
            return {name for name, (start, end) in ranges.items()
                    if any(start <= line <= end for line in error_lines)}

        reordered = original.replace(
            b"struct Acc {\n    uint256 amount;\n    address who;\n}",
            b"struct Acc {\n    address who;\n    uint256 amount;\n}",
        )
        check(original != reordered, "struct member reorder has a source target")
        edit_source(reordered)
        output = build(False, "unsupported struct shape")
        check(re.search(r"Contracts/SolidityImportSmoke/Structs/Structs.sol:\d+:\d+:", output)
              is not None,
              "reordering pair members is rejected with a source position")
        edit_source(original)
        build()

        named_reorder = original.replace(
            b"        return Acc({amount: amount, who: who});",
            b"        return Acc({who: who, amount: amount});",
        )
        check(original != named_reorder, "named constructor reorder has a source target")
        edit_source(named_reorder)
        build()
        printed_rev = print_names("make")
        check(".pairRev" in printed_rev,
              "named Acc({who, amount}) imports as pairRev")
        check(True, "named Acc({who: who, amount: amount}) still imports")
        edit_source(original)
        build()
        printed_fwd = print_names("make")
        check(".pair" in printed_fwd and ".pairRev" not in printed_fwd,
              "named Acc({amount, who}) stays Expr.pair")

        positional = original.replace(
            b"        return Acc({amount: amount, who: who});",
            b"        return Acc(amount, who);",
        )
        check(original != positional, "positional constructor has a source target")
        edit_source(positional)
        build()
        printed_pos = print_names("make")
        check(".pair" in printed_pos and ".pairRev" not in printed_pos,
              "positional Acc(amount, who) stays AST/member order as Expr.pair")
        edit_source(original)
        build()

        before = artifacts()
        importer.write_bytes(importer_original + b"\n-- structs identity probe\n")
        os.utime(importer, ns=(importer_stamp.st_atime_ns, importer_stamp.st_mtime_ns))
        build()
        check(before != artifacts(), "Lean importer content change invalidates struct artifacts")
        importer.write_bytes(importer_original)
        build()

        dyn_src = original.replace(
            b"    address who;\n",
            b"    address who;\n    string note;\n",
        ).replace(
            b"        return Acc({amount: amount, who: who});",
            b"        return Acc({amount: amount, who: who, note: \"\"});",
        ).replace(
            b"        return Acc({who: who, amount: amount});",
            b"        return Acc({who: who, amount: amount, note: \"\"});",
        )
        check(dyn_src != original, "dynamic member mutation has a source target")
        edit_source(dyn_src)
        output = build(False)
        check(
            "struct with a dynamic member" in output or "unsupported struct shape" in output,
            "dynamic member is rejected",
        )
        check(re.search(r"Contracts/SolidityImportSmoke/Structs/Structs.sol:\d+:\d+:", output)
              is not None,
              "dynamic member rejected with source position")
        edit_source(original)

        key_old = b"    Acc public data;\n    uint256 public other;\n"
        key_new = b"    Acc public data;\n    uint256 public other;\n    mapping(Acc => uint256) private keyed;\n"
        check(original.count(key_old) == 1, "struct mapping key mutation has one source target")
        edit_source(original.replace(key_old, key_new))
        output = build(False)
        check(
            "mapping with struct key" in output or "TypeError" in output,
            "mapping with struct key is rejected",
        )
        check(re.search(r"Contracts/SolidityImportSmoke/Structs/Structs.sol:\d+:\d+:", output)
              is not None,
              "mapping with struct key rejected with source position")
        edit_source(original)
        build()

        check(source.read_bytes() == original and importer.read_bytes() == importer_original,
              "temporary mutations restored; final baseline passes")
        print(f"PASS all struct-slice acceptance checks ({len(theorem_names)} audited theorems)",
              flush=True)


if __name__ == "__main__":
    main()
