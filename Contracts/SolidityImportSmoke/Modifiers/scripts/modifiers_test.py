#!/usr/bin/env python3
"""Acceptance checks for the Solidity importer modifiers slice."""

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
SMOKE = "Contracts/SolidityImportSmoke/Modifiers"
TARGET = "SolidityImportSmokeModifiers"
NS = "Contracts.SolidityImportSmoke.Modifiers.Child"
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
    semantics_path = ROOT / "Contracts/VaultFromSolidity/Importer/Semantics.lean"
    importer_text = importer_path.read_text()
    syntax_text = syntax_path.read_text()
    semantics_text = semantics_path.read_text()
    check("| seq " in syntax_text and "| block " in syntax_text,
          "modifier inlining uses Stmt.seq / Stmt.block")
    check("Semantics.lean never sees `_`" in semantics_text or
          "this file never sees `_`" in semantics_text,
          "modifier placeholder is inlined at parse time")
    check("wrapModifiers" in importer_text and "modifier with two placeholders" in importer_text,
          "importer inlines modifiers and rejects two placeholders")
    check("modifier arguments" in importer_text,
          "importer rejects parameterized modifiers")
    check("static.visibility == \"private\"" in importer_text and "!static.virtual" in importer_text,
          "identifier calls keep private/non-virtual static binding")
    check("wrapModifierParts" in importer_text and "inner.shift .uint 0" in importer_text,
          "prelude locals are bound over the inlined body and postlude")

    with tempfile.TemporaryDirectory(prefix="verity-mod-check-", dir=ROOT.parent) as directory:
        root = Path(directory)
        for name in ("Verity", "Compiler", "Contracts", "scripts"):
            shutil.copytree(ROOT / name, root / name)
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            shutil.copy2(ROOT / name, root / name)
        shutil.copytree(ROOT / ".lake/build", root / ".lake/build")
        (root / ".lake/solidity-import").mkdir(parents=True)
        shutil.copy2(ROOT / ".lake/solidity-import/solc", root / ".lake/solidity-import/solc")
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)

        source = root / SMOKE / "Modifiers.sol"
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
            paths = list((root / ".lake/build/lib/lean/Contracts/SolidityImportSmoke/Modifiers").rglob("*.olean"))
            return {
                str(path.relative_to(root)): (
                    path.stat().st_mtime_ns,
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in paths
            }

        def print_names(*names: str) -> str:
            probe = root / ".lake/solidity-import/ModPrint.lean"
            try:
                probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Modifiers\n"
                    + "".join(f"#print {NS}.{name}\n" for name in names)
                )
                return run(root, [LAKE, "env", "lean", str(probe)])
            finally:
                probe.unlink(missing_ok=True)

        build()
        check(True, "baseline lake build SolidityImportSmokeModifiers")

        audit_file = root / ".lake/solidity-import/ModAxiomAudit.lean"
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
            r"'Contracts.SolidityImportSmoke.Modifiers.Proofs.(\w+)' depends on axioms: \[([^\]]*)\]",
            audit,
        )
        check(set(theorem_names) == {name for name, _ in entries},
              "every modifier theorem appears in #print axioms output")
        axioms = {a.strip() for _, values in entries for a in values.split(",") if a.strip()}
        check(axioms <= {"propext", "Quot.sound"},
              "no project axioms or sorryAx: " + ", ".join(sorted(axioms)))

        printed_early = print_names("early")
        check(".seq" in printed_early and ".block" in printed_early,
              "#print Child.early inlines nonReentrant as seq/block")
        printed_guarded = print_names("guarded")
        check(printed_guarded.find("NotOwner") < printed_guarded.find("EnforcedPause"),
              "onlyOwner then whenNotPaused is declaration order")
        printed_tagged = print_names("tagged")
        check("HelperLike_bump" in printed_tagged and "Child_bump" not in printed_tagged,
              "inherited modifier keeps the declaring contract's private helper")
        printed_snapshot = print_names("snapshot")
        check(".local_" in printed_snapshot and ".block" in printed_snapshot,
              "#print Child.snapshot carries restore prelude local into the postlude")

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

        postlude = b"        status = 2;\n        _;\n        status = 1;"
        dropped = b"        status = 2;\n        _;"
        check(original.count(postlude) == 1, "nonReentrant postlude has one source target")
        edit_source(original.replace(postlude, dropped))
        output = build(False, "Contracts.SolidityImportSmoke.Modifiers.Proofs")
        check(bool({"status_restored", "early_meets_spec"} & broken_theorems(output)),
              "dropping the nonReentrant postlude breaks status_restored")
        edit_source(original)
        build()

        swapped = original.replace(b"onlyOwner whenNotPaused", b"whenNotPaused onlyOwner")
        check(original != swapped, "modifier-order mutation has a source target")
        edit_source(swapped)
        output = build(False, "Contracts.SolidityImportSmoke.Modifiers.Proofs")
        check("guarded_reverts_not_owner_before_pause" in broken_theorems(output),
              "swapping onlyOwner/whenNotPaused breaks guarded_reverts_not_owner_before_pause")
        edit_source(original)
        build()

        before = artifacts()
        importer.write_bytes(importer_original + b"\n-- modifiers identity probe\n")
        os.utime(importer, ns=(importer_stamp.st_atime_ns, importer_stamp.st_mtime_ns))
        build()
        check(before != artifacts(), "Lean importer content change invalidates modifier artifacts")
        importer.write_bytes(importer_original)
        build()

        two_ph_old = b"        if (msg.sender != owner) revert NotOwner();\n        _;"
        two_ph_new = b"        if (msg.sender != owner) revert NotOwner();\n        _;\n        _;"
        check(original.count(two_ph_old) == 1, "two placeholders mutation has one source target")
        edit_source(original.replace(two_ph_old, two_ph_new))
        output = build(False, "modifier with two placeholders")
        check(re.search(r"Contracts/SolidityImportSmoke/Modifiers/Modifiers.sol:\d+:\d+:", output)
              is not None,
              "two placeholders rejected with source position")
        edit_source(original)

        args_src = original.replace(
            b"    modifier onlyOwner() {\n        if (msg.sender != owner) revert NotOwner();\n        _;\n    }",
            b"    modifier onlyOwner(uint256 unused) {\n        unused;\n        if (msg.sender != owner) revert NotOwner();\n        _;\n    }",
        ).replace(
            b"    function guarded(uint256 amount) external onlyOwner whenNotPaused {",
            b"    function guarded(uint256 amount) external onlyOwner(0) whenNotPaused {",
        )
        check(args_src != original, "modifier arguments mutation has a source target")
        edit_source(args_src)
        output = build(False, "modifier arguments")
        check(re.search(r"Contracts/SolidityImportSmoke/Modifiers/Modifiers.sol:\d+:\d+:", output)
              is not None,
              "modifier arguments rejected with source position")
        edit_source(original)
        build()

        restore_post = b"        uint256 old = status;\n        _;\n        status = old;"
        restore_dropped = b"        uint256 old = status;\n        _;"
        check(original.count(restore_post) == 1, "restore postlude has one source target")
        edit_source(original.replace(restore_post, restore_dropped))
        output = build(False, "Contracts.SolidityImportSmoke.Modifiers.Proofs")
        check(bool({"snapshot_restores_status"} & broken_theorems(output)),
              "dropping the restore postlude breaks snapshot_restores_status")
        edit_source(original)
        build()

        base_helper = b"    function bump() private {\n        helperValue = 1;\n    }"
        base_helper_mut = b"    function bump() private {\n        helperValue = 9;\n    }"
        check(original.count(base_helper) == 1, "base private helper has one source target")
        edit_source(original.replace(base_helper, base_helper_mut))
        output = build(False, "Contracts.SolidityImportSmoke.Modifiers.Proofs")
        check(bool({"tagged_uses_base_helper"} & broken_theorems(output)),
              "mutating the declaring contract's private helper breaks tagged_uses_base_helper")
        edit_source(original)
        build()
        poison = b"    function poison() private {\n        helperValue = 2;\n    }"
        poison_mut = b"    function poison() private {\n        helperValue = 9;\n    }"
        check(original.count(poison) == 1, "unrelated derived private helper has one source target")
        edit_source(original.replace(poison, poison_mut))
        build()
        mutated_tagged = print_names("tagged")
        check("HelperLike_bump" in mutated_tagged and "Child_bump" not in mutated_tagged,
              "mutating an unrelated derived private helper does not rebind the inherited modifier")
        edit_source(original)
        build()

        check(source.read_bytes() == original and importer.read_bytes() == importer_original,
              "temporary mutations restored; final baseline passes")
        print(f"PASS all modifier-slice acceptance checks ({len(theorem_names)} audited theorems)",
              flush=True)


if __name__ == "__main__":
    main()
