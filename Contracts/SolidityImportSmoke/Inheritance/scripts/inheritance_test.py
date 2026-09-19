#!/usr/bin/env python3
"""Acceptance checks for the Solidity importer inheritance slice."""

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]


def lake_binary() -> str:
    found = shutil.which("lake")
    if found:
        return found
    version = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    candidates = [
        Path.home() / ".elan/toolchains" / f"leanprover--lean4---{version}" / "bin/lake",
        Path("/var/lib/opencode/.elan/toolchains") / f"leanprover--lean4---{version}" / "bin/lake",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    raise RuntimeError("lake executable not found")


LAKE = lake_binary()
ENV = dict(os.environ)
SMOKE = "Contracts/SolidityImportSmoke/Inheritance"
TARGET = "SolidityImportSmokeInheritance"
NS = "Contracts.SolidityImportSmoke.Inheritance.Child"
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
    check("inductive FVar" in syntax_text and "inductive Args" in syntax_text,
          "function table (FVar/Args) is in Syntax.lean")
    check("| call " in syntax_text and "| callStmt" in syntax_text,
          "internal calls are Expr.call / Stmt.callStmt")
    check("FnEnv" in semantics_text and "Args.eval" in semantics_text,
          "call meaning is in Semantics.lean")
    check("registeredSources" in importer_text and "linearizedBaseContracts" in importer_text,
          "importer accepts C3 linearization and a source manifest")
    check("effectful internal call in expression position" in importer_text,
          "importer rejects effectful Expr.call (legacy codegen order)")
    check("super dispatch family mismatch" in importer_text and
          "super dispatch disagrees with AST" not in importer_text,
          "super follows target C3 rather than defining-contract AST id")

    with tempfile.TemporaryDirectory(prefix="verity-inh-check-", dir=ROOT.parent) as directory:
        root = Path(directory)
        for name in ("Verity", "Compiler", "Contracts", "scripts"):
            shutil.copytree(ROOT / name, root / name)
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            shutil.copy2(ROOT / name, root / name)
        shutil.copytree(ROOT / ".lake/build", root / ".lake/build")
        (root / ".lake/solidity-import").mkdir(parents=True)
        shutil.copy2(ROOT / ".lake/solidity-import/solc", root / ".lake/solidity-import/solc")
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)

        source = root / SMOKE / "Inheritance.sol"
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
            paths = list((root / ".lake/build/lib/lean/Contracts/SolidityImportSmoke/Inheritance").rglob("*.olean"))
            return {
                str(path.relative_to(root)): (
                    path.stat().st_mtime_ns,
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in paths
            }

        def source_digest() -> str:
            digest_probe = root / ".lake/solidity-import/InhDigestProbe.lean"
            try:
                digest_probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Inheritance\n"
                    f"#eval {NS}.sourceDigest\n"
                )
                output = run(root, [LAKE, "env", "lean", str(digest_probe)])
                match = re.search(r'"([0-9a-f]{64})"', output)
                if match is None:
                    raise AssertionError("sourceDigest is not an auditable SHA-256 value")
                return match.group(1)
            finally:
                digest_probe.unlink(missing_ok=True)

        def slot_numbers() -> str:
            slot_probe = root / ".lake/solidity-import/InhSlotProbe.lean"
            try:
                slot_probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Inheritance\n"
                    f"#eval [{NS}.baseValueSlot.slot, {NS}.leftValueSlot.slot, "
                    f"{NS}.rightValueSlot.slot, {NS}.pausedSlot.slot, "
                    f"{NS}.ownerSlot.slot, {NS}.childValueSlot.slot]\n"
                )
                found = re.findall(r"\[\d+(?:, \d+)*\]", run(root, [LAKE, "env", "lean", str(slot_probe)]))
                if not found:
                    raise AssertionError("slot probe produced no list")
                return found[0]
            finally:
                slot_probe.unlink(missing_ok=True)

        build()
        check(True, "baseline lake build SolidityImportSmokeInheritance")

        audit_file = root / ".lake/solidity-import/InhAxiomAudit.lean"
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
            r"'Contracts.SolidityImportSmoke.Inheritance.Proofs.(\w+)' depends on axioms: \[([^\]]*)\]",
            audit,
        )
        check(set(theorem_names) == {name for name, _ in entries},
              "every inheritance theorem appears in #print axioms output")
        axioms = {a.strip() for _, values in entries for a in values.split(",") if a.strip()}
        check(axioms <= {"propext", "Quot.sound"},
              "no project axioms or sorryAx: " + ", ".join(sorted(axioms)))

        print_probe = root / ".lake/solidity-import/InhPrintProbe.lean"
        try:
            print_probe.write_text(
                f"import {SMOKE.replace('/', '.')}.Inheritance\n"
                f"#print {NS}.go\n"
                f"#print {NS}.Child__pause\n"
            )
            printed = run(root, [LAKE, "env", "lean", str(print_probe)])
            check("Child__pause" in printed and "callStmt" in printed,
                  "#print Child.go shows a call to Child__pause")
            check("PausableLike__pause" in printed,
                  "#print Child__pause shows the super hop to PausableLike__pause")
        finally:
            print_probe.unlink(missing_ok=True)

        def import_only(success: bool = True, contains: str | None = None) -> str:
            # Rebuild the importer module without Proofs.lean: diamond internals
            # enlarge FnEnv enough that the smoke proofs' `simp` budget fails,
            # but solc C3 super still has to elaborate.
            return run(
                root,
                [LAKE, "build", "Contracts.SolidityImportSmoke.Inheritance.Inheritance"],
                success,
                contains,
            )

        def print_names(*names: str) -> str:
            probe = root / ".lake/solidity-import/InhPrintNames.lean"
            try:
                probe.write_text(
                    f"import {SMOKE.replace('/', '.')}.Inheritance\n"
                    + "".join(f"#print {NS}.{name}\n" for name in names)
                )
                return run(root, [LAKE, "env", "lean", str(probe)])
            finally:
                probe.unlink(missing_ok=True)

        slots = slot_numbers()
        check(slots == "[0, 1, 2, 3, 4, 5]",
              "inherited slots follow solc layout [base, left, right, paused, owner, child]")

        swapped = original.replace(b"is Left, Right, PausableLike, OwnableLike",
                                   b"is Right, Left, PausableLike, OwnableLike")
        check(original != swapped, "is-order mutation has a source target")
        edit_source(swapped)
        build()
        check(slot_numbers() == "[0, 2, 1, 3, 4, 5]",
              "swapping is-order changes C3 and inherited slot numbers")
        edit_source(original)
        build()

        diamond = original.replace(
            b"    function _bump() internal virtual {\n        baseValue += 1;\n    }\n",
            b"    function _bump() internal virtual {\n        baseValue += 1;\n    }\n"
            b"    function _trace() internal virtual {}\n",
        ).replace(
            b"abstract contract Left is Base {\n    uint256 public leftValue;\n}\n",
            b"abstract contract Left is Base {\n    uint256 public leftValue;\n"
            b"    function _trace() internal virtual override { super._trace(); }\n}\n",
        ).replace(
            b"abstract contract Right is Base {\n    uint256 public rightValue;\n}\n",
            b"abstract contract Right is Base {\n    uint256 public rightValue;\n"
            b"    function _trace() internal virtual override {}\n}\n",
        ).replace(
            b"    function go() external {\n        _pause();\n    }\n",
            b"    function _trace() internal override(Left, Right) { super._trace(); }\n"
            b"    function go() external {\n        _pause();\n    }\n",
        )
        check(original != diamond, "diamond virtual mutation has a source target")
        edit_source(diamond)
        import_only()
        diamond_printed = print_names("Child__trace", "Left__trace")
        check("callStmt" in diamond_printed,
              "diamond super on default is-order imports as callStmt")
        # `is Right, Left` makes Left more derived than Right. Left._trace's AST
        # super target is Base._trace; target C3 super is Right._trace.
        diamond_swapped = diamond.replace(
            b"is Left, Right, PausableLike, OwnableLike",
            b"is Right, Left, PausableLike, OwnableLike")
        edit_source(diamond_swapped)
        swapped_import = import_only()
        check("super dispatch disagrees with AST" not in swapped_import,
              "diamond super follows target C3, not defining-contract AST id")
        check("callStmt" in print_names("Left__trace"),
              "#print Left__trace after diamond is-order swap still has super callStmt")
        edit_source(original)
        build()

        sum_src = original.replace(
            b"    function _add(uint256 a, uint256 b) internal pure returns (uint256) {\n"
            b"        return a + b;\n    }\n",
            b"    function _add(uint256 a, uint256 b) internal pure returns (uint256) {\n"
            b"        return a + b;\n    }\n"
            b"    function _sum() internal pure returns (uint256) {\n"
            b"        return _add(1, 2);\n    }\n",
        )
        check(original != sum_src, "pure Expr.call mutation has a source target")
        edit_source(sum_src)
        import_only()
        check("Child__add" in print_names("Child__sum"),
              "#print Child__sum shows Expr.call of pure Child__add")
        edit_source(original)
        build()

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

        override = b"        childValue += 1;"
        check(original.count(override) == 1, "override body has one source target")
        edit_source(original.replace(override, b"        childValue = 0;"))
        output = build(False, "Contracts.SolidityImportSmoke.Inheritance.Proofs")
        broken = broken_theorems(output)
        check(bool({"dispatch_is_child", "pause_success_spec", "go_success_spec"} & broken),
              "changing the override body breaks the dispatch observation")
        edit_source(original)
        build()

        pause_fn = b"    function pause() external {\n        _pause();\n    }\n"
        extra = b"    function ping() external {\n        paused = paused;\n    }\n" + pause_fn
        check(original.count(pause_fn) == 1, "base public function has one source target")
        edit_source(original.replace(pause_fn, extra))
        output = build(False, "Contracts.SolidityImportSmoke.Inheritance.Proofs")
        check("paused_invariant" in broken_theorems(output),
              "adding a public function to a base breaks paused_invariant")
        edit_source(original)
        build()

        before = artifacts()
        digest_before = source_digest()
        importer.write_bytes(importer_original + b"\n-- inheritance identity probe\n")
        os.utime(importer, ns=(importer_stamp.st_atime_ns, importer_stamp.st_mtime_ns))
        build()
        check(before != artifacts(), "Lean importer content change invalidates inheritance artifacts")
        check(digest_before != source_digest(), "Lean importer content changes sourceDigest")
        importer.write_bytes(importer_original)
        build()

        semantics = root / "Contracts/VaultFromSolidity/Importer/Semantics.lean"
        semantics_original = semantics.read_bytes()
        semantics_stamp = semantics.stat()
        before = artifacts()
        digest_before = source_digest()
        semantics.write_bytes(semantics_original + b"\n-- inheritance semantics identity probe\n")
        os.utime(semantics, ns=(semantics_stamp.st_atime_ns, semantics_stamp.st_mtime_ns))
        build()
        check(before != artifacts(), "Lean semantics content change invalidates inheritance artifacts")
        check(digest_before != source_digest(), "Lean semantics content changes sourceDigest")
        semantics.write_bytes(semantics_original)
        build()

        for name, old, new, diagnostic in (
            ("direct recursion",
             b"        super._pause();\n        childValue += 1;",
             b"        _pause();\n        childValue += 1;",
             "recursion"),
            ("unimplemented virtual",
             b"    function _bump() internal virtual {\n        baseValue += 1;\n    }",
             b"    function _bump() internal virtual;",
             "abstract"),
            ("opaque field touch",
             b"    function go() external {\n        _pause();\n    }",
             b"    function go() external {\n        unusedGap = unusedGap;\n        _pause();\n    }",
             "opaque field"),
            ("function overloading",
             b"    function bump() external {\n        _bump();\n    }",
             b"    function bump() external {\n        _bump();\n    }\n"
             b"    function bump(uint256 x) external {\n        baseValue = x;\n    }",
             "overloading"),
            ("effectful add of internal call",
             b"    function bump() external {\n        _bump();\n    }",
             b"    function _inc() internal returns (uint256) {\n"
             b"        childValue += 1;\n        return childValue;\n    }\n"
             b"    function bump() external {\n"
             b"        childValue = childValue + _inc();\n    }",
             "effectful internal call in expression position"),
            ("effectful compound assignment of internal call",
             b"    function bump() external {\n        _bump();\n    }",
             b"    function _inc() internal returns (uint256) {\n"
             b"        childValue += 1;\n        return childValue;\n    }\n"
             b"    function bump() external {\n"
             b"        childValue += _inc();\n    }",
             "effectful internal call in expression position"),
        ):
            check(original.count(old) == 1, name + " mutation has one source target")
            edit_source(original.replace(old, new))
            output = build(False, diagnostic)
            check(re.search(r"Contracts/SolidityImportSmoke/Inheritance/Inheritance.sol:\d+:\d+:", output)
                  is not None,
                  name + " rejected with source position")
        edit_source(original)
        build()

        check(source.read_bytes() == original and importer.read_bytes() == importer_original,
              "temporary mutations restored; final baseline passes")
        print(f"PASS all inheritance-slice acceptance checks ({len(theorem_names)} audited theorems)",
              flush=True)


if __name__ == "__main__":
    main()
