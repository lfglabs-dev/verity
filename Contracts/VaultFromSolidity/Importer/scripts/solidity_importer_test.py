#!/usr/bin/env python3
"""Acceptance checks for the Lean-only Solidity frontend.

Python only orchestrates disposable builds and mutations. The production import
path is `Contracts/VaultFromSolidity/Importer/Importer.lean` -> pinned solc -> checked Lean declarations.
"""

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
        Path("/home/claudine/.hermes/profiles/claudine/home/.elan/toolchains")
        / f"leanprover--lean4---{version}" / "bin/lake",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    raise RuntimeError("lake executable not found")


LAKE = lake_binary()
ENV = dict(os.environ)


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
    importer_text = importer_path.read_text()
    python_frontend = ROOT / "Contracts/VaultFromSolidity/Importer/scripts/solidity_importer.py"
    check(not python_frontend.exists(), "no Python importer/frontend exists")
    check("--standard-json" in importer_text and "--no-import-callback" in importer_text,
          "Lean importer invokes pinned solc standard JSON with import callback disabled")
    check("solcSha256" in importer_text and "compiler checksum mismatch" in importer_text,
          "Lean importer enforces compiler checksum and version pin")
    check('cmd := "/usr/bin/sha256sum"' in importer_text and 'cmd := "sha256sum"' not in importer_text,
          "compiler checksum utility uses a fixed path, not PATH lookup")
    check("translateExpr" in importer_text and "translateStmts" in importer_text,
          "Solidity constructs have explicit Lean translation functions")
    check(all(tag not in importer_text for tag in ('[\"read\"', '[\"write\"', '[\"guard\"')),
          "no custom serialized JSON IR tags")

    with tempfile.TemporaryDirectory(prefix="verity-vault-check-", dir=ROOT.parent) as directory:
        root = Path(directory)
        for name in ("Verity", "Compiler", "Contracts", "scripts"):
            shutil.copytree(ROOT / name, root / name)
        for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            shutil.copy2(ROOT / name, root / name)
        shutil.copytree(ROOT / ".lake/build", root / ".lake/build")
        (root / ".lake/solidity-import").mkdir(parents=True)
        shutil.copy2(ROOT / ".lake/solidity-import/solc", root / ".lake/solidity-import/solc")
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)

        source = root / "Contracts/VaultFromSolidity/Vault.sol"
        original = source.read_bytes()
        source_stamp = source.stat()
        importer = root / "Contracts/VaultFromSolidity/Importer/Importer.lean"
        importer_original = importer.read_bytes()
        importer_stamp = importer.stat()
        compiler = root / ".lake/solidity-import/solc"
        compiler_original = compiler.read_bytes()
        lean_sources = set(root.rglob("*.lean"))

        def edit_source(data: bytes) -> None:
            source.write_bytes(data)
            os.utime(source, ns=(source_stamp.st_atime_ns, source_stamp.st_mtime_ns))

        def build(success: bool = True, contains: str | None = None) -> str:
            return run(root, [LAKE, "build", "VaultFromSolidity"], success, contains)

        def artifacts() -> dict[str, tuple[int, str]]:
            paths = list((root / ".lake/build/lib/lean/Contracts/VaultFromSolidity").rglob("*.olean"))
            return {
                str(path.relative_to(root)): (
                    path.stat().st_mtime_ns,
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in paths
            }

        def source_digest() -> str:
            digest_probe = root / ".lake/solidity-import/SourceDigestProbe.lean"
            try:
                digest_probe.write_text(
                    "import Contracts.VaultFromSolidity.VaultFromSolidity\n"
                    "#eval Contracts.VaultFromSolidity.sourceDigest\n"
                )
                output = run(root, [LAKE, "env", "lean", str(digest_probe)])
                match = re.search(r'"([0-9a-f]{64})"', output)
                if match is None:
                    raise AssertionError("sourceDigest is not an auditable SHA-256 value")
                check(True, "sourceDigest is an auditable SHA-256 value")
                return match.group(1)
            finally:
                digest_probe.unlink(missing_ok=True)

        build()
        check(True, "baseline lake build VaultFromSolidity")

        ux_probe = root / "Contracts/VaultFromSolidity/FrontendProbe.lean"
        try:
            ux_probe.write_text('''import Contracts.VaultFromSolidity.Importer.Importer
solidity_contract Vault from "Vault.sol"
#print Vault.deposit
''')
            ux_output = run(root, [LAKE, "env", "lean", str(ux_probe)])
            check("def Vault.deposit" in ux_output and "Verity.setStorage" in ux_output,
                  "documented solidity_contract Vault UX exposes #print Vault.deposit")
        finally:
            ux_probe.unlink(missing_ok=True)

        proof = root / "Contracts/VaultFromSolidity/Proofs/Execution.lean"
        proof_text = proof.read_text()
        theorem_names = re.findall(r"^theorem\s+(\w+)", proof_text, re.M)
        audit_file = root / ".lake/solidity-import/AxiomAudit.lean"
        try:
            audit_file.write_text(
                "import Contracts.VaultFromSolidity.Proofs.Execution\n"
                + "\n".join(
                    "#print axioms Contracts.VaultFromSolidity.Proofs.Execution." + name
                    for name in theorem_names
                )
                + "\n"
            )
            audit = run(root, [LAKE, "env", "lean", str(audit_file)])
        finally:
            audit_file.unlink(missing_ok=True)
        entries = re.findall(
            r"'Contracts.VaultFromSolidity.Proofs.Execution.(\w+)' depends on axioms: \[([^\]]*)\]", audit
        )
        check(set(theorem_names) == {name for name, _ in entries},
              "every theorem appears in actual #print axioms output")
        axioms = {a.strip() for _, values in entries for a in values.split(",") if a.strip()}
        check(axioms <= {"propext", "Quot.sound", "Classical.choice"},
              "no project axioms or sorryAx: " + ", ".join(sorted(axioms)))

        probe = root / ".lake/solidity-import/RegistrationProbe.lean"
        try:
            probe.write_text('''import Contracts.VaultFromSolidity.VaultFromSolidity
open Lean Elab Command
#print Contracts.VaultFromSolidity.deposit
run_cmd do
  for suffix in ["totalAssetsSlot", "totalSupplySlot", "shareBalancesSlot",
                 "deposit", "withdraw", "balanceOf", "totalAssets", "totalSupply",
                 "shareBalances", "sourceDigest"] do
    let name := `Contracts.VaultFromSolidity ++ Name.mkSimple suffix
    let some (.defnInfo info) := (← getEnv).find? name
      | throwError "not a transparent definition: {name}"
    unless info.safety == .safe && !info.value.hasMVar && !info.value.hasFVar do
      throwError "unsafe or unclosed definition: {name}"
    for dep in info.value.getUsedConstants do
      if dep.toString.startsWith "Contracts." &&
          !dep.toString.startsWith "Contracts.VaultFromSolidity." then
        throwError "imported declaration depends on handwritten contract: {dep}"
  let some (.defnInfo deposit) := (← getEnv).find? `Contracts.VaultFromSolidity.deposit
    | throwError "missing imported deposit"
  for dep in [``Verity.setMapping, ``Verity.setStorage, ``Verity.Stdlib.Math.safeAdd] do
    unless deposit.value.getUsedConstants.contains dep do
      throwError "missing source-derived deposit operation: {dep}"
  logInfo "CHECKED_TRANSPARENT_DECLARATIONS"
solidity_contract Existing from "../../Contracts/VaultFromSolidity/Vault.sol"
run_cmd do
  let original ← getEnv
  let mut rejected := false
  try
    SolidityImporter.elabSolidityContract
      (← `(command| solidity_contract $(mkIdent `Existing):ident from "../../Contracts/VaultFromSolidity/Vault.sol"))
  catch _ => rejected := true
  unless rejected do throwError "duplicate alias accepted"
  let some (.defnInfo before) := original.find? `Existing.deposit
    | throwError "missing initial declaration"
  let some (.defnInfo after) := (← getEnv).find? `Existing.deposit
    | throwError "lost initial declaration"
  unless before.value == after.value && before.type == after.type do
    throwError "duplicate alias changed prior declaration"
  logInfo "DUPLICATE_ALIAS_REJECTED"
''')
            output = run(root, [LAKE, "env", "lean", str(probe)])
            check("CHECKED_TRANSPARENT_DECLARATIONS" in output and
                  "DUPLICATE_ALIAS_REJECTED" in output,
                  "safe transparent readable definitions and collision rollback")
            check("Verity.setMapping" in output and "Verity.setStorage" in output and
                  "safeAdd" in output,
                  "#print deposit exposes readable source-derived behavior")
        finally:
            probe.unlink(missing_ok=True)

        before = artifacts()
        build()
        check(before == artifacts(), "unchanged build reuses Vault artifacts")

        theorem_starts = [
            (match.group(1), line_no)
            for line_no, line in enumerate(proof_text.splitlines(), 1)
            if (match := re.match(r"theorem\s+([A-Za-z0-9_']+)", line.strip()))
        ]
        theorem_ranges = {
            name: (start, theorem_starts[index + 1][1] - 1 if index + 1 < len(theorem_starts)
                   else len(proof_text.splitlines()))
            for index, (name, start) in enumerate(theorem_starts)
        }

        edit_source(original.replace(b"assets", b"depositAmount"))
        build()
        check(True, "declaration-ID based parameter rename preserves proofs")
        edit_source(original)
        build()

        for name, theorem, old, new in (
            ("deposit behavior", "deposit_meets_spec", b"totalSupply += assets;", b"totalSupply = assets;"),
            ("getter behavior", "balance_meets_spec", b"return shareBalances[account];", b"return totalAssets;"),
        ):
            check(original.count(old) == 1, name + " mutation has one source target")
            before = artifacts()
            edit_source(original.replace(old, new))
            output = build(False, "Contracts.VaultFromSolidity.Proofs.Execution")
            error_lines = [int(value) for value in re.findall(
                r"Contracts/VaultFromSolidity/Proofs/Execution\.lean:(\d+):", output)]
            start, end = theorem_ranges[theorem]
            check(any(start <= line <= end for line in error_lines),
                  name + f" mutation breaks {theorem}")
            check(before != artifacts(), name + " preserved-mtime edit refreshes artifacts")
            edit_source(original)
            build()

        for name, old, new, diagnostic in (
            ("contract layout at", b"contract Vault {", b"contract Vault layout at 100 {", "layout at"),
            ("initializer", b"uint256 public totalAssets;", b"uint256 public totalAssets = 1;", "initializer"),
            ("unchecked block", b"totalAssets += assets;", b"unchecked { totalAssets += assets; }", "UncheckedBlock"),
            ("loop", b"totalAssets += assets;", b"while (assets < totalAssets) { totalAssets += assets; }", "WhileStatement"),
            ("second contract", b"contract Vault {", b"contract Other {}\ncontract Vault {", "exactly one"),
            ("multiplication", b"totalAssets += assets;", b"totalAssets = totalAssets * assets;", "unsupported binary"),
        ):
            edit_source(original.replace(old, new))
            output = build(False, diagnostic)
            check(re.search(r"Contracts/VaultFromSolidity/Vault.sol:\d+:\d+:", output) is not None,
                  name + " rejected with source position")
        edit_source(original)
        build()

        with tempfile.TemporaryDirectory(prefix="verity-vault-outside-", dir=ROOT.parent) as outside:
            escaped = Path(outside) / "Vault.sol"
            escaped.write_bytes(original)
            source.unlink()
            source.symlink_to(escaped)
            try:
                probe.write_text('''import Contracts.VaultFromSolidity.Importer.Importer
solidity_contract Escaped from "../../Contracts/VaultFromSolidity/Vault.sol"
''')
                run(root, [LAKE, "env", "lean", str(probe)], False, "source outside package")
                check(True, "registered-source symlink escape rejected")
            finally:
                probe.unlink(missing_ok=True)
                source.unlink()
                edit_source(original)
        build()

        before = artifacts()
        digest_before = source_digest()
        importer.write_bytes(importer_original + b"\n-- acceptance translation identity probe\n")
        os.utime(importer, ns=(importer_stamp.st_atime_ns, importer_stamp.st_mtime_ns))
        build()
        check(before != artifacts(), "Lean importer content change invalidates Vault artifacts")
        check(digest_before != source_digest(), "Lean importer content changes sourceDigest")
        importer.write_bytes(importer_original)
        build()

        policy = root / "lakefile.lean"
        policy_original = policy.read_bytes()
        before = artifacts()
        policy.write_bytes(policy_original + b"\n-- acceptance build-policy probe\n")
        build()
        check(before != artifacts(), "build-policy content change invalidates Vault artifacts")
        policy.write_bytes(policy_original)
        build()

        compiler_stamp = compiler.stat()
        compiler.write_bytes(compiler_original + b"\nacceptance-check\n")
        os.utime(compiler, ns=(compiler_stamp.st_atime_ns, compiler_stamp.st_mtime_ns))
        build(False, "compiler checksum mismatch")
        check(True, "compiler content mutation fails closed")
        compiler.write_bytes(compiler_original)
        build()

        # Synthetic compiler-output probes test the JSON boundary itself. The
        # temporary wrapper is checksummed and accepted only in this disposable
        # package; production still executes the pinned binary directly.
        real_compiler = compiler.with_name("solc-real")
        pin = b"1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468"
        for mode, diagnostic in (
            ("ast", "unexpected AST fields"),
            ("metadata", "unexpected AST fields"),
            ("typed", "invalid AST metadata field Assignment.isLValue"),
            ("missing", "missing AST fields"),
            ("span", "source span outside registered source"),
            ("layout", "missing/packed layout"),
        ):
            try:
                real_compiler.write_bytes(compiler_original)
                real_compiler.chmod(0o755)
                compiler.write_text(f'''#!/usr/bin/env python3
import json, pathlib, subprocess, sys
real = pathlib.Path(__file__).with_name("solc-real")
p = subprocess.run([str(real), *sys.argv[1:]], input=sys.stdin.buffer.read(), capture_output=True)
if "--standard-json" not in sys.argv:
    sys.stdout.buffer.write(p.stdout); sys.stderr.buffer.write(p.stderr); raise SystemExit(p.returncode)
o = json.loads(p.stdout)
if {mode!r} in ("ast", "metadata", "typed", "missing", "span"):
    def mutate(x):
        if isinstance(x, dict):
            if {mode!r} == "ast" and x.get("nodeType") == "Assignment":
                x["unknownExecutableField"] = True; return True
            if {mode!r} == "metadata" and x.get("nodeType") == "StructuredDocumentation":
                x["unexpectedExecutable"] = {{"nodeType": "UncheckedBlock", "id": 999999, "src": "0:0:0"}}
                return True
            if {mode!r} == "typed" and x.get("nodeType") == "Assignment":
                x["isLValue"] = {{"nodeType": "UncheckedBlock", "id": 999999, "src": "0:0:0"}}
                return True
            if {mode!r} == "missing" and x.get("nodeType") == "Assignment":
                del x["isPure"]
                return True
            if {mode!r} == "span" and x.get("nodeType") == "Assignment":
                start, size, _ = x["src"].split(":")
                x["src"] = f"{{start}}:{{size}}:999"
                return True
            return any(mutate(v) for v in x.values())
        if isinstance(x, list): return any(mutate(v) for v in x)
        return False
    assert mutate(o)
else:
    o["contracts"]["Contracts/VaultFromSolidity/Vault.sol"]["Vault"]["storageLayout"]["storage"][0]["offset"] = 1
sys.stdout.write(json.dumps(o))
''')
                compiler.chmod(0o755)
                wrapper_hash = hashlib.sha256(compiler.read_bytes()).hexdigest().encode()
                check(pin in importer_original, "compiler pin occurs in Lean importer")
                importer.write_bytes(importer_original.replace(pin, wrapper_hash))
                run(root, [LAKE, "build", "VaultSolidityImporter"])
                build(False, diagnostic)
                check(True, f"synthetic {mode} compiler output fails closed")
            finally:
                real_compiler.unlink(missing_ok=True)
                compiler.write_bytes(compiler_original)
                compiler.chmod(0o755)
                importer.write_bytes(importer_original)
        build()

        # Corrupt a late declaration's type. Synchronous checking must reject it
        # before any declaration from the failed namespace escapes the transaction.
        try:
            importer.write_bytes(importer_original.replace(
                b"  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })",
                b'  let type := if name.toString.endsWith ".deposit" then mkConst ``Nat else type\n'
                b"  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })",
            ))
            run(root, [LAKE, "build", "VaultSolidityImporter"])
            probe.write_text('''import Contracts.VaultFromSolidity.Importer.Importer
open Lean Elab Command
set_option Elab.async true
run_cmd do
  let mut rejected := false
  try
    SolidityImporter.elabSolidityContract
      (← `(command| solidity_contract $(mkIdent `Broken):ident from "../../Contracts/VaultFromSolidity/Vault.sol"))
  catch e =>
    rejected := true
    logInfo m!"EXPECTED_KERNEL_ERROR {e.toMessageData}"
  unless rejected do throwError "malformed declaration accepted"
  for suffix in ["totalAssetsSlot", "totalSupplySlot", "shareBalancesSlot",
                 "totalAssets", "totalSupply", "shareBalances", "deposit", "sourceDigest"] do
    if (← getEnv).contains (`Broken ++ Name.mkSimple suffix) then
      throwError "partial declaration escaped rollback: {suffix}"
  logInfo "KERNEL_REJECTION_ROLLED_BACK"
''')
            output = run(root, [LAKE, "env", "lean", str(probe)])
            check("KERNEL_REJECTION_ROLLED_BACK" in output and "(kernel)" in output,
                  "malformed late declaration rejected synchronously with full rollback")
        finally:
            probe.unlink(missing_ok=True)
            importer.write_bytes(importer_original)
        build()

        check(set(root.rglob("*.lean")) == lean_sources,
              "no generated model .lean files")
        check(source.read_bytes() == original and importer.read_bytes() == importer_original,
              "temporary mutations restored; final baseline passes")
        print(f"PASS all Lean-only Vault acceptance checks ({len(theorem_names)} audited theorems)", flush=True)


if __name__ == "__main__":
    main()
