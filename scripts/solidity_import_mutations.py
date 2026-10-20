#!/usr/bin/env python3
"""Mutation checks for the Solidity importer.

Each case copies the smoke project, changes one thing, and elaborates
`solidity_import`. A reached helper, a return-order change, and a layout
change must make the witness check fail. An unreached `for` stays importable.
Reaching that `for` must be rejected with a source position, and the failed
process must not leave an olean.
"""

import argparse
import os
import shutil
import json
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from solidity_differential.check_interface_static_call_mutations import MUTANTS as INTERFACE_MUTANTS
from solidity_differential.check_interface_word_static_call_mutations import (
    MUTANTS as INTERFACE_WORD_MUTANTS)
from solidity_differential.check_create2_struct_emit_mutations import MUTANTS as CREATE2_STRUCT_EMIT_MUTANTS
from solidity_differential.check_external_code_and_low_level_call_mutations import (
    MUTANTS as LOW_LEVEL_CALL_MUTANTS)
from solidity_differential.check_extcodecopy_struct_decode_mutations import (
    MUTANTS as EXTCODECOPY_STRUCT_DECODE_MUTANTS)

ROOT = Path(__file__).resolve().parents[1]
SOLC = ROOT / ".lake/solidity-import/solc-0.8.34"
WORK = ROOT / ".lake/import-mutations"
SMOKE = ROOT / "Contracts/SolidityImportSmoke"
GOLDEN = SMOKE / "model.golden"
# Provisioned by `setup()`; campaign modules import eth_hash/eth_abi from it.
VENV_PYTHON = ROOT / ".lake/slice-testing-venv/bin/python"

HEADER = """
import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Coverage

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.Denote

solidity_import imported from "{root}" entry "Slice.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function f(Mkt, bytes32, address)
"""

WITNESS = r"""
def sliceOracle : DenoteOracle where
  mappingSlot base key := base + key + 1
  keccakMemorySlice _ _ _ := 0

def packHalves (lo hi : Nat) : Nat := lo + hi * 2 ^ 128

def witnessWorld (credit pending lossFactor lastLoss lastAccrual : Nat) : Verity.ContractState :=
  Verity.defaultState.withStorageWords fun key =>
    let word :=
      match key with
      | .slot 5 => packHalves credit pending
      | .slot 6 => packHalves lastLoss lastAccrual
      | .slot 3 => packHalves 0 lossFactor
      | _ => 0
    Verity.Core.Uint256.ofNat word

def witnessCalldata (maturity : Nat) : List Nat :=
  [96, 1, 2, 0, 96, maturity, 0]

def runWitness (world : Verity.ContractState) (timestamp maturity : Nat) : Option (List Nat) :=
  match imported.model.functions with
  | fn :: _ =>
    let result := denoteFunction sliceOracle imported.model fn
      { sender := 0, functionSelector := 0, blockTimestamp := timestamp, args := witnessCalldata maturity } world
    if result.success then some result.returnWords else none
  | [] => none

def body : List Stmt :=
  match imported.model.functions with
  | fn :: _ => fn.body
  | [] => []

#eval IO.println imported.report.sourceDigest

#eval show IO Unit from do
  let success := runWitness (witnessWorld 100 10 0 0 0) 50 100
  unless success == some [95, 5, 5] do
    throw (IO.userError s!"witness changed: {success}")
  let reverted := runWitness (witnessWorld 1 2 0 0 0) 1 1
  unless reverted == none do
    throw (IO.userError s!"revert witness changed: {reverted}")
  IO.println imported.report.sourceDigest
"""


def lean(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def write_project(name: str, mutate) -> Path:
    dest = WORK / name
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    shutil.copy(SMOKE / "Slice.sol", dest / "Slice.sol")
    shutil.copy(SMOKE / "Lib.sol", dest / "Lib.sol")
    mutate(dest)
    return dest


def expect_success(name: str, project: Path, witness: bool, extra: str = "") -> str:
    lean_path = project / "Check.lean"
    text = HEADER.format(root=project)
    if witness:
        text += WITNESS
    lean_path.write_text(text + extra)
    result = lean(lean_path)
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(f"{name}: expected success")
    print(f"pass {name}")
    return result.stdout


def expect_failure(name: str, project: Path, needle: str) -> str:
    lean_path = project / "Check.lean"
    olean = project / "Check.olean"
    if olean.exists():
        olean.unlink()
    lean_path.write_text(HEADER.format(root=project) + WITNESS)
    result = subprocess.run(
        ["lake", "env", "lean", str(lean_path), "-o", str(olean)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    blob = result.stdout + result.stderr
    if result.returncode == 0 or needle not in blob or olean.exists():
        sys.stderr.write(blob)
        raise SystemExit(f"{name}: expected rejection containing {needle!r}")
    print(f"pass {name}")
    return blob


def unchanged(dest: Path) -> None:
    return None


def uninitialized_local(dest: Path) -> None:
    path = dest / "Slice.sol"
    source = path.read_text()
    old = "uint128 credit = p.credit;"
    assert old in source
    path.write_text(source.replace(old, "uint128 ignored;\n        " + old))


def call_unused_from_loss(dest: Path) -> None:
    lib = (dest / "Lib.sol").read_text()
    assert "i < 3; i++" in lib
    (dest / "Lib.sol").write_text(lib.replace("i < 3; i++", "i < 3; i += 2"))
    text = (dest / "Slice.sol").read_text()
    old = "return marketState[market].lossFactor;"
    assert old in text
    (dest / "Slice.sol").write_text(text.replace(old, "uint256 ignored = L.unused();\n        " + old))


def call_supported_unused(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace(
        "uint128 credit = p.credit;",
        "uint256 ignored = L.unused();\n        uint128 credit = p.credit;",
    )
    (dest / "Slice.sol").write_text(text)


def call_unused(dest: Path) -> None:
    lib = (dest / "Lib.sol").read_text()
    assert "i < 3; i++" in lib
    (dest / "Lib.sol").write_text(lib.replace("i < 3; i++", "i < 3; i += 2"))
    call_supported_unused(dest)



def swap_returns(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace(
        "return (uint128(post) - fee, uint128(postFee) - fee, fee);",
        "return (fee, uint128(postFee) - fee, uint128(post) - fee);",
    )
    (dest / "Slice.sol").write_text(text)


def change_rounding(dest: Path) -> None:
    # Witness A divides evenly, so floor versus ceil is invisible there.
    # An extra division in the reached helper changes that witness.
    text = (dest / "Lib.sol").read_text()
    text = text.replace("return (x * y) / d;", "return (x * y) / d / 2;")
    (dest / "Lib.sol").write_text(text)


def change_factor(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace(
        "postFee.mulDivDown(end - lastAccrual, m.maturity - lastAccrual)",
        "postFee.mulDivDown(end - lastAccrual + 50, m.maturity - lastAccrual)",
    )
    (dest / "Slice.sol").write_text(text)


def change_field(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace("uint128 credit = p.credit;", "uint128 credit = p.pendingFee;")
    (dest / "Slice.sol").write_text(text)


def swap_layout(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace(
        "uint128 credit;\n    uint128 pendingFee;",
        "uint128 pendingFee;\n    uint128 credit;",
    )
    (dest / "Slice.sol").write_text(text)


def helper_local_collision(dest: Path) -> None:
    # The caller also has `credit`. Inlining must not overwrite that binding.
    path = dest / "Lib.sol"
    path.write_text(path.read_text().replace(
        "return (x * y) / d;", "uint256 credit = x * y; return credit / d;"))


def generated_name_collision(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace("credit = p.credit", "_verity_slice_tmp_0 = p.credit")
                    .replace("credit.mulDivDown", "_verity_slice_tmp_0.mulDivDown")
                    .replace("credit > 0", "_verity_slice_tmp_0 > 0")
                    .replace("credit - post", "_verity_slice_tmp_0 - post")
                    .replace(", credit)", ", _verity_slice_tmp_0)"))


def unrelated_layout(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace(
        "contract C {", "struct Unused { int128 signedValue; }\ncontract C {").replace(
        "public marketState;", "public marketState;\n    mapping(bytes32 => Unused) private unusedState;"))


def named_arguments(dest: Path) -> None:
    path = dest / "Lib.sol"
    path.write_text(path.read_text().replace(
        "return (x * y) / d;", "return named({d: d, y: y, x: x});"))
    with path.open("a") as out:
        out.write("\nfunction named(uint256 x, uint256 y, uint256 d) pure returns (uint256) { return x*y/d; }\n")


def implicit_return(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace(
        "returns (uint128, uint128, uint128)", "returns (uint128 a, uint128 b, uint128)").replace(
        "return (uint128(post) - fee, uint128(postFee) - fee, fee);", ""))


def named_implicit_return(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace(
        "returns (uint128, uint128, uint128)", "returns (uint128 a, uint128 b, uint128 c)").replace(
        "return (uint128(post) - fee, uint128(postFee) - fee, fee);",
        "a = uint128(post) - fee; b = uint128(postFee) - fee; c = fee;"))


def former_projection_name_collision(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace("bytes32 id,", "bytes32 m_maturity,")
                    .replace("[id]", "[m_maturity]"))


def shadow_builtin(dest: Path) -> None:
    path = dest / "Slice.sol"
    path.write_text(path.read_text().replace("uint256 ignored;", "uint256 timestamp;")
                    .replace("Mkt memory m,", "Mkt memory block,")
                    .replace("m.maturity", "block.maturity"))


def narrow_multiply(dest: Path) -> None:
    (dest / "Slice.sol").write_text("""pragma solidity 0.8.34;
struct Mkt { uint256 maturity; }
contract C {
    function f(Mkt memory m, bytes32 id, address user) external pure returns (uint128, uint128, uint128) {
        uint248 x = uint248(m.maturity);
        uint248 product = x * x;
        return (uint128(product), 0, 0);
    }
}
""")


def digest_of(blob: str) -> str:
    lines = [line.strip() for line in blob.splitlines() if len(line.strip()) == 64]
    if not lines:
        raise SystemExit(f"no digest in output:\n{blob}")
    return lines[-1]


def setup() -> None:
    """Serial preparation shared by every task (builds and venvs must not race)."""
    if not SOLC.is_file():
        raise SystemExit(f"missing {SOLC}")
    # The checks import the status driver, which `lake build SolidityImportSmoke` does not build.
    subprocess.run(["lake", "build", "Compiler.SolidityImport.Differential"], cwd=ROOT, check=True)
    WORK.mkdir(parents=True, exist_ok=True)
    # Provision the differential venv and pinned compilers once, before workers share them.
    subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"), "--help"],
                   cwd=ROOT, check=True, stdout=subprocess.DEVNULL)


def prefix_checks(update_golden: bool) -> None:
    subprocess.run([str(VENV_PYTHON), str(ROOT / "scripts/solidity_differential/check_require_rejections.py")],
                   cwd=ROOT, check=True)
    snapshot = WORK / "model.txt"
    snapshot.unlink(missing_ok=True)
    base = expect_success("unreached-for", write_project("base", unchanged), witness=True,
                          extra=f'\n#eval IO.FS.writeFile "{snapshot}" (toString (repr imported.model) ++ "\\n")\n')
    # Refactors of the importer must reproduce the imported model exactly.
    if update_golden:
        shutil.copy(snapshot, GOLDEN)
    elif snapshot.read_text() != GOLDEN.read_text():
        raise SystemExit(f"imported model differs from {GOLDEN}; review, then rerun with --update-golden")
    print("pass golden-model")
    expect_success("helper-local-hygiene", write_project("helper-local", helper_local_collision), witness=True)
    expect_success("generated-name-hygiene", write_project("generated-name", generated_name_collision), witness=True)
    expect_success("unrelated-layout", write_project("unrelated-layout", unrelated_layout), witness=True)
    expect_failure("named-arguments", write_project("named-arguments", named_arguments), "named call arguments")
    expect_failure("implicit-return", write_project("implicit-return", implicit_return), "explicit root return")
    expect_success("named-implicit-return", write_project("named-implicit-return", named_implicit_return), witness=True)
    # Scalar defaults are now supported; retain the original execution witness.
    expect_success("uninitialized-local", write_project("uninitialized-local", uninitialized_local), witness=True)
    def unsupported_default(dest: Path) -> None:
        uninitialized_local(dest)
        path = dest / "Slice.sol"
        source = path.read_text()
        assert source.count("uint128 ignored;") == 1
        path.write_text(source.replace("uint128 ignored;", "int128 ignored;"))
    diagnostic = expect_failure("signed-default-local", write_project("signed-default-local", unsupported_default),
                                "unsupported default local type int128")
    if not re.search(r"Slice\.sol:\d+:\d+: VariableDeclaration:", diagnostic):
        raise SystemExit("unsupported default local lacks a Solidity source diagnostic")
    # The old flattened name is now legal: full tuple parameters must retain their
    # identity and the unchanged execution witness must still hold.
    expect_success("former-projection-name-hygiene",
                   write_project("projection-name", former_projection_name_collision), witness=True,
                   extra=r'''
#eval show IO Unit from do
  let some fn := imported.model.functions.head? | throw (IO.userError "missing imported function")
  let names := fn.params.map (·.name)
  unless names == ["m", "m_maturity", "user"] && imported.report.projections.isEmpty do
    throw (IO.userError "complete tuple signature was replaced by scalar projections")
''')
    namespaced = WORK / "base/Namespaced.lean"
    namespaced.write_text(HEADER.format(root=WORK / "base").replace(
        "solidity_import imported", "namespace Nested\nsolidity_import imported") +
        "\nend Nested\nexample : modelImportCovered Nested.imported.model = true := Nested.imported.covered\n")
    result = lean(namespaced)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    print("pass namespaced-import")
    expect_success("shadowed-block", write_project("shadowed-block", shadow_builtin), witness=False,
                   extra=WITNESS[:WITNESS.index("#eval")] + r'''
#eval show IO Unit from do
  let some fn := imported.model.functions.head? | throw (IO.userError "missing imported function")
  -- The first tuple member is the shadowing struct's timestamp (50), whereas
  -- the real environment timestamp is 999. Confusing them changes the fee.
  let result := denoteFunction sliceOracle imported.model fn
    { sender := 0, functionSelector := 0, blockTimestamp := 999,
      args := [96, 1, 2, 50, 96, 100, 0] } (witnessWorld 100 10 0 0 0)
  unless result.success && result.returnWords == [95, 5, 5] do
    throw (IO.userError "shadowed block was treated as a builtin")
  unless fn.params.map (·.name) == ["block", "id", "user"] &&
      imported.report.projections.isEmpty do
    throw (IO.userError "shadowed struct lost its complete ABI signature")
''')
    expect_success("narrow-multiply-overflow", write_project("narrow-multiply", narrow_multiply), witness=False,
                   extra=r'''
#eval show IO Unit from do
  let oracle : DenoteOracle := { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }
  let some fn := imported.model.functions.head? | throw (IO.userError "missing imported function")
  -- Mkt is a static one-word tuple in this fixture, followed by id and user.
  let run := fun maturity => denoteFunction oracle imported.model fn
    { sender := 0, functionSelector := 0, args := [maturity, 1, 2] } Verity.defaultState
  let small := run 3
  unless small.success && small.returnWords == [9, 0, 0] do
    throw (IO.userError "small uint248 product changed")
  unless !(run (2^128)).success do
    throw (IO.userError "uint248 product overflow was accepted")
''')
    two_roots = WORK / "base/TwoRoots.lean"
    two_roots.write_text("import Compiler.SolidityImport.Differential\n" + HEADER.format(root=WORK / "base") + WITNESS + f'''
solidity_import both from "{WORK / "base"}" entry "Slice.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function f(Mkt, bytes32, address)
  function lossOf(bytes32)

#eval show IO Unit from do
  -- A second root must not change how the first one is lowered.
  let single := imported.model.functions
  match both.model.functions with
  | [f, loss] =>
      unless toString (repr [f]) == toString (repr single) do
        throw (IO.userError "adding a root changed the first function")
      unless loss.name == "lossOf" && loss.params.map (·.name) == ["market"] do
        throw (IO.userError s!"unexpected second root {{loss.name}}")
  | _ => throw (IO.userError "expected two imported functions")
  unless both.model.fields.map (·.name) == ["position", "marketState"] do
    throw (IO.userError "roots do not share one field list")
  unless both.report.roots == ["f", "lossOf"] do
    throw (IO.userError "report roots changed")
  -- One status per root. Compiler-proof coverage is never claimed.
  unless both.report.functions.map (·.function) == ["f", "lossOf"] &&
      both.report.functions.all (·.denoteCovered) &&
      both.report.functions.all (·.compilerProof == CompilerProofStatus.unavailable noCompilerProofReason) do
    throw (IO.userError s!"unexpected function statuses {{repr both.report.functions}}")
  let status := Differential.statusText both.model both.report
  IO.println status
  unless (status.splitOn "compilable true").length == 3 &&
      (status.splitOn "compilerProofCovered unavailable").length == 3 do
    throw (IO.userError "status table changed")
''')
    result = lean(two_roots)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    print("pass two-roots")
    for name, extra, needle in [
            ("duplicate-root", "  function f(Mkt, bytes32, address)\n  function f(Mkt, bytes32, address)\n", "imported twice"),
            ("unknown-root", "  function nope(bytes32)\n", "no function C.nope(bytes32)")]:
        bad = WORK / f"base/{name}.lean"
        bad.write_text(HEADER.format(root=WORK / "base").replace("  function f(Mkt, bytes32, address)\n", extra))
        blob = lean(bad)
        if blob.returncode == 0 or needle not in blob.stdout + blob.stderr:
            raise SystemExit(f"{name}: expected rejection containing {needle!r}\n{blob.stdout}{blob.stderr}")
        print(f"pass {name}")
    # Generated typed accessors must not shadow `model`, `report`, ...
    clash = write_project("accessor-collision", lambda d: (d / "Slice.sol").write_text(
        (d / "Slice.sol").read_text().replace("function lossOf(", "function model(")))
    bad = clash / "Clash.lean"
    bad.write_text(HEADER.format(root=clash).replace(
        "  function f(Mkt, bytes32, address)\n", "  function model(bytes32)\n"))
    blob = lean(bad)
    if blob.returncode == 0 or "collides with the generated" not in blob.stdout + blob.stderr:
        raise SystemExit(f"accessor-collision: expected rejection\n{blob.stdout}{blob.stderr}")
    print("pass accessor-collision")
    # An unsupported construct reached from the second root names that root.
    second = write_project("second-root", call_unused_from_loss)
    bad = second / "SecondRoot.lean"
    bad.write_text(HEADER.format(root=second).replace(
        "  function f(Mkt, bytes32, address)\n",
        "  function f(Mkt, bytes32, address)\n  function lossOf(bytes32)\n"))
    blob = lean(bad)
    text = blob.stdout + blob.stderr
    if blob.returncode == 0 or "closure: C.lossOf -> L.unused" not in text:
        raise SystemExit(f"second-root-unsupported: expected the lossOf call path\n{text}")
    print("pass second-root-unsupported")
    repeated = expect_success("deterministic", WORK / "base", witness=True)
    if digest_of(base) != digest_of(repeated):
        raise SystemExit("identical input did not reproduce the digest")
    rounding = expect_failure("rounding-detected", write_project("rounding", change_rounding), "witness changed")
    expect_failure("factor-detected", write_project("factor", change_factor), "witness changed")
    expect_failure("field-detected", write_project("field", change_field), "witness changed")
    expect_failure("return-order", write_project("returns", swap_returns), "witness changed")
    expect_failure("layout", write_project("layout", swap_layout), "witness changed")
    expect_success("reachable-compound-for", write_project("reachable-compound-for", call_supported_unused), witness=True)
    diagnostic = expect_failure("reachable-for", write_project("reachable", call_unused), "unsupported")
    assert "[solidity-import:unsupported]" in diagnostic and "closure:" in diagnostic
    assert "Lib.sol:" in diagnostic and "closure: C.f -> L.unused" in diagnostic, diagnostic
    if digest_of(base) == digest_of(rounding):
        raise SystemExit("helper change did not move the digest")
    print("pass helper-digest")


# Compile and execute actual Denote mutants: a build failure is invalid,
# not a detected semantic mutation. These regressions compare EVM bytes.
DIFFERENTIAL_MUTANTS = ("denote-panic-selector", "denote-panic-endian",
                   "import-msg-sender", "import-address-this",
                   "import-block-number", "import-block-chainid",
                   "import-require-condition", "denote-require-selector",
                   "import-custom-require-condition", "denote-custom-require-selector",
                   "denote-custom-require-argument",
                   "import-scalar-read", "import-scalar-slot", "import-scalar-offset",
                   "import-scalar-write", "import-scalar-delete", "import-void-fallthrough",
                   "denote-scalar-sibling-mask", "import-bare-empty-revert",
                   'import-mapping-layout',
                   'import-mapping-read-one',
                   'import-mapping-read-two',
                   'import-mapping-write-one',
                   'import-mapping-write-two',
                   'import-mapping-delete',
                   'import-mapping-bool-literal',
                   'import-mapping-bool-read', 'import-logical-and-branch',
                   'import-logical-or-branch', 'import-logical-initial-value',
                   'import-yul-result-scope', 'import-yul-numeric-literal', 'import-yul-numeric-add', 'import-named-helper-default', 'import-named-helper-fallthrough', 'import-named-helper-assembly', 'import-named-helper-width', 'import-named-helper-bool', 'import-named-helper-frame', 'import-named-helper-branch', 'import-byte-local-pointer', 'import-byte-local-length', 'import-byte-local-initialize', 'import-discarded-helper-drop', 'import-discarded-helper-emit', 'import-array-write-order', 'import-array-write-capture', 'import-fixed-array-snapshot-read', 'import-fixed-array-read-bound', 'import-fixed-array-snapshot-bound', 'import-fixed-array-word', 'import-fixed-array-bit', 'import-fixed-array-capture', 'import-fixed-array-read', 'import-fixed-array-bound', 'import-fixed-array-write', 'import-fixed-array-two-keys', 'import-fixed-array-snapshot', 'import-fixed-array-delete', 'import-helper-effect-drop', 'import-packed-member-delete', 'import-packed-member-value', 'import-packed-member-target', 'import-packed-member-two-keys', 'import-packed-member-capture', 'import-helper-loop-block', 'import-helper-loop-branch', 'import-helper-loop-nested', 'import-helper-loop-drop', 'import-helper-loop-effect', 'import-helper-loop-emit', 'import-invariant-for-bound', 'import-invariant-for-counter', 'import-local-write-value', 'import-local-write-delete', 'import-default-local-zero', 'import-modulo-value', 'import-modulo-zero', 'import-constant-array-element', 'import-constant-array-selection',
                   'import-constant-array-bound', 'import-numeric-leading-dot', 'import-numeric-separators',
                   'import-numeric-constant-product', 'import-numeric-constant-sum', 'import-numeric-constant-value', 'import-numeric-decimal-scale',
                   'import-numeric-positive-exponent', 'import-numeric-negative-exponent',
                   'import-numeric-hex-value', 'import-numeric-integral-value',
                   'import-numeric-unit-minutes', 'import-numeric-unit-hours',
                   'import-numeric-unit-days', 'import-numeric-unit-weeks',
                   'import-numeric-unit-gwei', 'import-numeric-unit-ether',
                   'import-numeric-unit-one',
                   'import-if-root-swap', 'import-if-root-else-drop',
                   'import-if-helper-swap', 'import-if-helper-guard-swap',
                   'import-abi-source-offset', 'import-abi-drop', 'import-abi-offset', 'import-abi-uint-bound',
                   'import-abi-address-bound', 'import-abi-bool-bound',
                   'import-abi-inclusive', 'import-abi-revert',
                   'import-struct-tuple-order',
                   'import-struct-memory-drop',
                   'import-struct-calldata-eager',
                   'import-struct-calldata-drop',
                   'import-struct-member-value',
                   'import-struct-member-offset',
                   'import-struct-head-base',
                   'import-struct-memory-offset',
                   'denote-struct-member-offset',
                   'denote-struct-member-name',
                   'denote-struct-member-value',

                   'import-event-converted-binding', 'import-event-indexed', 'import-event-drop', 'import-event-values',
                   'import-event-signature', 'observe-event-word', 'observe-event-narrow',
                   'observe-event-address', 'observe-event-bool',
                   'import-scalar-array-source-stride',
                   'import-scalar-array-memory-stride',
                   'import-scalar-array-validation',
                   'import-scalar-array-length',
                   'import-abi-length-for-capture', 'import-abi-length-for-zero', 'import-abi-array-length-calldata', 'import-abi-array-length-memory',
                   'import-nested-dynamic-struct-root-offset',
                   'import-nested-dynamic-struct-root-size',
                   'import-nested-dynamic-struct-calldata-array-size',
                   'import-nested-dynamic-struct-memory-panic',
                   'import-nested-dynamic-struct-struct-source-stride',
                   'import-nested-dynamic-struct-struct-pointer-stride',
                   'import-nested-dynamic-struct-struct-validation',
                   'import-nested-dynamic-struct-calldata-element-stride',
                   'import-nested-dynamic-struct-memory-element-stride',
                   'import-nested-dynamic-struct-member-validation',
                   'import-nested-dynamic-struct-root-scalar-validation',
                   'import-nested-dynamic-struct-memory-scalar-read',
                   'import-nested-dynamic-struct-calldata-scalar-read',
                   'import-nested-dynamic-struct-calldata-root-validation',
                   'import-nested-dynamic-struct-calldata-index-bounds',
                   'import-dynamic-root-parameter-offset')

# Removing an order guard must change a located rejection to admission.
GUARD_MUTANTS = ('import-helper-effect-binary-guard', 'import-helper-effect-argument-guard', 'import-helper-effect-classifier', 'import-yul-result-id-guard', 'import-solc-viair-guard', 'import-solc-uncollected-source-guard')

# Each isolated campaign recompiles `Compiler.SolidityImport.Import` in a private
# snapshot. With one worker per core that build alone takes ~14 minutes, on top of
# the baseline and mutated campaign runs, so 40 minutes was too tight. The nested
# harness steps keep their own timeouts; this one only bounds a whole task.
MUTANT_TIMEOUT = 3600


def run_differential_mutant(mutant: str) -> list:
    output = Path(tempfile.mkdtemp(prefix=f"{mutant}-", dir=WORK))
    subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"),
                    "--mutations", "--mutant", mutant, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=MUTANT_TIMEOUT)
    return json.loads((output / "mutation-results.json").read_text())


def differential_mutant(mutant: str) -> None:
    results = run_differential_mutant(mutant)
    if len(results) != 1 or results[0]["mutant"] != mutant or results[0]["status"] != "detected":
        raise SystemExit(f"{mutant}: expected a runtime differential divergence")
    print(f"pass {mutant}", flush=True)


def guard_mutant(mutant: str) -> None:
    results = run_differential_mutant(mutant)
    if (len(results) != 1 or results[0]['mutant'] != mutant
            or not results[0]['detected'] or not results[0]['baselinePassed']
            or results[0]['kind'] != 'unsupported-order-admission'):
        raise SystemExit(f'{mutant}: exact negative control guard mutation escaped detection')
    print(f'pass {mutant} exact rejection guard', flush=True)


def module_campaign(module: str, label: str, timeout: int, *extra: str) -> dict:
    output = module_campaign_output(module, label, timeout, *extra)
    return json.loads((output / "complete.json").read_text())


HASHING_MUTANTS = (
    "hash-word-stride", "hash-root-offset", "hash-root-field", "hash-static-root-field",
    "hash-array-length", "hash-array-destination-stride", "hash-literal-value",
    "hash-literal-length", "hash-packed-address-width", "hash-packed-scalar-value",
    "hash-copy-byte-shift", "hash-copy-zero-fill", "hash-buffer-identity",
    "hash-keccak-length", "hash-hex-number")


def hashing_mutant(mutant: str) -> None:
    hashing = module_campaign("check_hashing_mutations", f"hashing-{mutant}", MUTANT_TIMEOUT,
                              "--mutant", mutant)
    if hashing["exit"] != 0 or [r["mutant"] for r in hashing["results"]] != [mutant]:
        raise SystemExit(f"{mutant}: hashing mutation coverage incomplete")
    if not all(r["detected"] and r["baselinePassed"] and r["witness"]["deletion_minimal"]
               and r["witness"]["transactions"] for r in hashing["results"]):
        raise SystemExit(f"{mutant}: hashing mutants require minimal reproduced runtime witnesses")
    print(f"pass ABI hashing mutation {mutant}", flush=True)


def quote_integrity_check() -> None:
    # Quotation corruption is rejected before an executable model exists.
    quote_results = run_differential_mutant("import-modulo-quote")
    if (len(quote_results) != 1 or quote_results[0]["mutant"] != "import-modulo-quote"
            or not quote_results[0]["baselinePassed"]
            or quote_results[0]["kind"] != "model-integrity-rejection"
            or quote_results[0]["diagnostic"] != "internal: the elaborated model differs from the imported value"):
        raise SystemExit("modulo quotation corruption escaped the exact integrity check")
    print("pass import-modulo-quote integrity rejection", flush=True)


def environment_rejections() -> None:
    subprocess.run([str(VENV_PYTHON), str(ROOT / "scripts/solidity_differential/check_environment_rejections.py")],
                   cwd=ROOT, check=True, timeout=900)
    print("pass environment rejection campaign", flush=True)


# ~420 located rejections, one `lean` elaboration each (~20 min serially on an
# idle host): split into parts so shards can spread them.
STORAGE_REJECTION_PARTS = 4


def storage_rejections(part: int) -> None:
    subprocess.run([str(VENV_PYTHON), str(ROOT / "scripts/solidity_differential/check_storage_rejections.py"),
                    "--part", f"{part}/{STORAGE_REJECTION_PARTS}"],
                   cwd=ROOT, check=True, timeout=MUTANT_TIMEOUT)
    print(f"pass storage rejection campaign part {part}/{STORAGE_REJECTION_PARTS}", flush=True)


def abi_rejections() -> None:
    module_campaign_output("check_scalar_array_abi_rejections", "scalar-array-rejections", 900)
    module_campaign_output("check_nested_dynamic_struct_abi_rejections",
                           "nested-dynamic-struct-rejections", 900)
    print("pass ABI rejection campaigns", flush=True)


def module_campaign_output(module: str, label: str, timeout: int, *extra: str) -> Path:
    output = Path(tempfile.mkdtemp(prefix=label + "-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                f'runpy.run_module("solidity_differential.{module}",run_name="__main__")')
    subprocess.run([str(VENV_PYTHON), "-c", launcher, "--output", str(output), *extra],
                   cwd=ROOT, check=True, timeout=timeout)
    return output


def deployment_world_mutations() -> None:
    results = json.loads((module_campaign_output("check_deployment_world_mutations", "deployment-world-mutations",
                                                 MUTANT_TIMEOUT) / "mutation-results.json").read_text())
    names = {"denote-create2-drop-nonce", "denote-create2-empty-code", "denote-create2-drop-value",
             "denote-create2-drop-deposit", "denote-create2-ignore-collision"}
    if ({row['mutant'] for row in results} != names
            or not all(row['detected'] and row['baselinePassed'] and row['deletion_minimal']
                       and row['signature'] for row in results)):
        raise SystemExit("deployment-world mutations require actual minimal EVM/Lean witnesses")
    print("pass five deployment-world runtime mutations (A/B foundation; compiled route pending)", flush=True)


def create2_opcode_mutations() -> None:
    results = json.loads((module_campaign_output("check_create2_opcode_mutations", "create2-opcode-mutations",
                                                 MUTANT_TIMEOUT) / "mutation-results.json").read_text())
    names = {"create2-initcode-word-cost", "create2-eip150-divisor", "create2-parent-refund",
             "create2-memory-expansion"}
    if ({row['mutant'] for row in results} != names
            or not all(row['detected'] and row['baselinePassed'] and row['deletion_minimal']
                       and row['signature'] and len(row['witnessCaseIds']) == 1 for row in results)):
        raise SystemExit("CREATE2 opcode mutants require executed minimal EVM/Lean witnesses")
    print("pass four CREATE2 opcode runtime mutations (A/B foundation; compiled route pending)", flush=True)


def account_storage_mutations() -> None:
    results = json.loads((module_campaign_output("check_account_storage_mutations", "account-storage-conformance",
                                                 MUTANT_TIMEOUT) / "mutation-results.json").read_text())
    names = {"denote-physical-slot-account", "denote-physical-batch-account", "denote-physical-modify-account"}
    if ({row['mutant'] for row in results} != names
            or not all(row['detected'] and row['baselinePassed'] and row['implementationCompiles']
                       and row['kind'] == 'kernel-conformance-rejection' for row in results)):
        raise SystemExit("account storage mutations require valid implementations rejected by unchanged kernel assertions")
    print("pass three account storage kernel conformance mutations (not runtime witnesses)", flush=True)


def block_mutation() -> None:
    block_result = module_campaign("check_block_mutations", "block-mutations", MUTANT_TIMEOUT)
    if (block_result["mutant"] != "import-block-drop" or not block_result["detected"]
            or not block_result["baselinePassed"] or not block_result["witness"]["deletion_minimal"]):
        raise SystemExit("block mutation requires detected minimal runtime witness")
    print("pass import-block-drop", flush=True)


def reference_mutation() -> None:
    reference = module_campaign("check_reference_argument_mutations", "reference-mutations", MUTANT_TIMEOUT)
    if (reference["mutant"] != "import-reference-wrong-root" or not reference["detected"]
            or not reference["baselinePassed"] or not reference["witness"]["deletion_minimal"]):
        raise SystemExit("reference mutation requires detected minimal runtime witness")
    print("pass import-reference-wrong-root", flush=True)


def reference_boundary_mutations() -> None:
    result = module_campaign("check_reference_boundary_mutations", "reference-boundary", 2 * MUTANT_TIMEOUT)
    controls = result["results"]
    if result["exit"] != 0 or {c["mutant"] for c in controls} != {"external-library", "yul-shadow"}:
        raise SystemExit("reference boundary mutation coverage incomplete")
    if not all(c["detected"] and c["baselinePassed"] and c["unsupportedInputImported"] for c in controls):
        raise SystemExit("reference boundary mutants require actual unsupported admission")
    print("pass reference-boundary", flush=True)


def reference_location_mutation() -> None:
    result = module_campaign("check_reference_location_mutation", "reference-location", MUTANT_TIMEOUT)
    if (result["mutant"] != "import-reference-location-guard" or not result["detected"]
            or not result["baselinePassed"] or not result["unsupportedCopyImported"]):
        raise SystemExit("reference location mutant requires actual unsupported copy admission")
    print("pass reference-location", flush=True)


def byte_call_mutations() -> None:
    subprocess.run([sys.executable,
                    str(ROOT / "scripts/solidity_differential/check_byte_call_mutations.py")],
                   cwd=ROOT, check=True, timeout=MUTANT_TIMEOUT)
    print("pass canonical byte-call and exact empty-revert mutations", flush=True)


def interface_static_call_rejections() -> None:
    module_campaign_output("check_interface_static_call_rejections",
                           "interface-static-call-rejections", MUTANT_TIMEOUT)
    print("pass interface staticcall located rejections", flush=True)


def library_call_rejections() -> None:
    module_campaign_output("check_library_call_rejections",
                           "library-call-rejections", MUTANT_TIMEOUT)
    print("pass external library call located rejections", flush=True)


def interface_static_call_mutant(mutant: str) -> None:
    result = module_campaign("check_interface_static_call_mutations", mutant,
                             MUTANT_TIMEOUT, "--only", mutant)
    if (result["exit"] != 0 or result["selected"] != [mutant]
            or [r["mutant"] for r in result["results"]] != [mutant]
            or not all(r["detected"] and r["baselinePassed"] for r in result["results"])):
        raise SystemExit(f"interface staticcall mutant {mutant} was not detected")
    print(f"pass {mutant}", flush=True)


def interface_word_static_call_rejections() -> None:
    module_campaign_output("check_interface_word_static_call_rejections",
                           "interface-word-static-call-rejections", MUTANT_TIMEOUT)
    print("pass interface word staticcall located rejections", flush=True)


def interface_word_static_call_mutant(mutant: str) -> None:
    result = module_campaign("check_interface_word_static_call_mutations", mutant,
                             MUTANT_TIMEOUT, "--only", mutant)
    if (result["exit"] != 0 or result["selected"] != [mutant]
            or [r["mutant"] for r in result["results"]] != [mutant]
            or not all(r["detected"] and r["baselinePassed"] for r in result["results"])):
        raise SystemExit(f"interface word staticcall mutant {mutant} was not detected")
    print(f"pass {mutant}", flush=True)


def create2_struct_emit_rejections() -> None:
    module_campaign_output("check_create2_struct_emit_rejections",
                           "create2-struct-emit-rejections", MUTANT_TIMEOUT)
    print("pass CREATE2/struct-event located rejections", flush=True)


def create2_struct_emit_mutant(mutant: str) -> None:
    result = module_campaign("check_create2_struct_emit_mutations", mutant,
                             2 * MUTANT_TIMEOUT, "--only", mutant)
    if (result["exit"] != 0 or result["selected"] != [mutant]
            or [r["mutant"] for r in result["results"]] != [mutant]
            or not all(r["detected"] and r["baselinePassed"] for r in result["results"])):
        raise SystemExit(f"CREATE2/struct-event mutant {mutant} was not detected")
    print(f"pass {mutant}", flush=True)


def low_level_call_rejections() -> None:
    module_campaign_output("check_external_code_and_low_level_call_rejections",
                           "external-code-low-level-call-rejections", MUTANT_TIMEOUT)
    print("pass code-length/low-level call located rejections", flush=True)


def low_level_call_mutant(mutant: str) -> None:
    result = module_campaign("check_external_code_and_low_level_call_mutations", mutant,
                             2 * MUTANT_TIMEOUT, "--only", mutant)
    if (result["exit"] != 0 or result["selected"] != [mutant]
            or [r["mutant"] for r in result["results"]] != [mutant]
            or not all(r["detected"] and r["baselinePassed"] for r in result["results"])):
        raise SystemExit(f"code-length/low-level call mutant {mutant} was not detected")
    print(f"pass {mutant}", flush=True)


def extcodecopy_struct_decode_rejections() -> None:
    module_campaign_output("check_extcodecopy_struct_decode_rejections",
                           "extcodecopy-struct-decode-rejections", MUTANT_TIMEOUT)
    print("pass code-copy/struct-decode located rejections", flush=True)


def extcodecopy_struct_decode_mutant(mutant: str) -> None:
    result = module_campaign("check_extcodecopy_struct_decode_mutations", mutant,
                             2 * MUTANT_TIMEOUT, "--only", mutant)
    if (result["exit"] != 0 or result["selected"] != [mutant]
            or [r["mutant"] for r in result["results"]] != [mutant]
            or not all(r["detected"] and r["baselinePassed"] for r in result["results"])):
        raise SystemExit(f"code-copy/struct-decode mutant {mutant} was not detected")
    print(f"pass {mutant}", flush=True)


def tasks(update_golden: bool) -> list:
    """Independent work items, most expensive first (each runs in its own snapshot).

    Weights count importer rebuilds (~14 minutes each under full parallel load),
    the unit of cost; campaigns without a rebuild are weighted by their runtime.
    """
    items = [("prefix-checks", 2, lambda: prefix_checks(update_golden)),
             ("reference-boundary", 2, reference_boundary_mutations)]
    items += [(f"storage-rejections-{part}", 1, (lambda part=part: storage_rejections(part)))
              for part in range(STORAGE_REJECTION_PARTS)]
    items += [("quote-integrity", 1, quote_integrity_check),
             ("environment-rejections", 1, environment_rejections),
             ("abi-rejections", 1, abi_rejections),
             ("block-drop", 1, block_mutation),
             ("reference-wrong-root", 1, reference_mutation),
             ("reference-location", 1, reference_location_mutation),
             ("byte-call", 1, byte_call_mutations),
             ("deployment-world", 1, deployment_world_mutations),
             ("create2-opcode", 1, create2_opcode_mutations),
             ("account-storage", 1, account_storage_mutations),
             ("interface-static-call-rejections", 1, interface_static_call_rejections),
             ("interface-word-static-call-rejections", 1, interface_word_static_call_rejections),
             ("library-call-rejections", 1, library_call_rejections),
             ("create2-struct-emit-rejections", 1, create2_struct_emit_rejections),
             ("external-code-low-level-call-rejections", 1, low_level_call_rejections),
             ("extcodecopy-struct-decode-rejections", 1, extcodecopy_struct_decode_rejections)]
    items += [(m, 1, (lambda m=m: hashing_mutant(m))) for m in HASHING_MUTANTS]
    items += [(m, 1, (lambda m=m: differential_mutant(m))) for m in DIFFERENTIAL_MUTANTS]
    items += [(m, 1, (lambda m=m: guard_mutant(m))) for m in GUARD_MUTANTS]
    items += [(m, 1, (lambda m=m: interface_static_call_mutant(m))) for m in INTERFACE_MUTANTS]
    items += [(m, 1, (lambda m=m: interface_word_static_call_mutant(m)))
              for m in INTERFACE_WORD_MUTANTS]
    items += [(m, 2, (lambda m=m: create2_struct_emit_mutant(m))) for m in CREATE2_STRUCT_EMIT_MUTANTS]
    items += [(m, 2, (lambda m=m: low_level_call_mutant(m))) for m in LOW_LEVEL_CALL_MUTANTS]
    items += [(m, 2, (lambda m=m: extcodecopy_struct_decode_mutant(m)))
              for m in EXTCODECOPY_STRUCT_DECODE_MUTANTS]
    return items


def auto_jobs() -> int:
    """One worker per usable core minus two, bounded by memory.

    Each worker is a single-threaded Lean rebuild of the importer (~2.7 GiB
    peak) plus its campaign; budget 4 GiB per worker so hosts with less memory
    than cores (or a cgroup cap) do not swap. Campaigns also run their own
    `lean --run` and anvil processes, so two cores stay free for them: with one
    worker per core, campaign subprocesses overran their time budgets.
    """
    cores = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
    limits = []
    try:
        with open("/proc/meminfo") as meminfo:
            limits += [int(line.split()[1]) * 1024 for line in meminfo if line.startswith("MemAvailable:")]
    except OSError:
        pass
    try:
        cap = Path("/sys/fs/cgroup/memory.max").read_text().strip()
        if cap != "max":
            limits.append(int(cap))
    except (OSError, ValueError):
        pass
    by_memory = min(limits) // (4 << 30) if limits else cores
    return max(1, min(cores - 2, by_memory))


def shard_of(items: list, index: int, count: int) -> list:
    """Deterministic longest-processing-time assignment of tasks to shards."""
    loads = [0] * count
    chosen = []
    for item in items:
        target = min(range(count), key=lambda s: (loads[s], s))
        loads[target] += item[1]
        if target == index:
            chosen.append(item)
    return chosen


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update-golden", action="store_true")
    parser.add_argument("--shard", default="0/1", help="run shard I of N, written I/N")
    parser.add_argument("--jobs", default="1", help="parallel isolated campaigns, or 'auto' to size by cores and memory")
    parser.add_argument("--list", action="store_true", help="print the selected tasks and exit")
    parser.add_argument("--task", action="append", help="run only the named task (repeatable)")
    args = parser.parse_args()
    try:
        index, count = (int(part) for part in args.shard.split("/"))
    except ValueError:
        parser.error("--shard must be I/N with 0 <= I < N")
    if not 0 <= index < count:
        parser.error("--shard must be I/N with 0 <= I < N")
    if args.jobs == "auto":
        jobs = auto_jobs()
    elif args.jobs.isdigit() and int(args.jobs) > 0:
        jobs = int(args.jobs)
    else:
        parser.error("--jobs must be a positive integer or 'auto'")
    selected = shard_of(tasks(args.update_golden), index, count)
    if args.task:
        unknown = set(args.task) - {name for name, _, _ in tasks(args.update_golden)}
        if unknown:
            parser.error(f"unknown task: {', '.join(sorted(unknown))}")
        selected = [item for item in selected if item[0] in args.task]
        if not selected:
            parser.error("--task names no task in this shard; check --list for the right shard")
    if args.list:
        for name, _, _ in selected:
            print(name)
        return
    print(f"import mutation shard {args.shard}: {len(selected)} tasks, {jobs} parallel", flush=True)
    setup()
    failures = []

    def timed(name, run):
        # Durations feed the shard weights in `tasks()`. A failed task runs once
        # more in a fresh snapshot: a surviving mutant fails both attempts, while
        # a campaign that overran a time budget on a loaded host gets a retry.
        start = time.monotonic()
        try:
            try:
                run()
            except (Exception, SystemExit) as error:
                print(f"RETRY {name} after failure: {error}", file=sys.stderr, flush=True)
                run()
        finally:
            print(f"task {name}: {time.monotonic() - start:.0f}s", flush=True)

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(timed, name, run): name for name, _, run in selected}
        for future in as_completed(futures):
            try:
                future.result()
            except KeyboardInterrupt:
                raise
            except (Exception, SystemExit) as error:
                failures.append(futures[future])
                print(f"FAIL {futures[future]}: {error}", file=sys.stderr, flush=True)
    if failures:
        raise SystemExit(f"import mutation shard {args.shard} failed: {', '.join(sorted(failures))}")
    print(f"import mutations passed (shard {args.shard}, {len(selected)} tasks)")


if __name__ == "__main__":
    main()
