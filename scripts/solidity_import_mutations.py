#!/usr/bin/env python3
"""Mutation checks for the Solidity importer.

Each case copies the smoke project, changes one thing, and elaborates
`solidity_import`. A reached helper, a return-order change, and a layout
change must make the witness check fail. An unreached `for` stays importable.
Reaching that `for` must be rejected with a source position, and the failed
process must not leave an olean.
"""

import shutil
import os
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOLC = ROOT / ".lake/solidity-import/solc-0.8.34"
WORK = ROOT / ".lake/import-mutations"
SMOKE = ROOT / "Contracts/SolidityImportSmoke"
GOLDEN = SMOKE / "model.golden"

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


def main() -> None:
    if not SOLC.is_file():
        raise SystemExit(f"missing {SOLC}")
    # The checks import the status driver, which `lake build SolidityImportSmoke` does not build.
    subprocess.run(["lake", "build", "Compiler.SolidityImport.Differential"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / "scripts/solidity_differential/check_require_rejections.py")],
                   cwd=ROOT, check=True)
    WORK.mkdir(parents=True, exist_ok=True)
    snapshot = WORK / "model.txt"
    snapshot.unlink(missing_ok=True)
    base = expect_success("unreached-for", write_project("base", unchanged), witness=True,
                          extra=f'\n#eval IO.FS.writeFile "{snapshot}" (toString (repr imported.model) ++ "\\n")\n')
    # Refactors of the importer must reproduce the imported model exactly.
    if "--update-golden" in sys.argv:
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
    for mutant in ("denote-panic-selector", "denote-panic-endian",
                   "denote-calldata-load-selector-data", "denote-calldata-copy-drop",
                   "import-msg-sender", "import-address-this",
                   "import-block-number", "import-block-chainid",
                   "import-require-condition", "denote-require-selector",
                   "import-custom-require-condition", "denote-custom-require-selector",
                   "denote-custom-require-argument",
                   "import-scalar-read", "import-scalar-slot", "import-scalar-offset",
                   "import-scalar-write", "import-scalar-delete", "import-void-fallthrough",
                   "denote-scalar-sibling-mask",
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
                   'import-market-root-offset',
                   'import-market-root-size',
                   'import-market-calldata-array-size',
                   'import-market-memory-panic',
                   'import-market-struct-source-stride',
                   'import-market-struct-pointer-stride',
                   'import-market-struct-validation',
                   'import-market-calldata-element-stride',
                   'import-market-memory-element-stride',
                   'import-market-member-validation',
                   'import-market-root-scalar-validation',
                   'import-market-memory-scalar-read',
                   'import-market-calldata-scalar-read',
                   'import-market-calldata-root-validation',
                   'import-market-calldata-index-bounds',
                   'import-dynamic-root-parameter-offset'):
        output = Path(tempfile.mkdtemp(prefix=f"{mutant}-", dir=WORK))
        subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"),
                        "--mutations", "--mutant", mutant, "--output", str(output)],
                       cwd=ROOT, check=True, timeout=900)
        results = json.loads((output / "mutation-results.json").read_text())
        if len(results) != 1 or results[0]["mutant"] != mutant or results[0]["status"] != "detected":
            raise SystemExit(f"{mutant}: expected a runtime differential divergence")
        print(f"pass {mutant}")
    # Removing an order guard must change a located rejection to admission.
    for mutant in ('import-helper-effect-binary-guard', 'import-helper-effect-argument-guard', 'import-helper-effect-classifier', 'import-yul-result-id-guard', 'import-solc-viair-guard', 'import-solc-uncollected-source-guard'):
        output = Path(tempfile.mkdtemp(prefix=f"{mutant}-", dir=WORK))
        subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"),
                        "--mutations", "--mutant", mutant, "--output", str(output)],
                       cwd=ROOT, check=True, timeout=900)
        results = json.loads((output / "mutation-results.json").read_text())
        if (len(results) != 1 or results[0]['mutant'] != mutant
                or not results[0]['detected'] or not results[0]['baselinePassed']
                or results[0]['kind'] != 'unsupported-order-admission'):
            raise SystemExit(f'{mutant}: exact negative control guard mutation escaped detection')
        print(f'pass {mutant} exact rejection guard')
    # Quotation corruption is rejected before an executable model exists.
    quote_output = Path(tempfile.mkdtemp(prefix="modulo-quote-integrity-", dir=WORK))
    subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"),
                    "--mutations", "--mutant", "import-modulo-quote", "--output", str(quote_output)],
                   cwd=ROOT, check=True, timeout=900)
    quote_results = json.loads((quote_output / "mutation-results.json").read_text())
    if (len(quote_results) != 1 or quote_results[0]["mutant"] != "import-modulo-quote"
            or not quote_results[0]["baselinePassed"]
            or quote_results[0]["kind"] != "model-integrity-rejection"
            or quote_results[0]["diagnostic"] != "internal: the elaborated model differs from the imported value"):
        raise SystemExit("modulo quotation corruption escaped the exact integrity check")
    print("pass import-modulo-quote integrity rejection")
    subprocess.run([sys.executable, str(ROOT / "scripts/solidity_differential/check_environment_rejections.py")],
                   cwd=ROOT, check=True, timeout=300)
    subprocess.run([sys.executable, str(ROOT / "scripts/solidity_differential/check_storage_rejections.py")],
                   cwd=ROOT, check=True, timeout=300)
    output = Path(tempfile.mkdtemp(prefix="scalar-array-rejections-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_scalar_array_abi_rejections",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=300)
    output = Path(tempfile.mkdtemp(prefix="market-rejections-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_market_abi_rejections",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=300)
    output = Path(tempfile.mkdtemp(prefix="block-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_block_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    block_result = json.loads((output / "complete.json").read_text())
    if (block_result["mutant"] != "import-block-drop" or not block_result["detected"]
            or not block_result["baselinePassed"] or not block_result["witness"]["deletion_minimal"]):
        raise SystemExit("block mutation requires detected minimal runtime witness")
    print("pass import-block-drop")
    output = Path(tempfile.mkdtemp(prefix="reference-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_reference_argument_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    reference = json.loads((output / "complete.json").read_text())
    if (reference["mutant"] != "import-reference-wrong-root" or not reference["detected"]
            or not reference["baselinePassed"] or not reference["witness"]["deletion_minimal"]):
        raise SystemExit("reference mutation requires detected minimal runtime witness")
    print("pass import-reference-wrong-root")
    for module, label in [
        ("check_reference_boundary_mutations", "reference-boundary"),
        ("check_reference_location_mutation", "reference-location"),
    ]:
        output = Path(tempfile.mkdtemp(prefix=label + "-", dir=WORK)) / "cases"
        launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                    f'runpy.run_module("solidity_differential.{module}",run_name="__main__")')
        subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                       cwd=ROOT, check=True, timeout=2400)
        result = json.loads((output / "complete.json").read_text())
        if label == "reference-boundary":
            controls = result["results"]
            if result["exit"] != 0 or {c["mutant"] for c in controls} != {"external-library", "yul-shadow"}:
                raise SystemExit("reference boundary mutation coverage incomplete")
            if not all(c["detected"] and c["baselinePassed"] and c["unsupportedInputImported"] for c in controls):
                raise SystemExit("reference boundary mutants require actual unsupported admission")
        elif (result["mutant"] != "import-reference-location-guard" or not result["detected"]
              or not result["baselinePassed"] or not result["unsupportedCopyImported"]):
            raise SystemExit("reference location mutant requires actual unsupported copy admission")
        print("pass " + label)
    output = Path(tempfile.mkdtemp(prefix="hashing-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_hashing_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=7200)
    hashing = json.loads((output / "complete.json").read_text())
    expected_hashing_mutants = {
        "hash-word-stride", "hash-root-offset", "hash-root-field", "hash-static-root-field",
        "hash-array-length", "hash-array-destination-stride", "hash-literal-value",
        "hash-literal-length", "hash-packed-address-width", "hash-packed-scalar-value",
        "hash-copy-byte-shift", "hash-copy-zero-fill", "hash-buffer-identity",
        "hash-keccak-length", "hash-hex-number"}
    if hashing["exit"] != 0 or {r["mutant"] for r in hashing["results"]} != expected_hashing_mutants:
        raise SystemExit("hashing mutation coverage incomplete")
    if not all(r["detected"] and r["baselinePassed"] and r["witness"]["deletion_minimal"]
               and r["witness"]["transactions"] for r in hashing["results"]):
        raise SystemExit("hashing mutants require minimal reproduced runtime witnesses")
    print("pass ABI hashing mutations")
    output = Path(tempfile.mkdtemp(prefix="call-refusal-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_call_refusal_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    checked_calls = json.loads((output / "complete.json").read_text())
    expected_checked_call_mutants = {
        "list-refusal-becomes-revert", "function-refusal-becomes-revert",
        "exception-accepts-nonzero-gas", "transaction-refusal-retains-prefix",
        "transaction-refusal-becomes-call-failure"}
    if (checked_calls["exit"] != 0
            or {row["name"] for row in checked_calls["mutants"]} != expected_checked_call_mutants
            or not all(row["replayed"] and row["expected"] != row["actual"]
                       for row in checked_calls["mutants"])):
        raise SystemExit("checked-call mutants require exact independently replayed runtime divergences")
    print("pass checked-call refusal mutations")
    output = Path(tempfile.mkdtemp(prefix="ir-creation-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_ir_creation_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    ir_creation = json.loads((output / "complete.json").read_text())
    expected_ir_creation_mutants = {
        "ir-create2-arguments-left-first", "ir-create2-drops-computed-state",
        "ir-create2-reuses-context", "ir-create2-exception-becomes-value",
        "ir-create2-scope-leaks-locals", "ir-create2-list-drops-post-state",
        "ir-mstore-drops-value", "ir-mstore8-wrong-offset",
        "ir-mstore8-wrong-low-byte", "ir-mstore8-offset-not-normalized",
        "ir-mstore8-modulo128", "ir-mstore8-divides-value"}
    if (ir_creation["exit"] != 0
            or {row["name"] for row in ir_creation["mutants"]} != expected_ir_creation_mutants
            or not all(row["replayed"] and row["expected"] != row["actual"]
                       for row in ir_creation["mutants"])):
        raise SystemExit("IR creation mutants require exact independently replayed semantic divergences")
    print("pass effectful IR creation mutations")
    output = Path(tempfile.mkdtemp(prefix="source-typed-evaluation-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_typed_evaluation_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    typed_evaluation = json.loads((output / "success.json").read_text())
    expected_typed_evaluation = {
        "typed-expression-add-discards-left-state", "typed-statement-consumer-refusal-as-revert",
        "typed-loop-discards-refusal", "typed-unsupported-statement-as-stop",
        "typed-return-values-reversed", "typed-immutable-value-discarded",
        "typed-calldata-source-offset-shifted", "typed-returndata-source-offset-shifted",
        "typed-returndata-exception-keeps-gas", "typed-emit-drops-event", "typed-assigned-helper-reverses-values",
        "typed-assigned-helper-drops-caller-locals",
        "typed-internal-return-writes-external-memory", "typed-discarded-helper-leaks-return-marker",
        "typed-expression-halt-as-revert", "typed-discarded-stop-as-continue",
        "typed-consumer-erases-revert-bytes", "typed-discarded-helper-erases-revert-bytes",
        "typed-assigned-helper-erases-revert-bytes", "typed-custom-error-erases-revert-bytes",
        "typed-panic-corrupts-code", "typed-require-error-evaluates-success-arguments",
        "typed-external-bind-discards-argument-state", "typed-try-external-discards-argument-state",
        "typed-ecm-discards-argument-state"}
    if (typed_evaluation["exit"] != 0 or not typed_evaluation["sources_unchanged"]
            or {row["name"] for row in typed_evaluation["mutants"]} != expected_typed_evaluation
            or not all(row["baseline"] != row["actual"] and row["replay"] == row["actual"]
                       for row in typed_evaluation["mutants"])):
        raise SystemExit("recursive typed mutants require exact independently replayed divergences")
    output = Path(tempfile.mkdtemp(prefix="ir-revert-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_ir_revert_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    ir_revert = json.loads((output / "success.json").read_text())
    if (ir_revert["exit"] != 0 or not ir_revert["sources_unchanged"]
            or {row["name"] for row in ir_revert["mutants"]} != {
                "ir-revert-capture-offset-shifted", "ir-revert-capture-size-increased",
                "ir-revert-byte-offset-shifted", "ir-revert-unobserved-as-empty"}
            or not all(row["expected"] != row["actual"] and row["replay"] == row["actual"]
                       for row in ir_revert["mutants"])):
        raise SystemExit("IR revert mutations require exact independently replayed divergences")
    output = Path(tempfile.mkdtemp(prefix="ir-revert-boundary-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_ir_revert_boundary_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    ir_boundary = json.loads((output / "success.json").read_text())
    if (ir_boundary["exit"] != 0 or not ir_boundary["sources_unchanged"]
            or {row["name"] for row in ir_boundary["mutants"]} != {
                "ir-revert-opcode-erases-capture", "ir-revert-opcode-ignores-offset",
                "public-ir-erases-revert-bytes"}
            or not all(row["expected"] != row["actual"] and row["replay"] == row["actual"]
                       for row in ir_boundary["mutants"])):
        raise SystemExit("IR opcode/public result mutations require exact independently replayed divergences")
    output = Path(tempfile.mkdtemp(prefix="public-revert-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_public_revert_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    public_revert = json.loads((output / "success.json").read_text())
    if (public_revert["exit"] != 0 or not public_revert["sources_unchanged"]
            or {row["name"] for row in public_revert["mutants"]} != {"public-denote-erases-revert-bytes"}
            or not all(row["expected"] != row["actual"] and row["replay"] == row["actual"]
                       for row in public_revert["mutants"])):
        raise SystemExit("public revert byte mutation requires exact independently replayed divergence")
    output = Path(tempfile.mkdtemp(prefix="source-expression-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_expression_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    expression = json.loads((output / "success.json").read_text())
    expected_expression_mutants = {
        "expression-bind-refusal-as-revert", "expression-helper-refusal-as-revert",
        "expression-helper-exception-as-revert", "expression-helper-discards-world",
        "expression-helper-leaks-locals", "expression-list-discards-argument-state",
        "expression-assignment-refusal-as-revert", "expression-helper-leaks-return-marker",
        "expression-helper-stop-as-refusal", "expression-bind-halt-as-revert",
        "expression-bind-erases-revert-bytes", "expression-helper-erases-revert-bytes",
        "expression-assignment-erases-revert-bytes"}
    if (expression["exit"] != 0 or not expression["sources_unchanged"]
            or {row["name"] for row in expression["mutants"]} != expected_expression_mutants
            or not all(row["expected"] != row["actual"] and row["replay"] == row["actual"]
                       for row in expression["mutants"])):
        raise SystemExit("typed expression mutants require exact independently replayed divergences")
    output = Path(tempfile.mkdtemp(prefix="typed-access-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_typed_access_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    typed_access = json.loads((output / "success.json").read_text())
    if ({row["name"] for row in typed_access["rows"]} != {
            "refusal-as-revert", "void-as-revert", "nonzero-gas-accepted", "unknown-function-accepted"}
            or not all(row["baseline"] != row["mutant"] and row["replay"] == row["mutant"]
                       and row["minimal"] for row in typed_access["rows"])):
        raise SystemExit("typed Access mutants require exact independently replayed runtime divergences")
    print("pass typed Access refusal mutations")
    output = Path(tempfile.mkdtemp(prefix="source-helper-refusal-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_helper_refusal_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    source_helpers = json.loads((output / "success.json").read_text())
    if ({row["name"] for row in source_helpers["mutants"]} != {"source-helper-refusal-becomes-revert"}
            or not source_helpers["sources_unchanged"]
            or not all(row["replayed"] and row["expected"] != row["actual"] and row["minimal"]
                       for row in source_helpers["mutants"])):
        raise SystemExit("Source helper refusal mutant requires independently replayed runtime divergence")
    print("pass Source helper refusal mutation")
    output = Path(tempfile.mkdtemp(prefix="native-creation-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_native_creation_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    native_creation = json.loads((output / "success.json").read_text())
    if ({row["name"] for row in native_creation["mutants"]} != {
            "native-context-root-gas", "native-memory-check-removed",
            "native-memory-bytes-unchecked", "native-operands-check-removed"}
            or not native_creation["sources_unchanged"]
            or not all(row["replayed"] and row["expected"] != row["actual"] and row["minimal"]
                       for row in native_creation["mutants"])):
        raise SystemExit("native creation mutants require exact independently replayed runtime divergences")
    print("pass native CREATE2 authentication mutations")
    output = Path(tempfile.mkdtemp(prefix="source-creation-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_creation_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    source_creation = json.loads((output / "success.json").read_text())
    if (source_creation["exit"] != 0 or not source_creation["sources_unchanged"]
            or {row["name"] for row in source_creation["mutants"]} != {"typed-create2-salt-corrupted"}
            or not all(row["baseline"] != row["actual"] and row["actual"] == row["replay"]
                       and len(row["smoke"]) == 1 and row["smoke"][0].startswith("FAIL:")
                       for row in source_creation["mutants"])):
        raise SystemExit("typed Source creation mutation requires exact independently replayed divergence")

    account_output = Path(tempfile.mkdtemp(prefix="account-inputs-", dir=WORK))
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_account_inputs",run_name="__main__")')
    reference = account_output / "reference"
    subprocess.run([sys.executable, "-c", launcher, "--output", str(reference)],
                   cwd=ROOT, check=True, timeout=600)
    inputs = json.loads((reference / "success.json").read_text())
    if (inputs["leanCases"] != 27 or len(inputs["mutations"]) != 6
            or not all(row["semanticDetections"] == 2 for row in inputs["mutations"])):
        raise SystemExit("account input Python mutants require actual semantic detection and replay")
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_account_input_mutations",run_name="__main__")')
    mutations = account_output / "mutations"
    subprocess.run([sys.executable, "-c", launcher, "--output", str(mutations),
                    "--reference", str(reference)], cwd=ROOT, check=True, timeout=1800)
    accounts = json.loads((mutations / "success.json").read_text())
    if (not accounts["sourcesUnchanged"] or {row["name"] for row in accounts["mutants"]} != {
            "erase-external-nonce", "erase-external-code", "erase-external-balance", "wrong-code-size",
            "allow-reserved", "allow-nonce-overflow", "erase-self-balance", "accept-wrong-target",
            "accept-sender-collision"}
            or not all(row["detected"] == row["replay"] for row in accounts["mutants"])):
        raise SystemExit("account input Lean mutants require independently replayed semantic failures")
    print("pass exact initial-account/caller input semantic mutations")

    print("import mutations passed")

    output = Path(tempfile.mkdtemp(prefix="effectful-returndata-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_effectful_returndata_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    effectful_returndata = json.loads((output / "success.json").read_text())
    if (effectful_returndata["exit"] != 0
            or {row["name"] for row in effectful_returndata["rows"]} != {
                "copy-source-shift", "zero-size-edge-rejected", "exception-retains-gas",
                "source-normalization-dropped", "revert-payload-reversed",
                "missing-context-becomes-revert", "terminal-payload-erased"}
            or not all(row["baseline"][-1] == "PASS" and row["detected"][0].startswith("FAIL:")
                       and row["expected"] != row["actual"] and row["replay"] == row["actual"]
                       and row["minimal"] for row in effectful_returndata["rows"])):
        raise SystemExit("effectful returndata mutants require semantic detection and independent replay")
    print("pass effectful returndata mutations")

    output = Path(tempfile.mkdtemp(prefix="canonical-returndata-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_canonical_returndata_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    canonical_returndata = json.loads((output / "success.json").read_text())
    if (canonical_returndata["exit"] != 0
            or {row["name"] for row in canonical_returndata["rows"]} != {
                "ordinary-source-shift", "helper-source-shift", "ordinary-zero-size-edge",
                "ordinary-exception-gas", "helper-exception-gas",
                "ordinary-normalization-dropped", "helper-normalization-dropped",
                "ordinary-missing-context-revert", "helper-missing-context-revert",
                "ordinary-terminal-exception-erased", "helper-callee-capture-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       and row["minimal"] for row in canonical_returndata["rows"])):
        raise SystemExit("canonical returndata mutants require exact semantic detection and independent replay")
    print("pass canonical returndata mutations")


    output = Path(tempfile.mkdtemp(prefix="source-public-exception-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_public_exception_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    public_exceptions = json.loads((output / "success.json").read_text())
    if (public_exceptions["exit"] != 0
            or {row["name"] for row in public_exceptions["rows"]} != {
                "source-public-exception-context-erased",
                "source-public-exception-nonzero-gas-accepted",
                "source-public-exception-missing-context-revert",
                "source-public-exception-rollback-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in public_exceptions["rows"])):
        raise SystemExit("Source public exception mutants require semantic detection and independent replay")
    print("pass Source public exception mutations")

    output = Path(tempfile.mkdtemp(prefix="denote-public-exception-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_denote_public_exception_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    public_exceptions = json.loads((output / "success.json").read_text())
    if (public_exceptions["exit"] != 0
            or {row["name"] for row in public_exceptions["rows"]} != {
                "denote-public-exception-source-projection-erased",
                "denote-public-exception-context-erased",
                "denote-public-exception-nonzero-gas-accepted",
                "denote-public-exception-missing-context-revert",
                "denote-public-exception-rollback-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in public_exceptions["rows"])):
        raise SystemExit("Denote public exception mutants require semantic detection and independent replay")
    print("pass Denote public exception mutations")

    output = Path(tempfile.mkdtemp(prefix="native-world-view-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_native_world_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    native_world = json.loads((output / "success.json").read_text())
    if (native_world["exit"] != 0 or len(native_world["rows"]) != 7
            or {row["name"] for row in native_world["rows"]} != {
                "erase-logs", "erase-presence", "erase-nonce", "erase-balance",
                "conflate-transient", "conflate-original", "conflate-slot-warmth"}
            or not all(len(row["detected"]) == 1
                       and row["detected"][0].startswith("NATIVE_WORLD_FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in native_world["rows"])):
        raise SystemExit("Native world view mutants require semantic detection and independent replay")
    print("pass native world view mutations")

    output = Path(tempfile.mkdtemp(prefix="native-caller-world-gates-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_native_caller_world_gate_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    caller_gates = json.loads((output / "success.json").read_text())
    if (caller_gates["exit"] != 0 or len(caller_gates["rows"]) != 2
            or {row["name"] for row in caller_gates["rows"]} != {
                "static-write-bypass", "sstore-stipend-off-by-one"}
            or not all(len(row["detected"]) == 1
                       and row["detected"][0].startswith("NATIVE_GATE_FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in caller_gates["rows"])):
        raise SystemExit("Native caller gates require semantic detection and independent replay")
    print("pass native caller world gate mutations")

    output = Path(tempfile.mkdtemp(prefix="native-paired-caller-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_native_paired_caller_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    paired = json.loads((output / "success.json").read_text())
    if (paired["exit"] != 0 or len(paired["rows"]) != 5
            or {row["name"] for row in paired["rows"]} != {
                "erase-persistent-update", "conflate-transient-channel", "bypass-account-presence",
                "erase-advance-world", "erase-run-world"}
            or not all(len(row["detected"]) == 1
                       and row["detected"][0].startswith("PAIRED_FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in paired["rows"])):
        raise SystemExit("Paired native caller mutants require semantic detection and independent replay")
    print("pass paired native caller mutations")

    output = Path(tempfile.mkdtemp(prefix="native-paired-creation-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_native_paired_creation_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    paired_creation = json.loads((output / "success.json").read_text())
    if (paired_creation["exit"] != 0 or len(paired_creation["rows"]) != 3
            or {row["name"] for row in paired_creation["rows"]} != {
                "stale-boundary-world", "stale-boundary-machine", "erase-exceptional-prefix"}
            or not all(len(row["detected"]) == 1
                       and row["detected"][0].startswith("PAIRED_CREATION_FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in paired_creation["rows"])):
        raise SystemExit("Paired creation delegation mutants require semantic detection and independent replay")
    print("pass paired native creation delegation mutations")

    # The constructor frame laws do not widen admission. Exercise actual native
    # X with arbitrary runtime payload bytes, exact canonical metering, all
    # world channels and an explicit insufficient-interpreter-fuel case.
    subprocess.run(["python3", "scripts/check_native_mapping_helper_capture.py", "--check"],
                   cwd=ROOT, check=True, timeout=300)
    constructor = subprocess.run(
        ["lake", "env",
         str(Path(os.environ["LEAN_SYSROOT"]) / "bin/lean")
         if os.environ.get("LAKE_OVERRIDE_LEAN") == "true" and os.environ.get("LEAN_SYSROOT")
         else "lean",
         "--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so",
         "--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so",
         "--run", "Contracts/SolidityImportSmoke/NativeInitcodeFrameChecks.lean"],
        cwd=ROOT, capture_output=True, text=True, check=True, timeout=180)
    if (constructor.stdout.splitlines() != [
            "native constructor frames:6 payloads,24 successful runs,6 underfuel rejections,24 gas boundaries",
            "native constructor xi:6 payloads,18 successful runs,6 underfuel rejections",
            "native constructor lambda:6 payloads,18 successful runs,6 underfuel rejections"]
            or constructor.stderr):
        raise SystemExit("Native constructor frame checks require exact output and clean stderr: "
                         + constructor.stdout + constructor.stderr)
    boundary_args = list(constructor.args)
    boundary_args[-1] = "Contracts/SolidityImportSmoke/NativeConstructorBoundaryChecks.lean"
    boundaries = subprocess.run(boundary_args, cwd=ROOT, capture_output=True,
                                text=True, check=True, timeout=180)
    if (boundaries.stdout != "native constructor lambda boundaries:6 payloads,216 runs,gas/deposit/runtime/collision\n"
            or boundaries.stderr):
        raise SystemExit("Native constructor boundary checks require exact output and clean stderr: "
                         + boundaries.stdout + boundaries.stderr)
    step_args = list(constructor.args)
    step_args[-1] = "Contracts/SolidityImportSmoke/NativeCreate2FuelChecks.lean"
    step_checks = subprocess.run(step_args, cwd=ROOT, capture_output=True,
                                 text=True, check=True, timeout=180)
    if (step_checks.stdout != "native create2 fuel:6 payloads,216 runs,gas/nonce/deposit/runtime/collision\n"
            or step_checks.stderr):
        raise SystemExit("Native CREATE2 fuel checks require exact output and clean stderr: "
                         + step_checks.stdout + step_checks.stderr)
    address_args = list(constructor.args)
    address_args[-1] = "Contracts/SolidityImportSmoke/NativeCreate2AddressChecks.lean"
    address_checks = subprocess.run(address_args, cwd=ROOT, capture_output=True,
                                   text=True, check=True, timeout=180)
    if (address_checks.stdout != "SOURCE_CALLER_SUCCESS:6 actual pinned IdLib/Market ABI cases\n"
            "HASHED_DENOTE_SUCCESS: 16 storage/creation/native-iterator comparisons; 37 refusals\n"
            "HASHED_CREATION_SUCCESS: 16 storage/creation/native-iterator comparisons; 5 refusals\n"
            "BOUNDARY_SUCCESS: executions=64; checkedBoundaries=1056\n"
            "native create2 address:54 cases,two hashes,exact preimage,full address,raw-initcode sentinel\n"
            or address_checks.stderr):
        raise SystemExit("Native CREATE2 address checks require exact output and clean stderr: "
                         + address_checks.stdout + address_checks.stderr)
    refusal_args = list(constructor.args)
    refusal_args[-1] = "Contracts/SolidityImportSmoke/NativeMidnightRefusalChecks.lean"
    refusal_checks = subprocess.run(refusal_args, cwd=ROOT, capture_output=True,
                                    text=True, check=True, timeout=180)
    if (refusal_checks.stdout != "SOURCE_COLLISION_SUCCESS:12 actual pinned IdLib collision/revert cases\n"
            "SOURCE_INVALID_SUCCESS:24 malformed ABI native rejections\n" or refusal_checks.stderr):
        raise SystemExit("Native source refusal checks require exact output and clean stderr: "
                         + refusal_checks.stdout + refusal_checks.stderr)
    rollback_args = list(constructor.args)
    rollback_args[-1] = "Contracts/SolidityImportSmoke/NativeMidnightRollbackRunner.lean"
    rollback_checks = subprocess.run(rollback_args, cwd=ROOT, capture_output=True,
                                     text=True, check=True, timeout=180)
    if (rollback_checks.stdout != "SOURCE_ROLLBACK_SUCCESS:6 actual pinned IdLib successful-creation then event/revert cases\n"
            or rollback_checks.stderr):
        raise SystemExit("Native source rollback checks require exact output and clean stderr: "
                         + rollback_checks.stdout + rollback_checks.stderr)
    print("pass native constructor frame checks")
    subprocess.run([sys.executable, "scripts/check_native_midnight_source_capture.py", "--check"],
                   cwd=ROOT, check=True, timeout=180)
    output = Path(tempfile.mkdtemp(prefix="native-midnight-source-", dir=WORK)) / "cases"
    subprocess.run([sys.executable, "scripts/solidity_differential/check_native_midnight_source_mutations.py",
                    "--output", str(output)], cwd=ROOT, check=True, timeout=1800)
    captured = json.loads((output / "success.json").read_text())
    if (captured["exit"] != 0 or len(captured["rows"]) != 3 or
            {row["name"] for row in captured["rows"]} != {
                "omit-storage-write", "corrupt-initcode-header", "corrupt-abi-root"} or
            not all(len(row["detected"]) == 1 and row["detected"] == row["replay"] and
                    row["detected"][0].startswith("uncaught exception: source caller")
                    for row in captured["rows"])):
        raise SystemExit("Captured Solidity caller mutants require semantic detection and replay")

    output = Path(tempfile.mkdtemp(prefix="native-midnight-refusals-", dir=WORK)) / "cases"
    subprocess.run([sys.executable, "scripts/solidity_differential/check_native_midnight_refusal_mutations.py",
                    "--output", str(output)], cwd=ROOT, check=True, timeout=1800)
    refusals = json.loads((output / "success.json").read_text())
    if (refusals["exit"] != 0 or len(refusals["rows"]) != 3 or
            {row["name"] for row in refusals["rows"]} != {
                "missing-native-collision", "missing-canonical-collision", "valid-abi-in-refusal"} or
            not all(len(row["detected"]) == 1 and row["detected"] == row["replay"]
                    for row in refusals["rows"])):
        raise SystemExit("Source refusal mutants require semantic detection and replay")

    subprocess.run([sys.executable, "scripts/check_native_midnight_rollback_capture.py", "--check"],
                   cwd=ROOT, check=True, timeout=180)
    output = Path(tempfile.mkdtemp(prefix="native-midnight-rollback-", dir=WORK)) / "cases"
    subprocess.run([sys.executable, "scripts/solidity_differential/check_native_midnight_rollback_mutations.py",
                    "--output", str(output)], cwd=ROOT, check=True, timeout=1800)
    rollback = json.loads((output / "success.json").read_text())
    if (rollback["exit"] != 0 or len(rollback["rows"]) != 3 or
            {row["name"] for row in rollback["rows"]} != {
                "omit-storage-write", "corrupt-initcode-header", "corrupt-custom-revert"} or
            not all(len(row["detected"]) == 1 and row["detected"] == row["replay"] and
                    row["detected"][0].startswith("uncaught exception: source ")
                    for row in rollback["rows"])):
        raise SystemExit("Source rollback mutants require semantic detection and replay")

    output = Path(tempfile.mkdtemp(prefix="native-hashed-caller-", dir=WORK)) / "cases"
    subprocess.run([sys.executable, "scripts/solidity_differential/check_native_hashed_caller_mutations.py",
                    "--output", str(output)], cwd=ROOT, check=True, timeout=1800)
    hashed = json.loads((output / "success.json").read_text())
    if (hashed["exit"] != 0 or {row["name"] for row in hashed["rows"]} != {
            "zero-hash", "skip-hash-step", "stale-world"} or len(hashed["rows"]) != 3
            or not all(len(row["detected"]) == 1 and row["detected"] == row["replay"]
                       and row["detected"][0].startswith("uncaught exception: hash prefix")
                       for row in hashed["rows"])):
        raise SystemExit("Hashed caller mutants require actual semantic detection and replay")


    output = Path(tempfile.mkdtemp(prefix="native-hashed-denote-", dir=WORK)) / "cases"
    subprocess.run([sys.executable, "scripts/solidity_differential/check_native_hashed_denote_mutations.py",
                    "--output", str(output)], cwd=ROOT, check=True, timeout=1800)
    hashed = json.loads((output / "success.json").read_text())
    if (hashed["exit"] != 0 or {row["name"] for row in hashed["rows"]} != {
            "stale-world", "stale-context", "erase-bindings"} or len(hashed["rows"]) != 3
            or not all(len(row["detected"]) == 1 and row["detected"] == row["replay"]
                       and row["detected"][0].startswith("uncaught exception: denote")
                       for row in hashed["rows"])):
        raise SystemExit("Hashed Denote mutants require actual semantic detection and replay")


    output = Path(tempfile.mkdtemp(prefix="source-public-context-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_public_context_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    public_contexts = json.loads((output / "success.json").read_text())
    expected_public_contexts = {
        f"source-public-{entry}-{kind}-erased"
        for entry in ("interpretFunction", "interpretConstructor", "interpretContract",
                      "interpretFunctionWithHelpers", "interpretConstructorWithHelpers",
                      "interpretContractWithHelpers")
        for kind in ("context", "cursor", "oracle")}
    if (public_contexts["exit"] != 0 or not public_contexts["sources_unchanged"]
            or {row["name"] for row in public_contexts["rows"]} != expected_public_contexts
            or len(public_contexts["rows"]) != 18
            or not all(len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       and len(row["failed"]) == 1 and row["failed"][0].startswith("FAIL:")
                       for row in public_contexts["rows"])):
        raise SystemExit("all six public entries require context/cursor/oracle semantic detection and replay")
    print("pass Source public context forwarding mutations")


    output = Path(tempfile.mkdtemp(prefix="source-internal-exception-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_internal_exception_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    internal_exceptions = json.loads((output / "success.json").read_text())
    if (internal_exceptions["exit"] != 0
            or len(internal_exceptions["rows"]) != 4
            or {row["name"] for row in internal_exceptions["rows"]} != {
                "source-internal-exception-state-erased",
                "source-internal-exception-became-revert",
                "source-internal-exception-rollback-erased",
                "source-internal-exception-refusal-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in internal_exceptions["rows"])):
        raise SystemExit("Source internal exception mutants require semantic detection and independent replay")
    print("pass Source internal exception mutations")


    output = Path(tempfile.mkdtemp(prefix="source-helper-context-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_helper_context_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=3600)
    helper_contexts = json.loads((output / "success.json").read_text())
    if (helper_contexts["exit"] != 0 or len(helper_contexts["rows"]) != 7
            or {row["name"] for row in helper_contexts["rows"]} != {
                "entry-context-erased", "void-call-context-erased", "assign-call-context-erased",
                "success-result-context-erased", "void-resume-context-erased",
                "assign-resume-context-erased", "exceptional-terminal-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in helper_contexts["rows"])):
        raise SystemExit("Source helper context mutants require semantic detection and independent replay")
    print("pass Source helper context mutations")


    output = Path(tempfile.mkdtemp(prefix="helper-body-context-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_helper_body_context_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    body_contexts = json.loads((output / "success.json").read_text())
    if (body_contexts["exit"] != 0 or len(body_contexts["rows"]) != 5
            or (output / "baseline.log").read_text().splitlines() != [
                "Helper-body actual context, error bytes, exception and refusal checks passed", "PASS"]
            or {row["name"] for row in body_contexts["rows"]} != {
                "source-errors-erased", "source-context-erased", "ir-revert-terminal-erased",
                "ir-exception-erased", "ir-refusal-erased"}
            or not all(len(row["detected"]) == 1 and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in body_contexts["rows"])):
        raise SystemExit("Helper-body context mutants require semantic detection and independent replay")
    print("pass helper-body context mutations")


    output = Path(tempfile.mkdtemp(prefix="source-helper-external-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_source_helper_external_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=3600)
    helper_external = json.loads((output / "success.json").read_text())
    if (helper_external["exit"] != 0 or len(helper_external["rows"]) != 11
            or {row["name"] for row in helper_external["rows"]} != {
                "expression-oracle-erased", "expression-cursor-erased",
                "entry-oracle-erased", "entry-cursor-erased", "void-oracle-erased",
                "assign-oracle-erased", "void-cursor-erased", "assign-cursor-erased",
                "success-cursor-erased", "void-resume-cursor-erased", "assign-resume-cursor-erased"}
            or not all(row["baseline"][-1] == "PASS" and len(row["detected"]) == 1
                       and row["detected"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in helper_external["rows"])):
        raise SystemExit("Source helper receipt mutants require semantic detection and independent replay")
    print("pass Source helper external receipt mutations")


    output = Path(tempfile.mkdtemp(prefix="require-payload-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_require_payload_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    payloads = json.loads((output / "success.json").read_text())
    if (payloads["exit"] != 0 or not payloads["sources_unchanged"] or len(payloads["rows"]) != 7
            or {row["name"] for row in payloads["rows"]} != {
                "payload-extent-rejects-finite", "payload-node-polarity", "payload-deep-gate-polarity",
                "payload-function-rejects-finite", "payload-constructor-rejects-finite",
                "payload-function-base-bypassed", "payload-constructor-base-bypassed"}
            or not all(len(row["failed"]) == 1 and row["failed"][0].startswith("FAIL:")
                       and len(row["expected"]) == len(row["actual"]) == 1
                       and row["expected"] != row["actual"] and row["actual"] == row["replay"]
                       for row in payloads["rows"])):
        raise SystemExit("Payload validators require finite semantic witnesses and independent replay")
    print("pass require payload production validation mutations")


    output = Path(tempfile.mkdtemp(prefix="require-import-guard-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_require_import_guards",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=5400)
    import_guards = json.loads((output / "success.json").read_text())
    if (import_guards["exit"] != 0 or not import_guards["sources_unchanged"]
            or len(import_guards["rows"]) != 2
            or {row["name"] for row in import_guards["rows"]} != {
                "import-require-payload-overreject", "import-revert-payload-overreject"}
            or not all(row["positive"]["exit"] == row["expected"]["exit"] == 0
                       and row["positive"]["artifact"] and row["expected"]["artifact"]
                       and row["actual"]["exit"] != 0 and not row["actual"]["artifact"]
                       and row["replay"]["exit"] != 0 and not row["replay"]["artifact"]
                       and row["located"].startswith("Fixture.sol:4:")
                       for row in import_guards["rows"])):
        raise SystemExit("Importer payload guards require compiled mutants and precise rejection replay")
    print("pass importer require/revert payload guard mutations")


    output = Path(tempfile.mkdtemp(prefix="dispatcher-revert-mutations-", dir=WORK)) / "cases"
    launcher = ('import runpy,sys; sys.path.insert(0,"scripts"); '
                'runpy.run_module("solidity_differential.check_dispatcher_revert_mutations",run_name="__main__")')
    subprocess.run([sys.executable, "-c", launcher, "--output", str(output)],
                   cwd=ROOT, check=True, timeout=1800)
    dispatch = json.loads((output / "success.json").read_text())
    if (dispatch["exit"] != 0 or not dispatch["sources_unchanged"] or len(dispatch["rows"]) != 6
            or {row["name"] for row in dispatch["rows"]} != {
                "dispatch-legacy-nonpayable-bytes-erased", "dispatch-legacy-short-args-bytes-erased",
                "dispatch-legacy-unknown-bytes-erased", "dispatch-helpers-nonpayable-bytes-erased",
                "dispatch-helpers-short-args-bytes-erased", "dispatch-helpers-unknown-bytes-erased"}
            or not all(row["expected"] == ["some []"] and row["actual"] == ["none"]
                       and row["actual"] == row["replay"] for row in dispatch["rows"])):
        raise SystemExit("Dispatcher guards require six compiled mutants and exact kernel observation replay")
    print("pass dispatcher exact empty revert mutations")


if __name__ == "__main__":
    main()
