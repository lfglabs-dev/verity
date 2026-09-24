#!/usr/bin/env python3
"""Mutation checks for the Solidity slice importer.

Each case copies the smoke project, changes one thing, and elaborates
`solidity_slice_import`. A reached helper, a return-order change, and a layout
change must make the witness check fail. An unreached `for` stays importable.
Reaching that `for` must be rejected with a source position, and the failed
process must not leave an olean.
"""

import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOLC = ROOT / ".lake/solidity-import/solc-0.8.34"
WORK = ROOT / ".lake/slice-mutations"
SMOKE = ROOT / "Contracts/SoliditySliceSmoke"

HEADER = """
import Compiler.SoliditySlice.Import
import Compiler.SoliditySlice.Coverage

open Compiler.CompilationModel
open Compiler.CompilationModel.SoliditySlice
open Compiler.CompilationModel.Denote

solidity_slice_import imported
  slice_root "{root}" slice_entry "Slice.sol"
  slice_contract "C" slice_function "f"
  slice_param_tys ["struct Mkt", "bytes32", "address"]
  slice_solc "0.8.34+commit.80d5c536" slice_via_ir true slice_evm "osaka"
  slice_optimizer true slice_runs 466 slice_bytecode_hash "none"
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

def witnessBindings (maturity : Nat) : Env :=
  [("m_maturity", maturity), ("id", 1), ("user", 2)]

def body : List Stmt :=
  match imported.model.functions with
  | fn :: _ => fn.body
  | [] => []

#eval IO.println imported.report.sourceDigest

#eval show IO Unit from do
  let success := denoteScalarBody sliceOracle imported.model.fields
    (witnessWorld 100 10 0 0 0) 50 (witnessBindings 100) body
  unless success == some [95, 5, 5] do
    throw (IO.userError s!"witness changed: {success}")
  let reverted := denoteScalarBody sliceOracle imported.model.fields
    (witnessWorld 1 2 0 0 0) 1 (witnessBindings 1) body
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


def call_unused(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    text = text.replace(
        "uint128 credit = p.credit;",
        "uint256 ignored = L.unused();\n        uint128 credit = p.credit;",
    )
    (dest / "Slice.sol").write_text(text)


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
        "returns (uint128, uint128, uint128)", "returns (uint128 a, uint128 b, uint128 c)").replace(
        "return (uint128(post) - fee, uint128(postFee) - fee, fee);", ""))


def projected_name_collision(dest: Path) -> None:
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
    WORK.mkdir(parents=True, exist_ok=True)
    base = expect_success("unreached-for", write_project("base", unchanged), witness=True)
    expect_success("helper-local-hygiene", write_project("helper-local", helper_local_collision), witness=True)
    expect_success("generated-name-hygiene", write_project("generated-name", generated_name_collision), witness=True)
    expect_success("unrelated-layout", write_project("unrelated-layout", unrelated_layout), witness=True)
    expect_failure("named-arguments", write_project("named-arguments", named_arguments), "named call arguments")
    expect_failure("implicit-return", write_project("implicit-return", implicit_return), "explicit root return")
    expect_failure("projection-name-collision", write_project("projection-name", projected_name_collision), "projected parameter name collision")
    namespaced = WORK / "base/Namespaced.lean"
    namespaced.write_text(HEADER.format(root=WORK / "base").replace(
        "solidity_slice_import imported", "namespace Nested\nsolidity_slice_import imported") +
        "\nend Nested\nexample : modelSliceCovered Nested.imported.model = true := Nested.imported.sliceCovered\n")
    result = lean(namespaced)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    print("pass namespaced-import")
    expect_success("shadowed-block", write_project("shadowed-block", shadow_builtin), witness=False,
                   extra='\n#eval show IO Unit from do\n  unless imported.report.projections.any (fun p => p.member == "timestamp") do\n    throw (IO.userError "shadowed block was treated as a builtin")\n')
    expect_success("narrow-multiply-overflow", write_project("narrow-multiply", narrow_multiply), witness=False,
                   extra=r'''
#eval show IO Unit from do
  let oracle : DenoteOracle := { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }
  let body := match imported.model.functions with | f :: _ => f.body | [] => []
  let run := fun maturity => denoteScalarBody oracle imported.model.fields Verity.defaultState 0 [("m_maturity", maturity)] body
  unless run 3 == some [9, 0, 0] do throw (IO.userError "small uint248 product changed")
  unless run (2^128) == none do throw (IO.userError "uint248 product overflow was accepted")
''')
    repeated = expect_success("deterministic", WORK / "base", witness=True)
    if digest_of(base) != digest_of(repeated):
        raise SystemExit("identical input did not reproduce the digest")
    rounding = expect_failure("rounding-detected", write_project("rounding", change_rounding), "witness changed")
    expect_failure("factor-detected", write_project("factor", change_factor), "witness changed")
    expect_failure("field-detected", write_project("field", change_field), "witness changed")
    expect_failure("return-order", write_project("returns", swap_returns), "witness changed")
    expect_failure("layout", write_project("layout", swap_layout), "witness changed")
    diagnostic = expect_failure("reachable-for", write_project("reachable", call_unused), "unsupported")
    assert "[solidity-slice:unsupported]" in diagnostic and "closure:" in diagnostic
    assert "Lib.sol:" in diagnostic and "closure: C.f -> L.unused" in diagnostic, diagnostic
    if digest_of(base) == digest_of(rounding):
        raise SystemExit("helper change did not move the digest")
    print("pass helper-digest")
    print("slice mutations passed")


if __name__ == "__main__":
    main()
