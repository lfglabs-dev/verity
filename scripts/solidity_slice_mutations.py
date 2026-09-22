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


def expect_success(name: str, project: Path, witness: bool) -> str:
    lean_path = project / "Check.lean"
    text = HEADER.format(root=project)
    if witness:
        text += WITNESS
    lean_path.write_text(text)
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
    rounding = expect_failure("rounding-detected", write_project("rounding", change_rounding), "witness changed")
    expect_failure("factor-detected", write_project("factor", change_factor), "witness changed")
    expect_failure("field-detected", write_project("field", change_field), "witness changed")
    expect_failure("return-order", write_project("returns", swap_returns), "witness changed")
    expect_failure("layout", write_project("layout", swap_layout), "witness changed")
    expect_failure("reachable-for", write_project("reachable", call_unused), "unsupported")
    if digest_of(base) == digest_of(rounding):
        raise SystemExit("helper change did not move the digest")
    print("pass helper-digest")
    print("slice mutations passed")


if __name__ == "__main__":
    main()
