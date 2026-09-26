#!/usr/bin/env python3
"""Mutation checks for the Solidity importer.

Each case copies the smoke project, changes one thing, and elaborates
`solidity_import`. A reached helper, a return-order change, and a layout
change must make the witness check fail. An unreached `for` stays importable.
Reaching that `for` must be rejected with a source position, and the failed
process must not leave an olean.
"""

import shutil
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


def uninitialized_local(dest: Path) -> None:
    path = dest / "Slice.sol"
    source = path.read_text()
    old = "uint128 credit = p.credit;"
    assert old in source
    path.write_text(source.replace(old, "uint128 ignored;\n        " + old))


def call_unused_from_loss(dest: Path) -> None:
    text = (dest / "Slice.sol").read_text()
    old = "return marketState[market].lossFactor;"
    assert old in text
    (dest / "Slice.sol").write_text(text.replace(old, "uint256 ignored = L.unused();\n        " + old))


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
    diagnostic = expect_failure("uninitialized-local", write_project("uninitialized-local", uninitialized_local),
                                "local declarations without an initializer")
    if not re.search(r"Slice\.sol:\d+:\d+: VariableDeclarationStatement:", diagnostic):
        raise SystemExit("uninitialized local lacks a Solidity source diagnostic")
    expect_failure("projection-name-collision", write_project("projection-name", projected_name_collision), "projected parameter name collision")
    namespaced = WORK / "base/Namespaced.lean"
    namespaced.write_text(HEADER.format(root=WORK / "base").replace(
        "solidity_import imported", "namespace Nested\nsolidity_import imported") +
        "\nend Nested\nexample : modelImportCovered Nested.imported.model = true := Nested.imported.covered\n")
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
    diagnostic = expect_failure("reachable-for", write_project("reachable", call_unused), "unsupported")
    assert "[solidity-import:unsupported]" in diagnostic and "closure:" in diagnostic
    assert "Lib.sol:" in diagnostic and "closure: C.f -> L.unused" in diagnostic, diagnostic
    if digest_of(base) == digest_of(rounding):
        raise SystemExit("helper change did not move the digest")
    print("pass helper-digest")
    # Compile and execute actual Denote mutants: a build failure is invalid,
    # not a detected semantic mutation. These regressions compare EVM bytes.
    for mutant in ("denote-panic-selector", "denote-panic-endian",
                   "import-msg-sender", "import-address-this",
                   "import-block-number", "import-block-chainid",
                   "import-require-condition", "denote-require-selector",
                   "import-custom-require-condition", "denote-custom-require-selector",
                   "denote-custom-require-argument",
                   "import-scalar-read", "import-scalar-slot", "import-scalar-offset",
                   "import-scalar-write", "import-scalar-delete", "import-void-fallthrough",
                   "denote-scalar-sibling-mask"):
        output = Path(tempfile.mkdtemp(prefix=f"{mutant}-", dir=WORK))
        subprocess.run(["sh", str(ROOT / "scripts/check_solidity_differential.sh"),
                        "--mutations", "--mutant", mutant, "--output", str(output)],
                       cwd=ROOT, check=True, timeout=900)
        results = json.loads((output / "mutation-results.json").read_text())
        if len(results) != 1 or results[0]["mutant"] != mutant or results[0]["status"] != "detected":
            raise SystemExit(f"{mutant}: expected a runtime differential divergence")
        print(f"pass {mutant}")
    subprocess.run([sys.executable, str(ROOT / "scripts/solidity_differential/check_environment_rejections.py")],
                   cwd=ROOT, check=True, timeout=300)
    subprocess.run([sys.executable, str(ROOT / "scripts/solidity_differential/check_storage_rejections.py")],
                   cwd=ROOT, check=True, timeout=300)
    print("import mutations passed")


if __name__ == "__main__":
    main()
