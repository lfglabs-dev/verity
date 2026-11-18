"""Actual legacy source/model/compiled-model comparisons and ABI dirty words.

Source compilation is Solidity 0.7.6 / Istanbul. The observation machine is
Foundry's Osaka EVM, as in the existing differential harness; gas is excluded.
No rejection or infrastructure failure counts as an agreeing execution.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from .engine import ROOT, HarnessError, campaign, execute, write_json

FIXTURES = ("arithmetic", "helper", "wrapThenCheck", "abi-v1", "abi-v2", "abi-v2-directive",
            "abi-v1-inherits-v2", "abi-v2-inherits-v1")


def rejection_controls(output):
    """Require source-located rejection, never a timeout or elaborator failure."""
    reports = []
    for name, reason in (("division", "legacy exceptional halt is not modeled"),
                         ("helperDivision", "legacy exceptional halt is not modeled"),
                         ("modulo", "legacy exceptional halt is not modeled"),
                         ("assertion", "assert/INVALID is not modeled"),
                         ("mutation", "requires a read-only function"),
                         ("fixedBytesConversion", "admits only unsigned/address conversions")):
        path = output / f"reject-{name}.lean"
        path.write_text('import Compiler.SolidityImport.Import\n'
            'solidity_import rejected from "Contracts/SolidityImportSmoke" entry "LegacyArithmetic.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "ipfs" }\n'
            f'  contract LegacyArithmetic\n  function {name}(uint256, uint256)\n')
        proc = subprocess.run(["lake", "env", "lean", str(path)],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        log = proc.stdout + proc.stderr
        path.with_suffix(".log").write_text(log)
        if proc.returncode == 0 or "[solidity-import:unsupported]" not in log or reason not in log:
            raise HarnessError(f"missing explicit legacy rejection for {name}: {log}")
        reports.append({"function": name, "status": "source-rejected", "reason": reason})
    write_json(output / "rejections.json", reports)
    for name, compiler, evm, via_ir, reason in (
        ("compiler-suffix", "0.7.6", "istanbul", "false", "this importer is pinned to solc"),
        ("via-ir", "0.7.6+commit.7338295f", "istanbul", "true", "viaIR is not supported"),
        ("evm-target", "0.7.6+commit.7338295f", "homestead", "false", "evmVersion homestead is not supported"),
    ):
        path = output / f"reject-profile-{name}.lean"
        path.write_text('import Compiler.SolidityImport.Import\n'
            'solidity_import rejected from "Contracts/SolidityImportSmoke" entry "LegacyArithmetic.sol"\n'
            f'  using {{ solc := "{compiler}", evmVersion := "{evm}", viaIR := {via_ir}, '
            'optimizerRuns := none, bytecodeHash := "ipfs" }\n'
            '  contract LegacyArithmetic\n  function arithmetic(uint256, uint256)\n')
        proc = subprocess.run(["lake", "env", "lean", str(path)],
            cwd=ROOT, text=True, capture_output=True, timeout=180)
        log = proc.stdout + proc.stderr
        path.with_suffix(".log").write_text(log)
        if proc.returncode == 0 or reason not in log:
            raise HarnessError(f"missing explicit legacy profile rejection for {name}: {log}")
        reports.append({"profile": name, "status": "profile-rejected", "reason": reason})
    write_json(output / "rejections.json", reports)


def check_survey(output):
    """Keep supported roots and report the actual call path of a rejected helper."""
    driver = output / "Survey.lean"
    driver.write_text('''import Compiler.SolidityImport.Import
solidity_import surveyed from "Contracts/SolidityImportSmoke" entry "LegacyArithmetic.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := none, bytecodeHash := "ipfs", collectUnsupported := true }
  contract LegacyArithmetic
  function division(uint256, uint256)
  function helperDivision(uint256, uint256)
  function arithmetic(uint256, uint256)
#guard surveyed.report.functions.map (fun f => (f.function, f.denoteCovered)) ==
  [("division", false), ("helperDivision", false), ("arithmetic", true)]
#guard (surveyed.report.functions.flatMap (·.unsupported)).filterMap (fun u =>
  if u.followOn.isEmpty then some (u.kind, u.closure) else none) ==
  [("BinaryOperation", ["LegacyArithmetic.division"]),
   ("BinaryOperation", ["LegacyArithmetic.helperDivision", "LegacyArithmeticHelpers.divide"])]
''')
    proc = subprocess.run(["lake", "env", "lean", str(driver)], cwd=ROOT, text=True,
                          capture_output=True, timeout=180)
    if proc.returncode:
        raise HarnessError(f"legacy survey failed: {proc.stdout}{proc.stderr}")


def run(output, count=32, fixtures=FIXTURES):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = ROOT / "Contracts/SolidityImportSmoke"
    reports = []
    for name in fixtures:
        directory = output / name
        result = campaign(fixture / f"differential-legacy-{name}.json", directory, count, 7600)
        reports.append({"fixture": name, **result})
        if name.startswith("abi-") and not result["divergences"]:
            cases = json.loads((directory / "model-cases.json").read_text())
            template = cases[0]
            for index, word in ((0, 256), (0, 2**256-1), (1, 2), (1, 2**256-1),
                                (2, 2**160), (2, 2**256-1)):
                case = copy.deepcopy(template)
                case["id"] = f"dirty-{index}-{word}"
                case["args"][index] = str(word)
                payload = b"".join(int(value).to_bytes(32, "big") for value in case["args"])
                for key in ("sourceCalldata", "compiledCalldata"):
                    case[key] = case[key][:10] + payload.hex()
                cases.append(case)
            for words in range(3):
                case = copy.deepcopy(template)
                case["id"] = f"truncated-{words}-words"
                case["args"] = case["args"][:words]
                for key in ("sourceCalldata", "compiledCalldata"):
                    case[key] = case[key][:10 + 64 * words]
                cases.append(case)
            manifest_path = directory / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["casesSha256"] = hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest()
            write_json(manifest_path, manifest)
            result = execute(directory, cases)
            reports[-1] = {"fixture": name, **result}
        write_json(output / "results.json", reports)
        print(name, result["cases"], "cases", len(result["divergences"]), "divergences", flush=True)
    rejection_controls(output)
    check_survey(output)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--fixture", choices=FIXTURES, action="append",
                        help="select a fixture for focused iteration; default is all")
    args = parser.parse_args()
    if args.cases < 0:
        parser.error("--cases must be nonnegative")
    try:
        reports = run(args.output, args.cases, args.fixture or FIXTURES)
    except (HarnessError, subprocess.TimeoutExpired, ValueError, KeyError, OSError) as error:
        print(f"HARNESS ERROR: {error}", file=sys.stderr)
        return 2
    return int(any(result["divergences"] for result in reports))


if __name__ == "__main__":
    raise SystemExit(main())
