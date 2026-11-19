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


def check_constant_expressions(output, config_path):
    """Check widened casts and source-located rejections through constant references."""
    config = json.loads(config_path.read_text())
    fixture = config_path.parent
    directory = output / ("constants-" + config["contract"])
    directory.mkdir()
    config.update(project=str(fixture), function="widenedLiterals", param_types=[], arguments={},
                  variables={"time": 8}, timestamp="time")
    config.pop("corpus")
    request = directory / "config.json"
    write_json(request, config)
    result = campaign(request, directory, 1, 7600)
    model, = json.loads((directory / "model-results.json").read_text())
    if result["divergences"] or result["successes"] != 1 or model["words"] != ["0", "255", "42"]:
        raise HarnessError(f"{config['contract']}: wrong widened integer constant")

    def driver(roots, survey=False):
        options = ', collectUnsupported := true' if survey else ''
        return ('import Compiler.SolidityImport.Import\n'
                f'solidity_import tested from "Contracts/SolidityImportSmoke" entry "{config["entry"]}"\n'
                '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
                f'viaIR := false, optimizerRuns := none, bytecodeHash := "ipfs"{options} }}\n'
                f'  contract {config["contract"]}\n'
                + ''.join(f'  function {root}()\n' for root in roots))

    locations = []
    roots = {"localConstant": "LegacyArithmetic.sol",
             "qualifiedConstant": "LegacyConstantInitializers.sol",
             "indirectConstant": "LegacyConstantInitializers.sol"}
    for root, filename in roots.items():
        before, _ = (fixture / filename).read_text().split("uint256(10) /")
        line = before.count("\n") + 1
        column = len(before.rsplit("\n", 1)[-1]) + 1
        locations.append(f'("{root}", false, [("{filename}", {line}, {column}, "BinaryOperation")])')
        path = directory / (root + ".lean")
        path.write_text(driver([root]))
        proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                              text=True, capture_output=True, timeout=180)
        log = proc.stdout + proc.stderr
        at = f"{filename}:{line}:{column}: BinaryOperation: [solidity-import:unsupported]"
        if not proc.returncode or at not in log or "legacy exceptional halt is not modeled" not in log:
            raise HarnessError(f"{root}: missing rejection at the initializer: {log}")

    path = directory / "Survey.lean"
    locations.append('("widenedLiterals", true, [])')
    path.write_text(driver([*roots, "widenedLiterals"], survey=True)
        + '#guard tested.report.functions.map (fun f => (f.function, f.denoteCovered,\n'
        + '  f.unsupported.map (fun u => (u.file, u.line, u.column, u.kind)))) ==\n'
        + '  [' + ',\n   '.join(locations) + ']\n')
    proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                          text=True, capture_output=True, timeout=180)
    if proc.returncode:
        raise HarnessError(f"wrong constant initializer survey: {proc.stdout}{proc.stderr}")


def check_mapping_getter(output, config_path, strict):
    """A generated getter must decode its key before reading the mapping slot."""
    directory = output / ("getter-v2" if strict else "getter-v1")
    source = directory / "fixture"
    source.mkdir(parents=True)
    pragma = "pragma experimental ABIEncoderV2;\n" if strict else ""
    (source / "Getter.sol").write_text("// SPDX-License-Identifier: MIT\npragma solidity 0.7.6;\n"
        + pragma + "contract Getter { mapping(address => uint256) public items; }\n")
    profile = json.loads(config_path.read_text())
    write_json(directory / "config.json", {
        "project": str(source), "entry": "Getter.sol", "contract": "Getter", "function": "items",
        "param_types": ["address"], "variables": {"key": 160},
        "solc": profile["solc"], "settings": profile["settings"],
    })
    prepare(directory / "config.json", directory)
    canonical_key = 17
    slot = int.from_bytes(keccak(canonical_key.to_bytes(32, "big") + bytes(32)), "big")
    selector = keccak(b"items(address)")[:4]
    cases, expected = [], []
    for name, words in (("canonical", [canonical_key]), ("dirty", [2**160 + canonical_key]),
                        ("short", [])):
        payload = b"".join(word.to_bytes(32, "big") for word in words)
        cases.append({"id": name, "args": list(map(str, words)), "timestamp": "0",
                      "storage": [[str(slot), "37"]], "observe": [], "storageCount": 1,
                      "observeCount": 0, "sourceCalldata": "0x" + (selector + payload).hex(),
                      "compiledCalldata": "0x12345678" + payload.hex()})
        returns_value = name == "canonical" or (name == "dirty" and not strict)
        expected.append(("ok", "0x" + (37).to_bytes(32, "big").hex()) if returns_value
                        else ("revert", "0x"))
    manifest = json.loads((directory / "manifest.json").read_text())
    manifest["casesSha256"] = hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest()
    write_json(directory / "manifest.json", manifest)
    result = execute(directory, cases)
    original = parse_evm(directory / "out/source.txt", cases)
    if result["divergences"] or [(row["status"], row["data"]) for row in original] != expected:
        raise HarnessError(f"{directory.name}: mapping getter disagrees with the expected ABI result")


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
    for name in ("abi-v1", "abi-v2-inherits-v1"):
        check_constant_expressions(output, fixture / f"differential-legacy-{name}.json")
    for strict in (False, True):
        check_mapping_getter(output, fixture / "differential-legacy-abi-v1.json", strict)
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
