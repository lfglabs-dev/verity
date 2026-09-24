"""Batch A/B/C execution with explicit infrastructure failures and replay artifacts."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

from .cases import canonical, generate, materialize

ROOT = Path(__file__).resolve().parents[2]
WORKSPACE = Path.cwd().resolve()
SOLC = WORKSPACE / ".lake/solidity-import/solc-0.8.34"


class HarnessError(RuntimeError):
    pass


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2) + "\n")


def command(argv, *, cwd=WORKSPACE, timeout=180, stdin=None, log=None):
    try:
        result = subprocess.run(list(map(str, argv)), cwd=cwd, input=stdin, text=True, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        raise HarnessError(f"resource_limit: {argv[0]} exceeded {timeout}s") from error
    if log:
        Path(log).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise HarnessError(f"tool_failure ({result.returncode}): {' '.join(map(str, argv))}\n{(result.stdout + result.stderr)[-4000:]}")
    return result.stdout


def solc_compile(request, project, out):
    write_json(out.with_suffix(".input.json"), request)
    stdout = command([SOLC, "--base-path", project, "--standard-json"], stdin=json.dumps(request), timeout=180)
    result = json.loads(stdout)
    write_json(out.with_suffix(".output.json"), result)
    errors = [e.get("formattedMessage", e["message"]) for e in result.get("errors", []) if e["severity"] == "error"]
    if errors:
        raise HarnessError("solc_failure: " + "\n".join(errors))
    return result


def implementation_hashes():
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for directory in ("Compiler", "Verity", "scripts/solidity_differential")
            for p in (ROOT / directory).rglob("*") if p.suffix in (".lean", ".py", ".sol", ".txt")}

    for name in ("scripts/solidity_slice_differential.py", "lake-manifest.json", "lean-toolchain"):
        hashes[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    return hashes


def prepare(config_path, output):
    config_path = Path(config_path).resolve()
    config = json.loads(config_path.read_text())
    project = (config_path.parent / config["project"]).resolve()
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "out").mkdir(exist_ok=True)
    if not isinstance(config.get("variables"), dict) or not config["variables"]:
        raise HarnessError("fixture_unsupported: nonempty variable domains required")
    for name, bits in config["variables"].items():
        if not isinstance(bits, int) or not 1 <= bits <= 256:
            raise HarnessError("invalid variable width: " + name)
    settings = config.get("settings", {})
    if set(settings) - {"evmVersion", "viaIR", "optimizer", "metadata"}:
        raise HarnessError("fixture_unsupported: unknown compiler settings")
    profile = {"evmVersion": "osaka", "viaIR": True, "optimizer": {"enabled": True, "runs": 466},
               "metadata": {"bytecodeHash": "none"}, **settings}
    if profile["evmVersion"] != "osaka":
        raise HarnessError("fixture_unsupported: this runner currently targets Osaka")
    command(["lake", "build", "Compiler.SoliditySlice.Import", "Compiler.SoliditySlice.Differential"],
            timeout=1800, log=output / "build.log")
    # Keep the importer and reference compiler profile identical.
    driver = output / "Driver.lean"
    driver.write_text('import Compiler.SoliditySlice.Import\nimport Compiler.SoliditySlice.Differential\n'
        + 'solidity_slice_import tested\n'
        + f'  slice_root {json.dumps(str(project))} slice_entry {json.dumps(config["entry"])}\n'
        + f'  slice_contract {json.dumps(config["contract"])} slice_function {json.dumps(config["function"])}\n'
        + '  slice_param_tys [' + ', '.join(map(json.dumps, config["param_types"])) + ']\n'
        + f'  slice_solc "0.8.34+commit.80d5c536" slice_via_ir {str(profile["viaIR"]).lower()} slice_evm {json.dumps(profile["evmVersion"])}\n'
        + f'  slice_optimizer {str(profile["optimizer"]["enabled"]).lower()} slice_runs {profile["optimizer"]["runs"]} slice_bytecode_hash {json.dumps(profile["metadata"]["bytecodeHash"])}\n'
        + 'def main (args : List String) : IO UInt32 :=\n'
        + '  Compiler.CompilationModel.SoliditySlice.Differential.run tested.model tested.report args\n')
    command(["lake", "env", "lean", "--run", driver, "describe", output / "model.json", output / "model.yul"],
            timeout=300, log=output / "import.log")
    metadata = json.loads((output / "model.json").read_text())
    if not metadata["compilable"]:
        raise HarnessError("compilation_unsupported: " + metadata["compileError"])
    imported_settings = json.loads(metadata["settings"])
    source_request = {"language": "Solidity", "sources": {config["entry"]: {"urls": [config["entry"]]}},
                      "settings": {**imported_settings, "outputSelection": {"*": {"*": ["abi", "storageLayout", "evm.bytecode.object", "evm.deployedBytecode.object"]}}}}
    source_result = solc_compile(source_request, project, output / "source")
    contract = source_result["contracts"][config["entry"]][config["contract"]]
    constructors = [x for x in contract["abi"] if x["type"] == "constructor"]
    if constructors and constructors[0]["inputs"]:
        raise HarnessError("fixture_unsupported: constructor arguments require an explicit deployment fixture")
    matches = [x for x in contract["abi"] if x["type"] == "function" and x["name"] == config["function"]
               and [p.get("internalType", p["type"]).replace(" payable", "") for p in x["inputs"]] == config["param_types"]]
    if len(matches) != 1:
        raise HarnessError("fixture_unsupported: selected function ABI is missing or ambiguous")
    abi = matches[0]
    if any(p["type"] in ("bytes", "string") or "[" in p["type"] or p["type"] == "tuple" for p in abi["outputs"]):
        raise HarnessError("fixture_unsupported: only static scalar returns are compared")
    source_bin = bytes.fromhex(contract["evm"]["bytecode"]["object"])
    (output / "source.bin").write_bytes(source_bin)
    yul_request = {"language": "Yul", "sources": {"Model.yul": {"content": (output / "model.yul").read_text()}},
                   "settings": {"evmVersion": profile["evmVersion"], "optimizer": profile["optimizer"],
                                "outputSelection": {"*": {"*": ["evm.bytecode.object", "evm.deployedBytecode.object"]}}}}
    compiled_result = solc_compile(yul_request, project, output / "compiled")
    compiled_contracts = list(compiled_result["contracts"]["Model.yul"].values())
    if len(compiled_contracts) != 1:
        raise HarnessError("harness: expected one compiled Yul object")
    (output / "compiled.bin").write_bytes(bytes.fromhex(compiled_contracts[0]["evm"]["bytecode"]["object"]))
    shutil.copyfile(Path(__file__).with_name("Runner.t.sol"), output / "Runner.t.sol")
    (output / "foundry.toml").write_text('[profile.default]\nsrc = "empty"\ntest = "."\n'
        + f'solc = {json.dumps(str(SOLC))}\nevm_version = "osaka"\noptimizer = true\nvia_ir = true\n'
        + 'gas_limit = 9223372036854775807\ncode_size_limit = 100000\n'
        + 'fs_permissions = [{ access = "read-write", path = "./" }]\n')
    manifest = {"config": config, "configPath": str(config_path), "model": metadata,
                "verity": command(["git", "rev-parse", "HEAD"], cwd=ROOT).strip(),
                "solcSha256": hashlib.sha256(SOLC.read_bytes()).hexdigest(),
                "forge": command(["forge", "--version"]).strip(),
                "observables": ["success/revert", "return words", "observed storage", "no storage writes", "A/C revert payload"],
                "exclusions": ["Denote revert payload", "gas equivalence", "memory allocation identity", "full ABI equivalence"]}
    # Archive the source closure loaded by solc. Reject paths escaping the project.
    for logical in source_result["sources"]:
        path = (project / logical).resolve()
        if not path.is_relative_to(project):
            raise HarnessError("source outside project: " + logical)
        target = output / "sources" / logical
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    manifest["sourceHashes"] = {str(p.relative_to(output / "sources")): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in (output / "sources").rglob("*.sol")}
    write_json(output / "abi.json", abi)
    write_json(output / "layout.json", contract["storageLayout"])
    manifest["implementationHashes"] = implementation_hashes()
    manifest["artifactHashes"] = {name: hashlib.sha256((output / name).read_bytes()).hexdigest()
        for name in ("source.bin", "compiled.bin", "model.yul", "Driver.lean", "Runner.t.sol", "foundry.toml", "abi.json", "layout.json")
        if (output / name).exists()}
    write_json(output / "manifest.json", manifest)
    return config, metadata, abi, contract["storageLayout"], driver


def parse_evm(path, cases):
    lines = path.read_text().splitlines()
    if len(lines) != len(cases):
        raise HarnessError("missing EVM results")
    results = []
    for i, (line, case) in enumerate(zip(lines, cases)):
        index, status, data, *storage = line.split()
        if index != str(i) or status not in ("ok", "revert") or len(storage) != len(case["observe"]):
            raise HarnessError("invalid EVM result row")
        raw = bytes.fromhex(data.removeprefix("0x"))
        if status == "ok" and len(raw) % 32:
            raise HarnessError("invalid scalar ABI result length")
        results.append({"id": case["id"], "status": status, "data": data,
                        "words": [str(int.from_bytes(raw[k:k+32], "big")) for k in range(0, len(raw), 32)] if status == "ok" else [],
                        "storage": storage})
    return results


def execute(output, cases):
    output = Path(output).resolve()
    manifest = json.loads((output / "manifest.json").read_text())
    if implementation_hashes() != manifest["implementationHashes"]:
        raise HarnessError("implementation changed; prepare a new campaign")
    if not cases:
        raise HarnessError("empty campaign is not a passing comparison")
    for name, digest in manifest.get("artifactHashes", {}).items():
        if hashlib.sha256((output / name).read_bytes()).hexdigest() != digest:
            raise HarnessError("campaign artifact changed: " + name)
    if hashlib.sha256(SOLC.read_bytes()).hexdigest() != manifest["solcSha256"]:
        raise HarnessError("compiler binary changed")
    if command(["forge", "--version"]).strip() != manifest["forge"]:
        raise HarnessError("Foundry version changed")
    if len({case["id"] for case in cases}) != len(cases):
        raise HarnessError("duplicate case identities")
    write_json(output / "model-cases.json", cases)
    write_json(output / "cases.json", {"count": len(cases)})
    # Parse one small document per EVM case, avoiding quadratic JSON work.
    (output / "evm-cases").mkdir(exist_ok=True)
    for index, case in enumerate(cases):
        write_json(output / "evm-cases" / f"{index}.json", case)
    # Delete old outputs: a broken process cannot pass by leaving stale results.
    for file in ("model-results.json", "out/source.txt", "out/compiled.txt"):
        (output / file).unlink(missing_ok=True)
    command(["lake", "env", "lean", "--run", output / "Driver.lean", "run", output / "model-cases.json", output / "model-results.json", manifest["model"]["digest"]],
            timeout=300, log=output / "model-run.log")
    command(["forge", "test", "--root", output, "--match-contract", "SliceDifferentialTest", "-vv"],
            cwd=output, timeout=300, log=output / "forge.log")
    source = parse_evm(output / "out/source.txt", cases)
    compiled = parse_evm(output / "out/compiled.txt", cases)
    model = json.loads((output / "model-results.json").read_text())
    if len(model) != len(cases):
        raise HarnessError("missing model results")
    divergences = []
    for case, a, b, c in zip(cases, source, model, compiled):
        if b["status"] not in ("ok", "revert"):
            raise HarnessError("invalid model status")
        if b["id"] != case["id"]:
            raise HarnessError("model result identity mismatch")
        observable = lambda r: (r["status"], r["words"], r["storage"])
        if observable(a) != observable(b) or observable(b) != observable(c) or a["data"] != c["data"]:
            divergences.append({"case": case, "source": a, "model": b, "compiled": c})
    report = {"cases": len(cases), "successes": sum(r["status"] == "ok" for r in source),
              "reverts": sum(r["status"] == "revert" for r in source), "divergences": divergences}
    write_json(output / "results.json", report)
    return report


def campaign(config_path, output, count, seed):
    started = time.monotonic()
    config, metadata, abi, layout, _ = prepare(config_path, output)
    corpus_path = config.get("corpus")
    corpus = json.loads((Path(config_path).resolve().parent / corpus_path).read_text()) if corpus_path else []
    values = generate(config, count, seed, corpus)
    write_json(Path(output) / "values.json", [{"name": name, **{k: str(v) for k, v in row.items()}} for name, row in values])
    cases = [materialize(config, metadata, abi, layout, row, name) for name, row in values]
    manifest_path = Path(output) / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["casesSha256"] = hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest()
    write_json(manifest_path, manifest)
    report = execute(output, cases)
    report.update(seed=seed, seconds=round(time.monotonic() - started, 3))
    write_json(Path(output) / "results.json", report)
    return report
