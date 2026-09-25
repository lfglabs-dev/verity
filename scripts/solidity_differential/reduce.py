"""Budgeted reducers which preserve the original observable mismatch category."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import time

from .cases import materialize
from .engine import campaign, execute, write_json
from .programs import smaller_expressions, write_program


def signature(divergence):
    if "metamorphic" in divergence:
        return ("metamorphic",)
    routes = [divergence[k] for k in ("source", "model", "compiled")]
    return tuple((key, routes[0][key] == routes[1][key], routes[1][key] == routes[2][key])
                 for key in ("status", "words", "storage", "data")) + (("revert-data", routes[0]["data"] == routes[2]["data"]),)


def reduce_failure(directory, seconds=120):
    directory = Path(directory).resolve()
    report = json.loads((directory / "results.json").read_text())
    if not report["divergences"]:
        raise ValueError("campaign has no divergence to reduce")
    failure = report["divergences"][0]
    if "case" not in failure:
        raise ValueError("only A/B/C case divergences are reducible; inspect metamorphic-divergence.json")
    target = signature(failure)
    manifest = json.loads((directory / "manifest.json").read_text())
    config, metadata = manifest["config"], manifest["model"]
    abi = json.loads((directory / "abi.json").read_text())
    layout = json.loads((directory / "layout.json").read_text())
    name = failure["case"]["id"]
    row = next(row for row in json.loads((directory / "values.json").read_text()) if row["name"] == name)
    best = {k: int(row[k]) for k in config["variables"]}
    scratch = directory / "reduced"
    scratch.mkdir(exist_ok=True)
    for path in directory.iterdir():
        if path.is_file() and path.name not in ("results.json", "values.json"):
            shutil.copyfile(path, scratch / path.name)
    (scratch / "out").mkdir(exist_ok=True)
    deadline = time.monotonic() + seconds
    attempts = 0
    for key in best:
        candidates = sorted({0, 1, 2, best[key] // 2, best[key] & (best[key] - 1)})
        for value in candidates:
            if value >= best[key] or time.monotonic() >= deadline:
                continue
            trial = {**best, key: value}
            result = execute(scratch, [materialize(config, metadata, abi, layout, trial, name)])
            attempts += 1
            if result["divergences"] and signature(result["divergences"][0]) == target:
                best = trial
    final = execute(scratch, [materialize(config, metadata, abi, layout, best, name)])
    if not final["divergences"] or signature(final["divergences"][0]) != target:
        raise ValueError("reduced input did not preserve the divergence")
    write_json(scratch / "values.json", [{"name": name, **{k: str(v) for k, v in best.items()}}])
    reduced_cases = json.loads((scratch / "model-cases.json").read_text())
    manifest["casesSha256"] = hashlib.sha256(json.dumps(reduced_cases, sort_keys=True).encode()).hexdigest()
    write_json(scratch / "manifest.json", manifest)
    # Generated programs additionally admit a typed AST reduction. Do not edit
    # arbitrary production Solidity by textual deletion.
    program_path = directory.parent / "program.json"
    if program_path.exists():
        spec = json.loads(program_path.read_text())
        for tree in smaller_expressions(spec["expression"]):
            if time.monotonic() >= deadline:
                break
            trial = copy.deepcopy(spec)
            trial["expression"] = tree
            program_dir = scratch / "program"
            fixture = write_program(program_dir, trial)
            write_json(program_dir / "corpus.json", [{"name": name, **{k: str(v) for k, v in best.items()}}])
            result = campaign(fixture, program_dir / "run", 0, 0)
            attempts += 1
            if result["divergences"] and signature(result["divergences"][0]) == target:
                spec = trial
                write_json(scratch / "minimal-program.json", spec)
                (scratch / "minimal.sol").write_text((program_dir / "Slice.sol").read_text())
    return {"attempts": attempts, "output": str(scratch), "divergences": final["divergences"]}
