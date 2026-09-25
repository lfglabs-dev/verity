"""Compile actual importer/Denote mutants in isolated source/cache snapshots."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

from .engine import ROOT, WORKSPACE, HarnessError, command, write_json

MUTANTS = {
    "denote-panic-selector": ("Verity/Core/Model/Denote.lean", '[0x4e, 0x48, 0x7b, 0x71]', '[0x4e, 0x48, 0x7b, 0x70]'),
    "denote-panic-endian": ("Verity/Core/Model/Denote.lean", 'value / 2^(8*(31-i))', 'value / 2^(8*i)'),
    "import-comparison": ("Compiler/SolidityImport/Import.lean", '| "<" => cmp .lt left right', '| "<" => cmp .gt left right'),
    "import-field-slot": ("Compiler/SolidityImport/Import.lean", 'slot := some slot }', 'slot := some (slot + 1) }'),
    "denote-packed-mask": ("Verity/Core/Model/Denote.lean", '(2 ^ packed.width) - 1', '(2 ^ packed.width) - 2'),
    "denote-storage-read": ("Verity/Core/Model/Denote.lean", '    world.readSlot (wordNormalize slot)\n', '    world.readSlot (wordNormalize (slot + 1))\n'),
}


def snapshot(destination):
    destination.mkdir(parents=True, exist_ok=False)
    paths = command(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).split("\0")
    for name in paths:
        if not name or not (ROOT / name).is_file():
            continue
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
    cache = destination / ".lake"
    cache.mkdir(exist_ok=True)
    (cache / "packages").symlink_to(WORKSPACE / ".lake/packages", target_is_directory=True)
    # Private copy-on-write cache: no hardlinks/symlinks to mutable parent oleans.
    if sys.platform == "darwin":
        command(["/bin/cp", "-cR", WORKSPACE / ".lake/build", cache / "build"], timeout=300)
    else:
        command(["cp", "-a", "--reflink=auto", WORKSPACE / ".lake/build", cache / "build"], timeout=300)
    (cache / "solidity-import").mkdir()
    shutil.copy2(WORKSPACE / ".lake/solidity-import/solc-0.8.34", cache / "solidity-import/solc-0.8.34")


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        relative, before, after = MUTANTS[name]
        directory = output / name
        if directory.exists():
            raise HarnessError("mutation output already exists; choose a fresh output: " + str(directory))
        snapshot(directory)
        source = directory / relative
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError("mutation anchor drifted: " + name)
        source.write_text(text.replace(before, after))
        argv = [sys.executable, str(directory / "scripts/solidity_import_differential.py"),
                "--config", str(directory / "Contracts/SolidityImportSmoke/differential.json"),
                "--output", str(directory / ".lake/campaign"), "--cases", "8"]
        try:
            result = subprocess.run(argv, cwd=directory, text=True, capture_output=True, timeout=600)
            (directory / "mutation.log").write_text(result.stdout + result.stderr)
            report_file = directory / ".lake/campaign/results.json"
            report = json.loads(report_file.read_text()) if report_file.exists() else {}
            if result.returncode == 1 and report.get("divergences"):
                status = "detected"
            elif result.returncode == 0:
                status = "survived"
            else:
                status = "invalid"  # compilation/tool failure does not kill a mutant
        except subprocess.TimeoutExpired:
            status = "invalid"
        reports.append({"mutant": name, "status": status, "path": relative, "output": str(directory)})
        write_json(output / "mutation-results.json", reports)
        print(f"{name}: {status}", flush=True)
    return {"mutants": reports, "divergences": [r for r in reports if r["status"] != "detected"]}
