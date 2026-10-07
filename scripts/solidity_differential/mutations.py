"""Compile actual importer/Denote mutants in isolated source/cache snapshots."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

from .engine import ROOT, WORKSPACE, HarnessError, command, write_json

MUTANTS = {
    "import-require-condition": ("Compiler/SolidityImport/Import.lean", 'return condition.pre.push (.require condition.expr value)', 'return condition.pre.push (.require (.literal 1) value)'),
    "denote-require-selector": ("Verity/Core/Model/Denote.lean", '[0x08, 0xc3, 0x79, 0xa0]', '[0x08, 0xc3, 0x79, 0xa1]'),
    "import-custom-require-condition": ("Compiler/SolidityImport/Import.lean", '(.requireError condition.expr name values)', '(.requireError (.literal 1) name values)'),
    "denote-custom-require-selector": ("Verity/Core/Model/Denote.lean", '(wordBytes hash).take 4', '((wordBytes hash).drop 1).take 4'),
    "denote-custom-require-argument": ("Verity/Core/Model/Denote.lean", 'return selector ++ values.flatMap wordBytes', 'return selector ++ values.flatMap (fun value => wordBytes (value + 1))'),
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
    for compiler_name in ("solc-0.8.34", "solc-0.8.10"):
        compiler_src = WORKSPACE / ".lake/solidity-import" / compiler_name
        if compiler_src.exists():
            shutil.copy2(compiler_src, cache / "solidity-import" / compiler_name)


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    from .check_environment_mutations import MUTANTS as CONTEXT_MUTANTS
    from .check_environment_mutations import mutation_campaign as context_campaign
    from .check_storage_mutations import MUTANTS as STORAGE_MUTANTS
    from .check_storage_mutations import mutation_campaign as storage_campaign
    from .check_abi_mutations import MUTANTS as ABI_MUTANTS
    from .check_abi_mutations import mutation_campaign as abi_campaign
    from .check_struct_abi_mutations import MUTANTS as STRUCT_ABI_MUTANTS
    from .check_struct_abi_mutations import mutation_campaign as struct_abi_campaign
    from .check_abi_length_for_mutations import MUTANTS as ARRAY_FOR_MUTANTS
    from .check_abi_length_for_mutations import mutation_campaign as array_for_campaign
    from .check_scalar_array_abi_mutations import MUTANTS as SCALAR_ARRAY_MUTANTS
    from .check_scalar_array_abi_mutations import mutation_campaign as scalar_array_campaign
    from .check_market_abi_mutations import MUTANTS as MARKET_ABI_MUTANTS
    from .check_market_abi_mutations import mutation_campaign as market_abi_campaign
    from .check_multiple_dynamic_abi_mutations import MUTANTS as MULTIPLE_ABI_MUTANTS
    from .check_multiple_dynamic_abi_mutations import mutation_campaign as multiple_abi_campaign
    for name in selected or [*MUTANTS, *CONTEXT_MUTANTS, *STORAGE_MUTANTS, *ABI_MUTANTS, *STRUCT_ABI_MUTANTS, *SCALAR_ARRAY_MUTANTS, *ARRAY_FOR_MUTANTS, *MARKET_ABI_MUTANTS, *MULTIPLE_ABI_MUTANTS]:
        if name in MULTIPLE_ABI_MUTANTS:
            result = multiple_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in MARKET_ABI_MUTANTS:
            result = market_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in ARRAY_FOR_MUTANTS:
            result = array_for_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / 'mutation-results.json', reports)
            continue
        if name in SCALAR_ARRAY_MUTANTS:
            result = scalar_array_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in STRUCT_ABI_MUTANTS:
            result = struct_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in ABI_MUTANTS:
            result = abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in STORAGE_MUTANTS:
            storage = storage_campaign(output, [name])
            reports.extend(storage['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in CONTEXT_MUTANTS:
            context = context_campaign(output, [name])
            reports.extend(context['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        relative, before, after = MUTANTS[name]
        directory = output / name
        if directory.exists():
            raise HarnessError("mutation output already exists; choose a fresh output: " + str(directory))
        snapshot(directory)
        source = directory / relative
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError("mutation anchor drifted: " + name)
        config = "differential-require.json" if "require" in name else "differential.json"
        if "custom-require" in name:
            config = "differential-require-custom.json"
        argv = [sys.executable, str(directory / "scripts/solidity_import_differential.py"),
                "--config", str(directory / "Contracts/SolidityImportSmoke" / config),
                "--output", str(directory / ".lake/campaign"), "--cases", "8"]
        # A pre-existing fixture divergence is not evidence that a mutation was
        # detected. Run the identical inputs in the private snapshot first.
        baseline_argv = [str(directory / ".lake/baseline") if arg == str(directory / ".lake/campaign")
                         else arg for arg in argv]
        baseline = subprocess.run(baseline_argv, cwd=directory, text=True,
                                  capture_output=True, timeout=600)
        (directory / "baseline.log").write_text(baseline.stdout + baseline.stderr)
        baseline_file = directory / ".lake/baseline/results.json"
        baseline_report = json.loads(baseline_file.read_text()) if baseline_file.exists() else {}
        if (baseline.returncode != 0 or baseline_report.get("divergences") != [] or
                baseline_report.get("cases", 0) <= 0):
            raise HarnessError("mutation positive control failed: " + name)
        source.write_text(text.replace(before, after))
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
