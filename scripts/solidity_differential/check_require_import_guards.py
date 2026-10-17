"""Compile actual importer guard mutants and detect over-rejection of supported input.

An importer module must compile before any rejection is scored. Positive and
minimal independent sources must import in the unchanged implementation. The
mutant must emit the precise payload diagnostic at the Solidity source location,
and replay it. These are admission regressions, not giant-string execution tests.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from .engine import HarnessError, command

MUTANTS = {
    'import-require-payload-overreject': (
        'unless requirePayloadFitsWord value do\n    failAt message "require message ABI payload exceeds the EVM word address space"',
        'unless requirePayloadFitsWord value && value.isEmpty do\n    failAt message "require message ABI payload exceeds the EVM word address space"',
        'require', 'require message ABI payload exceeds the EVM word address space'),
    'import-revert-payload-overreject': (
        'unless requirePayloadFitsWord value do\n    failAt args[0]! "revert message ABI payload exceeds the EVM word address space"',
        'unless requirePayloadFitsWord value && value.isEmpty do\n    failAt args[0]! "revert message ABI payload exceeds the EVM word address space"',
        'revert', 'revert message ABI payload exceeds the EVM word address space'),
}


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    source = root / 'Compiler/SolidityImport/Import.lean'
    payload = root / 'Compiler/CompilationModel/RequirePayloadValidation.lean'
    files = sorted(set([source, payload, Path(__file__).resolve(), root / 'lakefile.lean',
                        root / 'lake-manifest.json', root / 'lean-toolchain'] +
                       [p for directory in ('Compiler', 'Verity') for p in (root / directory).rglob('*.lean')]))
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    # Build all original dependencies; mutated modules never replace parent oleans.
    command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=root,
            timeout=1800, log=job / 'build.log')
    raw = source.read_text()
    lean = str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'

    def compile_importer(name, text):
        assert unchanged(), 'campaign inputs changed'
        directory = job / name
        directory.mkdir()
        module = directory / 'PayloadImporter.lean'
        module.write_text(text)
        command(['lake', 'env', lean, '--root=' + str(directory), str(module), '-o', str(module.with_suffix('.olean'))],
                cwd=root, timeout=1200, log=directory / 'compile.log')
        assert module.with_suffix('.olean').is_file()
        assert unchanged(), 'campaign inputs changed'
        return directory

    def probe(directory, name, kind, minimal=False):
        project = job / name
        project.mkdir()
        statement = f'{kind}("x");' if kind == 'revert' else 'require(value > 7, "x");'
        if not minimal:
            message = 'unicode"' + 'é' * 16 + '"'
            statement = f'revert({message});' if kind == 'revert' else f'require(value > 7, {message});'
        (project / 'Fixture.sol').write_text('pragma solidity 0.8.34;\ncontract C {\n'
            ' function probe(uint256 value) external pure returns (uint256) {\n'
            '  ' + statement + ('\n' if kind == 'revert' else '\n  return value;\n') + ' }\n}\n')
        driver = project / 'Check.lean'
        driver.write_text('import PayloadImporter\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Fixture.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            '  contract C\n  function probe(uint256)\n#eval IO.println "IMPORTED"\n')
        # Read Lake's actual dependency search path, then prepend only this private module.
        inherited = command(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root).strip()
        env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + inherited)
        # Invoke the selected Lean directly: `lake env` would overwrite this LEAN_PATH.
        result = subprocess.run([lean, str(driver), '-o', str(driver.with_suffix('.olean'))],
                                cwd=root, env=env, capture_output=True, text=True, timeout=300)
        output = result.stdout + result.stderr
        (project / 'check.log').write_text(output)
        assert unchanged(), 'campaign inputs changed'
        return dict(exit=result.returncode, output=output, artifact=driver.with_suffix('.olean').is_file())

    baseline = compile_importer('baseline', raw)
    rows = []
    for name, (anchor, replacement, kind, diagnostic) in MUTANTS.items():
        assert raw.count(anchor) == 1, name
        positive = probe(baseline, name + '-positive', kind)
        expected = probe(baseline, name + '-expected', kind, minimal=True)
        for control in (positive, expected):
            if control['exit'] or not control['artifact'] or 'IMPORTED' not in control['output']:
                raise HarnessError(f'{name}: unchanged importer failed positive control: {control}')
        mutant = compile_importer(name, raw.replace(anchor, replacement, 1))
        failed = probe(mutant, name + '-detected', kind)
        actual = probe(mutant, name + '-actual', kind, minimal=True)
        replay = probe(mutant, name + '-replay', kind, minimal=True)
        for observation in (failed, actual, replay):
            if (observation['exit'] == 0 or observation['artifact'] or diagnostic not in observation['output'] or
                    not re.search(r'Fixture\.sol:4:\d+:', observation['output']) or
                    'unknown module' in observation['output'] or 'unknown identifier' in observation['output']):
                raise HarnessError(f'{name}: infrastructure/compilation failure is not detection: {observation}')
        # Absolute probe paths differ; compare the actual source-located diagnostic itself.
        def located(observation):
            match = re.search(r'Fixture\.sol:4:\d+:[^\n]*' + re.escape(diagnostic), observation['output'])
            assert match, observation
            return match.group(0)
        assert located(actual) == located(replay)
        rows.append(dict(name=name, positive=positive, expected=expected, failed=failed,
                         actual=actual, replay=replay, located=located(actual)))
        print(name, 'compiled and detected with independent located replay', flush=True)
    artifacts = {str(p.relative_to(job)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in job.rglob('*') if p.suffix in ('.lean', '.sol', '.olean')}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, sources_unchanged=unchanged(),
        identity=identity, artifacts=artifacts, rows=rows), indent=2))


if __name__ == '__main__':
    main()
