"""Executable mutations of native CREATE2 boundary authentication."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=root / '.lake/native-creation-mutations')
    args = parser.parse_args()
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.NativeCreationBoundary',
             'Contracts.SolidityImportSmoke.NativeCreationBoundaryChecks'], cwd=root,
            timeout=1800, log=job / 'build.log')
    source = root / 'Compiler/Proofs/IRGeneration/NativeCreationBoundary.lean'
    fixture_path = root / 'Contracts/SolidityImportSmoke/NativeCreationBoundaryChecks.lean'
    original = source.read_text()
    namespace = 'Compiler.Proofs.IRGeneration.NativeCreationBoundary'
    prefix = original.split('theorem runtime_schedule', 1)[0] + 'end ' + namespace + '\n'
    prefix = prefix.replace(namespace, namespace + 'Mutation')
    fixture = '\n'.join(line for line in fixture_path.read_text().splitlines()
                        if not line.startswith('import '))
    fixture = fixture.replace(namespace, namespace + 'Mutation')
    smoke = fixture.replace('def main : IO Unit := SolidityImportSmoke.NativeCreationBoundaryChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.NativeCreationBoundaryChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    helpers = fixture.split('def runChecks', 1)[0]
    observe = '''private def observe (result : Except String (IRCreationInterpreter.Outcome Nat)) : IO Unit := do
      match result with
      | .error message => IO.println s!"error:{message}"
      | .ok (.interpretationError message) => IO.println s!"interpretation-error:{message}"
      | .ok (.exceptional _) => IO.println "exceptional"
      | .ok (.stop _) => IO.println "stop"
      | .ok (.revert data _) => IO.println s!"revert:{data.map UInt8.toNat}"
      | .ok (.value _ next) =>
          match next.state.executionContext with
          | some context => IO.println s!"gas:{context.opcode.gas}"
          | none => IO.println "missing-context"
    '''
    def witness(call):
        return helpers + observe + 'def witness : IO Unit := observe (' + call + ')\n' + \
            'end SolidityImportSmoke.NativeCreationBoundaryChecks\n' + \
            'def main : IO Unit := SolidityImportSmoke.NativeCreationBoundaryChecks.witness\n'
    cases = [
        ('native-context-root-gas',
         '{ afterArgs with creationContexts := [CreationCaller.context machine before.warm] }',
         '{ afterArgs with creationContexts := [CreationCaller.context before.machine before.warm] }',
         'run 32 32 before (candidate memory) args'),
        ('native-memory-check-removed', 'if !memoryAgrees machine candidate.state then',
         'if false then', 'run 32 32 before (candidate (memory.writeByte 63 ⟨1, by decide⟩)) args'),
        ('native-memory-bytes-unchecked',
         '(List.range actual.size).all (fun index =>\n      state.byteMemory.readByte index == actual[index]!.toNat)',
         '(List.range actual.size).all (fun index =>\n      state.byteMemory.readByte index == state.byteMemory.readByte index)',
         'run 32 32 before (candidate (memory.writeByte 63 ⟨1, by decide⟩)) args'),
        ('native-operands-check-removed',
         'if values.map (fun word => word % Compiler.Constants.evmModulus) != expected then',
         'if expected != expected then',
         'run 32 32 before (candidate memory) [.lit 0, .lit 0, .lit MidnightInitcode.header.size, .lit 8]'),
    ]
    files = [source, fixture_path, Path(__file__).resolve(),
             root / '.lake/build/lib/lean/Compiler/Proofs/IRGeneration/NativeCreationBoundary.olean']
    manifest = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    lean = (str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean')
            if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' and os.environ.get('LEAN_SYSROOT')
            else 'lean')

    def unchanged():
        return all(hashlib.sha256((root / p).read_bytes()).hexdigest() == h for p, h in manifest.items())

    def run(name, definitions, test):
        assert unchanged()
        driver = job / (name + '.lean')
        driver.write_text(definitions + test)
        with (job / (name + '.log')).open('w') as log:
            result = subprocess.run(['lake', 'env', lean, '--run', str(driver)], cwd=root,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=180)
        lines = (job / (name + '.log')).read_text().splitlines()
        assert result.returncode == 0 and unchanged(), (name, result.returncode, lines)
        return lines

    assert run('positive', prefix, smoke) == [
        'native CREATE2 context, memory and operand authentication passed', 'PASS']
    rows = []
    for name, old, new, call in cases:
        assert prefix.count(old) == 1, (name, prefix.count(old))
        mutated = prefix.replace(old, new)
        failures = run(name + '-smoke', mutated, smoke)
        assert len(failures) == 1 and failures[0].startswith('FAIL:'), (name, failures)
        expected = run(name + '-baseline', prefix, witness(call))
        actual = run(name + '-mutant', mutated, witness(call))
        replay = run(name + '-replay', mutated, witness(call))
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append({'name': name, 'expected': expected, 'actual': actual,
                     'replayed': actual == replay, 'minimal': 'one authenticated creation boundary',
                     'smoke': failures})
    (job / 'success.json').write_text(json.dumps({'mutants': rows, 'sources': manifest,
        'sources_unchanged': unchanged(),
        'scope': 'native boundary component controls; not importer mutation or wholefunction/EVM replay'}, indent=2))


if __name__ == '__main__':
    main()
