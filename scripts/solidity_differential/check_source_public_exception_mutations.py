"""Mutate the actual Source public exception projection, never counting compile failures."""
import argparse
import hashlib
import json
from pathlib import Path
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    source = root / 'Compiler/Proofs/IRGeneration/SourceSemantics.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/SourcePublicExceptionChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.SourcePublicExceptionChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    body = 'def exceptionalResult' + source.read_text().split('def exceptionalResult', 1)[1].split('\ntheorem exceptionalResult_of_exhausted_context', 1)[0]
    prefix = ('import Compiler.Proofs.IRGeneration.SourceSemantics\n'
              'namespace PublicSourceExceptionMutation\n'
              'open Compiler.CompilationModel Compiler.Proofs.IRGeneration.SourceSemantics\n')
    def definitions(actual):
        return prefix + actual + '\nend PublicSourceExceptionMutation\n'
    runtime = fixture.read_text().split('private def model', 1)[1]
    runtime = ('namespace SolidityImportSmoke.SourcePublicExceptionChecks\n'
               'open Compiler.CompilationModel Compiler.Proofs.IRGeneration\n'
               'open SourceSemantics\nprivate def model' + runtime)
    runtime = runtime.replace('exceptionalResult model', 'PublicSourceExceptionMutation.exceptionalResult model')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.SourcePublicExceptionChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourcePublicExceptionChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''open Compiler.CompilationModel Compiler.Proofs.IRGeneration.SourceSemantics
private def context (gas : Nat) : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := gas, depth := 2, isStatic := false }, warm := fun _ => false }
def main : IO Unit := do
  let model : CompilationModel := { name := "Witness", fields := [], functions := [], constructor := none }
  let state : RuntimeState := { world := Verity.defaultState.writeSlot 0 99, bindings := [], executionContext := CONTEXT }
  let result := PublicSourceExceptionMutation.exceptionalResult model Verity.defaultState state
  IO.println s!"{result.exceptionalContext.map (·.opcode.gas)}:{result.interpretationError}:{result.finalStorage 0}"
'''
    cases = [
        ('source-public-exception-context-erased', 'exceptionalContext := some context',
         'exceptionalContext := none', 'some (context 0)'),
        ('source-public-exception-nonzero-gas-accepted', 'if context.opcode.gas = 0 then',
         'if true then', 'some (context 19)'),
        ('source-public-exception-missing-context-revert',
         'interpretationError := some "exceptional exit requires actual opcode context"',
         'interpretationError := none', 'none'),
        ('source-public-exception-rollback-erased',
         '{ revertedResult spec initialWorld with exceptionalContext := some context }',
         '{ revertedResult spec terminal.world with exceptionalContext := some context }', 'some (context 0)'),
    ]
    files = [source, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def run(name, implementation, test):
        path = job / (name + '.lean')
        path.write_text(definitions(implementation) + test)
        return command(['lake', 'env', 'lean', '--run', str(path)], cwd=root,
                       timeout=180, log=job / (name + '.log')).splitlines()
    rows = []
    for name, old, new, context in cases:
        assert body.count(old) == 1, name
        mutant = body.replace(old, new, 1)
        baseline = run(name + '-baseline', body, runtime)
        assert baseline == ['Source public exception context, refusal and rollback checks passed', 'PASS'], baseline
        detected = run(name + '-mutant', mutant, runtime)
        assert len(detected) == 1 and detected[0].startswith('FAIL:'), detected
        test = witness.replace('CONTEXT', context)
        expected = run(name + '-minimal-baseline', body, test)
        actual = run(name + '-minimal-mutant', mutant, test)
        replay = run(name + '-minimal-replay', mutant, test)
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append(dict(name=name, baseline=baseline, detected=detected,
                         expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2))
    print('4 Source public exception mutants detected and independently replayed')


if __name__ == '__main__':
    main()
