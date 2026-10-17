"""Mutate the actual Denote public exception projection, never counting compile failures."""
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
    source = root / 'Verity/Core/Model/Denote.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/DenotePublicExceptionChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.DenotePublicExceptionChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    body = 'def exceptionalResult' + source.read_text().split('def exceptionalResult', 1)[1].split('\ndef successResult', 1)[0]
    projection = root / 'Compiler/Proofs/IRGeneration/DenoteFunctionAgreement.lean'
    body += '\ndef toSourceResult' + projection.read_text().split('def toSourceResult', 1)[1].split('\n@[simp] theorem toSourceResult_revertData', 1)[0]
    prefix = ('import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement\n'
              'namespace PublicDenoteExceptionMutation\n'
              'open Compiler.CompilationModel Compiler.Proofs.IRGeneration Denote\n')
    def definitions(actual):
        return prefix + actual + '\nend PublicDenoteExceptionMutation\n'
    runtime = fixture.read_text().split('private def oracle', 1)[1]
    runtime = ('namespace SolidityImportSmoke.DenotePublicExceptionChecks\n'
               'open Compiler.CompilationModel Denote\nprivate def oracle' + runtime)
    runtime = runtime.replace('exceptionalResult oracle model', 'PublicDenoteExceptionMutation.exceptionalResult oracle model')
    runtime = runtime.replace('Compiler.Proofs.IRGeneration.DenoteAgreement.toSourceResult', 'PublicDenoteExceptionMutation.toSourceResult')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.DenotePublicExceptionChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.DenotePublicExceptionChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''open Compiler.CompilationModel Denote
private def context (gas : Nat) : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := gas, depth := 2, isStatic := false }, warm := fun _ => false }
def main : IO Unit := do
  let model : CompilationModel := { name := "Witness", fields := [], functions := [], constructor := none }
  let state : DenoteState := { world := Verity.defaultState.writeSlot 0 99, bindings := [], executionContext := CONTEXT }
  let result := PublicDenoteExceptionMutation.exceptionalResult { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 } model Verity.defaultState state
  let result := PublicDenoteExceptionMutation.toSourceResult result
  IO.println s!"{result.exceptionalContext.map (·.opcode.gas)}:{result.interpretationError}:{result.finalStorage 0}"
'''
    cases = [
        ('denote-public-exception-source-projection-erased', 'exceptionalContext := r.exceptionalContext',
         'exceptionalContext := none', 'some (context 0)'),
        ('denote-public-exception-context-erased', 'exceptionalContext := some context',
         'exceptionalContext := none', 'some (context 0)'),
        ('denote-public-exception-nonzero-gas-accepted', 'if context.opcode.gas = 0 then',
         'if true then', 'some (context 19)'),
        ('denote-public-exception-missing-context-revert',
         'interpretationError := some "exceptional exit requires actual opcode context"',
         'interpretationError := none', 'none'),
        ('denote-public-exception-rollback-erased',
         '{ revertedResult oracle spec initialWorld with exceptionalContext := some context }',
         '{ revertedResult oracle spec terminal.world with exceptionalContext := some context }', 'some (context 0)'),
    ]
    files = [source, projection, fixture, Path(__file__).resolve()]
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
        assert baseline == ['Denote public exception context, refusal and rollback checks passed', 'PASS'], baseline
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
    print('5 Denote public exception mutants detected and independently replayed')


if __name__ == '__main__':
    main()
