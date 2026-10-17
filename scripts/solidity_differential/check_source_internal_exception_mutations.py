"""Mutate actual Source internal-exception transport; require semantic detection and replay."""
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
    fixture = root / 'Contracts/SolidityImportSmoke/SourceInternalExceptionChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.SourceInternalExceptionChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    text = source.read_text()
    failure = 'def failedInternalOutcome' + text.split('def failedInternalOutcome', 1)[1].split('\ntheorem failedInternalOutcome_error', 1)[0]
    projection = 'def exceptionalInternalResult' + text.split('def exceptionalInternalResult', 1)[1].split('\ntheorem exceptionalInternalResult_failedOutcome', 1)[0]
    body = failure + '\n' + projection
    prefix = ('import Compiler.Proofs.IRGeneration.SourceSemantics\n'
              'set_option linter.unusedVariables false\n'
              'namespace InternalSourceExceptionMutation\n'
              'open Compiler.CompilationModel Compiler.Proofs.IRGeneration.SourceSemantics\n')
    runtime = fixture.read_text().split('private def model', 1)[1]
    runtime = ('namespace SolidityImportSmoke.SourceInternalExceptionChecks\n'
               'open Compiler.CompilationModel Compiler.Proofs.IRGeneration\n'
               'open SourceSemantics\nprivate def model' + runtime)
    runtime = runtime.replace('exceptionalInternalResult initial.world',
                              'InternalSourceExceptionMutation.exceptionalInternalResult initial.world')
    runtime = runtime.replace('failedInternalOutcome ', 'InternalSourceExceptionMutation.failedInternalOutcome ')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.SourceInternalExceptionChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourceInternalExceptionChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''open Compiler.CompilationModel Compiler.Proofs.IRGeneration.SourceSemantics
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 0, depth := 7, isStatic := false }, warm := fun _ => false }
def main : IO Unit := do
  let terminal : RuntimeState :=
    { world := Verity.defaultState.writeSlot 0 99, bindings := [], executionContext := some context }
  let projected := InternalSourceExceptionMutation.exceptionalInternalResult Verity.defaultState terminal
  let result := { projected with interpretationError := ERROR }
  let status := match InternalSourceExceptionMutation.failedInternalOutcome result with
    | .exceptional observed => s!"exception:{observed.executionContext.map (fun (frame : Verity.Core.Model.ExecutionContext) => frame.opcode.gas)}:{observed.executionContext.map (fun (frame : Verity.Core.Model.ExecutionContext) => frame.opcode.depth)}"
    | .interpretationError message => s!"refusal:{message}"
    | .revertWithData bytes => s!"revert:{bytes.length}"
    | _ => "other"
  IO.println s!"{status}:{(result.world.readSlot 0).val}"
'''
    cases = [
        ('source-internal-exception-state-erased', 'exceptionalState := some terminal',
         'exceptionalState := none', 'none'),
        ('source-internal-exception-became-revert', '| some terminal => .exceptional terminal',
         '| some _ => .revertWithData result.revertData', 'none'),
        ('source-internal-exception-rollback-erased',
         '{ revertedInternalResult initialWorld with exceptionalState := some terminal }',
         '{ revertedInternalResult terminal.world with exceptionalState := some terminal }', 'none'),
        ('source-internal-exception-refusal-erased', '| some message => .interpretationError message',
         '| some _ => .revertWithData result.revertData', 'some "instrument refusal"'),
    ]
    files = [source, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    def run(name, implementation, test):
        path = job / (name + '.lean')
        path.write_text(prefix + implementation + '\nend InternalSourceExceptionMutation\n' + test)
        return command(['lake', 'env', 'lean', '--run', str(path)], cwd=root,
                       timeout=180, log=job / (name + '.log')).splitlines()

    rows = []
    for name, old, new, error in cases:
        assert body.count(old) == 1, name
        mutant = body.replace(old, new, 1)
        baseline = run(name + '-baseline', body, runtime)
        assert baseline == ['Source internal exception carrier, rollback, refusal and revert checks passed', 'PASS'], baseline
        detected = run(name + '-mutant', mutant, runtime)
        assert len(detected) == 1 and detected[0].startswith('FAIL:'), detected
        test = witness.replace('ERROR', error)
        expected = run(name + '-minimal-baseline', body, test)
        actual = run(name + '-minimal-mutant', mutant, test)
        replay = run(name + '-minimal-replay', mutant, test)
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append(dict(name=name, baseline=baseline, detected=detected,
                         expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2))
    print('4 Source internal exception mutants detected and independently replayed')


if __name__ == '__main__':
    main()
