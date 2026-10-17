"""Mutate actual mutually recursive helper receipt schedules; compile errors never count."""
import argparse
import hashlib
import json
from pathlib import Path
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    options = parser.parse_args()
    job = options.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    source = root / 'Compiler/Proofs/IRGeneration/SourceSemantics.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/SourceHelperExternalChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.SourceHelperExternalChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    text = source.read_text()
    recursive = 'set_option maxHeartbeats 400000 in\nmutual\n  /-- Spec-aware'
    block = recursive + text.split(recursive, 1)[1].split('\nend\n\ntheorem evalExprListWithHelpers_length_of_some', 1)[0] + '\nend\n'
    find = 'private def findUniqueInternalFunction?' + text.split('private def findUniqueInternalFunction?', 1)[1].split('\nstructure ExternalCallOutcome', 1)[0]
    aliases = 'private def ceilDivVal' + text.split('private def ceilDivVal', 1)[1].split('\ndef evalExpr (', 1)[0]
    success = 'def successInternalResult' + text.split('def successInternalResult', 1)[1].split('\ndef bindSupportedParams', 1)[0]
    body = success + '\n' + block
    prefix = ('import Compiler.Proofs.IRGeneration.SourceSemantics\n'
              'set_option linter.unusedVariables false\n'
              'set_option linter.unusedSimpArgs false\n'
              'namespace HelperExternalMutation\n'
              'open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration\n'
              'open Compiler.Proofs.IRGeneration.SourceSemantics\n' + find + '\n' + aliases + '\n')
    files = [source, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    token = hashlib.sha256(str(job).encode()).hexdigest()[:12]
    artifacts = {}

    def compile_definition(label, definition):
        module = 'HelperExternalMutation' + token + label
        path = job / (module + '.lean')
        path.write_text(prefix + definition + '\nend HelperExternalMutation\n')
        output = root / '.lake/build/lib/lean' / (module + '.olean')
        command(['lake', 'env', 'lean', '--root', job, '-o', output, path],
                cwd=root, timeout=300, log=job / (label + '-compile.log'))
        artifacts[module] = hashlib.sha256(path.read_bytes()).hexdigest()
        return module

    runtime = fixture.read_text().split('namespace SolidityImportSmoke.SourceHelperExternalChecks', 1)[1]
    runtime = 'namespace SolidityImportSmoke.SourceHelperExternalChecks' + runtime
    for name in ['execStmtWithHelpers', 'execStmtListWithHelpers', 'evalExprWithHelpers', 'interpretInternalFunctionFuel']:
        runtime = runtime.replace(name + ' model', 'HelperExternalMutation.' + name + ' model')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.SourceHelperExternalChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourceHelperExternalChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    setup = fixture.read_text().split('private def leaf', 1)[1].split('\nprivate def checkIndex', 1)[0]
    setup = 'open Compiler.CompilationModel Compiler.Proofs.IRGeneration\nopen SourceSemantics\nprivate def leaf' + setup
    witness = setup + '''
def describe (result : StmtResult) : String :=
  match result with
  | .continue state => s!"continue:{state.externalCallIndex}:{(state.world.readSlot 0).val}:{lookupBinding? state.bindings "value"}"
  | .revertWithData data => s!"revert:{data.map UInt8.toNat}"
  | .interpretationError message => s!"refusal:{message}"
  | _ => "other"
def main : IO Unit := do
  let result := TEST
  IO.println (describe result)
'''
    direct = '(let result := HelperExternalMutation.interpretInternalFunctionFuel model 16 leaf initial.world [] (externalCallOracle := oracle) (externalCallIndex := 3) (executionContext := initial.executionContext); if result.success then StmtResult.continue { initial with world := result.world, externalCallIndex := result.externalCallIndex } else failedInternalOutcome result)'
    void_call = 'HelperExternalMutation.execStmtWithHelpers model [] 16 initial (.internalCall "leaf" [])'
    assign_call = 'HelperExternalMutation.execStmtWithHelpers model [] 16 initial (.internalCallAssign ["value"] "leaf" [])'
    call = 'let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals\n                  (externalCallOracle := state.externalCallOracle)\n                  (externalCallIndex := state.externalCallIndex)\n                  (executionContext := state.executionContext)'
    void_suffix = '\n                if hresult.success then\n                  .continue { state with world := hresult.world, executionContext := hresult.executionContext, externalCallIndex := hresult.externalCallIndex }'
    assign_suffix = '\n                if hresult.success then\n                  match names, hresult.returnValue with'
    void_resume = '.continue { state with world := hresult.world, executionContext := hresult.executionContext, externalCallIndex := hresult.externalCallIndex }'
    assign_resume = 'world := hresult.world, executionContext := hresult.executionContext, externalCallIndex := hresult.externalCallIndex\n                        bindings := bindValue'
    expr_suffix = '\n            if hresult.success then hresult.returnValue else none'
    expr_call = call.replace('\n                  (externalCallOracle', '\n                  (externalCallOracle')
    expr_test = '(match HelperExternalMutation.evalExprWithHelpers model [] 16 initial (.internalCall "leaf" []) with | some value => StmtResult.continue { initial with bindings := bindValue initial.bindings "value" value } | none => StmtResult.revert)'
    cases = [
        ('expression-oracle-erased', expr_call + expr_suffix,
         expr_call.replace('state.externalCallOracle', '(fun _ => ⟨false, [], none⟩)') + expr_suffix, expr_test),
        ('expression-cursor-erased', expr_call + expr_suffix,
         expr_call.replace('state.externalCallIndex', '0') + expr_suffix, expr_test),
        ('entry-oracle-erased', 'externalCallOracle := externalCallOracle,\n              externalCallIndex := externalCallIndex,',
         'externalCallOracle := (fun _ => ⟨false, [], none⟩),\n              externalCallIndex := externalCallIndex,', direct),
        ('entry-cursor-erased', 'externalCallIndex := externalCallIndex, executionContext := executionContext,',
         'externalCallIndex := 0, executionContext := executionContext,', direct),
        ('void-oracle-erased', call + void_suffix,
         call.replace('state.externalCallOracle', '(fun _ => ⟨false, [], none⟩)') + void_suffix, void_call),
        ('assign-oracle-erased', call + assign_suffix,
         call.replace('state.externalCallOracle', '(fun _ => ⟨false, [], none⟩)') + assign_suffix, assign_call),
        ('void-cursor-erased', call + void_suffix,
         call.replace('state.externalCallIndex', '0') + void_suffix, void_call),
        ('assign-cursor-erased', call + assign_suffix,
         call.replace('state.externalCallIndex', '0') + assign_suffix, assign_call),
        ('success-cursor-erased', 'externalCallIndex := externalCallIndex\n    world := world',
         'externalCallIndex := 0\n    world := world', direct),
        ('void-resume-cursor-erased', void_resume,
         void_resume.replace('hresult.externalCallIndex', 'state.externalCallIndex'), void_call),
        ('assign-resume-cursor-erased', assign_resume,
         assign_resume.replace('hresult.externalCallIndex', 'state.externalCallIndex'), assign_call),
    ]

    def run(label, module, test):
        path = job / (label + '.lean')
        path.write_text('import ' + module + '\n' + test)
        return command(['lake', 'env', 'lean', '--run', path], cwd=root,
                       timeout=180, log=job / (label + '.log')).splitlines()

    baseline = compile_definition('Baseline', body)
    positive = run('baseline', baseline, runtime)
    assert positive == ['Source helper actual oracle, nested receipt cursor, caught failure and resume checks passed', 'PASS'], positive
    rows = []
    for index, (name, old, new, test) in enumerate(cases):
        assert body.count(old) == 1, (name, body.count(old))
        module = compile_definition('Mutant' + str(index), body.replace(old, new, 1))
        detected = run(name + '-mutant', module, runtime)
        assert len(detected) == 1 and detected[0].startswith('FAIL:'), detected
        minimal = witness.replace('TEST', test)
        expected = run(name + '-minimal-baseline', baseline, minimal)
        actual = run(name + '-minimal-mutant', module, minimal)
        replay = run(name + '-minimal-replay', module, minimal)
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append(dict(name=name, baseline=positive, detected=detected,
                         expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, clones=artifacts, rows=rows), indent=2))
    print('11 Source helper receipt schedule mutants detected and independently replayed')


if __name__ == '__main__':
    main()
