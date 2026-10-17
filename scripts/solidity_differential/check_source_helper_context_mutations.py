"""Mutate actual mutually recursive helper context semantics; compile errors never count."""
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
    fixture = root / 'Contracts/SolidityImportSmoke/SourceHelperContextChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.SourceHelperContextChecks'],
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
              'namespace HelperContextMutation\n'
              'open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration\n'
              'open Compiler.Proofs.IRGeneration.SourceSemantics\n' + find + '\n' + aliases + '\n')
    files = [source, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    token = hashlib.sha256(str(job).encode()).hexdigest()[:12]
    artifacts = {}

    def compile_definition(label, definition):
        module = 'HelperContextMutation' + token + label
        path = job / (module + '.lean')
        path.write_text(prefix + definition + '\nend HelperContextMutation\n')
        output = root / '.lake/build/lib/lean' / (module + '.olean')
        command(['lake', 'env', 'lean', '--root', job, '-o', output, path],
                cwd=root, timeout=300, log=job / (label + '-compile.log'))
        artifacts[module] = hashlib.sha256(path.read_bytes()).hexdigest()
        return module

    runtime = fixture.read_text().split('namespace SolidityImportSmoke.SourceHelperContextChecks', 1)[1]
    runtime = 'namespace SolidityImportSmoke.SourceHelperContextChecks' + runtime
    for name in ['execStmtWithHelpers', 'interpretInternalFunctionFuel']:
        runtime = runtime.replace(name + ' model', 'HelperContextMutation.' + name + ' model')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.SourceHelperContextChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourceHelperContextChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    setup = fixture.read_text().split('private def leaf', 1)[1].split('\nprivate def checkException', 1)[0]
    setup = 'open Compiler.CompilationModel Compiler.Proofs.IRGeneration\nopen SourceSemantics\nprivate def leaf' + setup
    witness = setup + '''
def describe (result : StmtResult) : String :=
  match result with
  | .exceptional terminal => s!"exception:{terminal.executionContext.map (fun (frame : Verity.Core.Model.ExecutionContext) => frame.opcode.gas)}:{terminal.executionContext.map (fun (frame : Verity.Core.Model.ExecutionContext) => frame.opcode.depth)}"
  | .interpretationError message => s!"refusal:{message}"
  | .continue terminal => s!"continue:{terminal.executionContext.map (fun (frame : Verity.Core.Model.ExecutionContext) => frame.opcode.gas)}:{lookupBinding? terminal.bindings "value"}"
  | _ => "other"
def main : IO Unit := do
  let result := TEST
  IO.println (describe result)
'''
    direct = '(failedInternalOutcome (HelperContextMutation.interpretInternalFunctionFuel model 8 leaf initial.world [] (executionContext := initial.executionContext)))'
    void_call = 'HelperContextMutation.execStmtWithHelpers model [] 8 initial (.internalCall "leaf" [])'
    assign_call = 'HelperContextMutation.execStmtWithHelpers model [] 8 initial (.internalCallAssign ["value"] "leaf" [])'
    successful_void = 'HelperContextMutation.execStmtWithHelpers model [] 8 initial (.internalCall "returning" [])'
    successful_assign = 'HelperContextMutation.execStmtWithHelpers model [] 8 initial (.internalCallAssign ["value"] "returning" [])'
    call = 'let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals\n                  (externalCallOracle := state.externalCallOracle)\n                  (externalCallIndex := state.externalCallIndex)\n                  (executionContext := state.executionContext)'
    void_resume = '.continue { state with world := hresult.world, executionContext := hresult.executionContext, externalCallIndex := hresult.externalCallIndex }'
    assign_resume = 'world := hresult.world, executionContext := hresult.executionContext, externalCallIndex := hresult.externalCallIndex\n                        bindings := bindValue'
    cases = [
        ('entry-context-erased', 'externalCallIndex := externalCallIndex, executionContext := executionContext,',
         'externalCallIndex := externalCallIndex, executionContext := none,', direct),
        ('void-call-context-erased', call + '\n                if hresult.success then\n                  ' + void_resume,
         call.replace('state.executionContext', 'none') + '\n                if hresult.success then\n                  ' + void_resume, void_call),
        ('assign-call-context-erased', call + '\n                if hresult.success then\n                  match names, hresult.returnValue with',
         call.replace('state.executionContext', 'none') + '\n                if hresult.success then\n                  match names, hresult.returnValue with', assign_call),
        ('success-result-context-erased', 'executionContext := executionContext\n    externalCallIndex := externalCallIndex\n    world := world',
         'executionContext := none\n    externalCallIndex := externalCallIndex\n    world := world', successful_assign),
        ('void-resume-context-erased', void_resume,
         void_resume.replace('hresult.executionContext', 'none'), successful_void),
        ('assign-resume-context-erased', assign_resume,
         assign_resume.replace('hresult.executionContext', 'none'), successful_assign),
        ('exceptional-terminal-erased', '| .exceptional terminal => exceptionalInternalResult initialWorld terminal',
         '| .exceptional _ => revertedInternalResult initialWorld', direct),
    ]

    def run(label, module, test):
        path = job / (label + '.lean')
        path.write_text('import ' + module + '\n' + test)
        return command(['lake', 'env', 'lean', '--run', path], cwd=root,
                       timeout=180, log=job / (label + '.log')).splitlines()

    baseline = compile_definition('Baseline', body)
    positive = run('baseline', baseline, runtime)
    assert positive == ['Source helper actual-context entry, nested exception and success checks passed', 'PASS'], positive
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
    print('7 Source helper context mutants detected and independently replayed')


if __name__ == '__main__':
    main()
