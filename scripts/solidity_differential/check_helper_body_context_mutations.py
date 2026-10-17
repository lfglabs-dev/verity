"""Mutate actual helper-body bridge definitions; compiler failures never count."""
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
    source = root / 'Compiler/Proofs/IRGeneration/InternalHelperBodyCorrespondence.lean'
    bridge = root / 'Compiler/Proofs/IRGeneration/HelperBodyBridge.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/HelperBodyContextChecks.lean'
    files = [source, bridge, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.HelperBodyContextChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    src, ir = source.read_text(), bridge.read_text()
    body = src[src.index('def internalHelperBodyRuntime'):src.index('noncomputable def internalHelperBodyIRExec')]
    body += src[src.index('def internalHelperResultOfStmtResult'):src.index('theorem interpretInternalFunctionFuel_eq_')]
    body += src[src.index('def internalHelperBodyInterpretation'):src.index('/-- Soundness of an internal-helper summary')]
    body += ir[ir.index('def internalHelperBodyIRExecResultAsCallResult'):ir.index('/-- N1a helper-body bridge:')]
    body += ir[ir.index('abbrev internalHelperAssignCallResult'):ir.index('private theorem execIRStmtsWithInternals_singleton_expr_')]
    prefix = ('import Compiler.Proofs.IRGeneration.HelperBodyBridge\n'
              'set_option linter.unusedVariables false\n'
              'set_option linter.unusedSimpArgs false\n'
              'namespace HelperBodyMutation\n'
              'open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration\n')
    token = hashlib.sha256(str(job).encode()).hexdigest()[:12]
    clones = {}

    def compile_definition(label, text):
        module = 'HelperBodyMutation' + token + label
        path = job / (module + '.lean')
        path.write_text(prefix + text + '\nend HelperBodyMutation\n')
        command(['lake', 'env', 'lean', '-o', root / '.lake/build/lib/lean' / (module + '.olean'), path],
                cwd=root, timeout=180, log=job / (module + '-compile.log'))
        clones[module] = hashlib.sha256(path.read_bytes()).hexdigest()
        return module

    runtime = ('namespace SolidityImportSmoke.HelperBodyContextChecks\n'
               'open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration\nopen SourceSemantics\n'
               'private def errors' + fixture.read_text().split('private def errors', 1)[1])
    names = ['internalHelperBodyInterpretation', 'internalHelperBodyIRExecResultAsCallResult',
             'internalHelperAssignCallResult']
    for name in names:
        runtime = runtime.replace(name + ' ', 'HelperBodyMutation.' + name + ' ')
    runtime = runtime.replace('def main : IO Unit := SolidityImportSmoke.HelperBodyContextChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.HelperBodyContextChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''
open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 7, isStatic := false }, warm := fun _ => false }
private def caller : IRState := { IRState.initial 7 with vars := [("caller", 51)] }
private def terminal : IRState :=
  { (caller.writePhysicalMemoryValue 0 0xdead).captureRevert 30 2 with
    vars := [("callee", 99)], executionContext := some context }
private def helper : IRInternalFunctionDef := { name := "h", params := [], rets := [], body := [] }
private def describeIR : IRValuesEvalResult → String
  | .revert state => s!"revert:{state.revertBytes.map (List.map UInt8.toNat)}:{state.vars}"
  | .exceptional state => s!"exception:{state.executionContext.map (fun (c : Verity.Core.Model.ExecutionContext) => c.opcode.depth)}:{state.vars}"
  | .interpretationError message => s!"refusal:{message}"
  | _ => "ordinary"
private def describeSource (result : InternalFunctionResult) : String :=
  s!"{result.success}:{result.revertData.map UInt8.toNat}:{result.exceptionalState.map (fun (s : RuntimeState) => s.executionContext.map (fun (c : Verity.Core.Model.ExecutionContext) => c.opcode.depth))}:{result.interpretationError}"
def main : IO Unit := do
  TEST
'''
    custom = '''let model : CompilationModel := { name := "m", fields := [], functions := [], constructor := none, errors := [{ name := "BadValue", params := [.uint256] }] }
  let fn : FunctionSpec := { name := "h", params := [], returnType := none, body := [.revertError "BadValue" [.literal 7]] }
  IO.println (describeSource (HelperBodyMutation.internalHelperBodyInterpretation model 4 fn Verity.defaultState 0 [] (some context)))'''
    copy = '''let model : CompilationModel := { name := "m", fields := [], functions := [], constructor := none }
  let fn : FunctionSpec := { name := "h", params := [], returnType := none, body := [.returndataCopy (.literal 0) (.literal 1) (.literal 0)] }
  IO.println (describeSource (HelperBodyMutation.internalHelperBodyInterpretation model 4 fn Verity.defaultState 0 [] (some context)))'''
    cases = [
        ('source-errors-erased', 'executionContext spec.errors externalCallOracle externalCallIndex)', 'executionContext [] externalCallOracle externalCallIndex)', custom),
        ('source-context-erased', 'executionContext := executionContext, errors := errors',
         'executionContext := none, errors := errors', copy),
        ('ir-revert-terminal-erased', '| .revert finalState =>\n      .revert (restoreCallerVars callerState finalState)',
         '| .revert finalState =>\n      .revert callerState',
         'IO.println (describeIR (HelperBodyMutation.internalHelperBodyIRExecResultAsCallResult caller helper (.revert terminal)))'),
        ('ir-exception-erased', '| .exceptional finalState =>\n      .exceptional (restoreCallerVars callerState finalState)',
         '| .exceptional finalState =>\n      .revert (restoreCallerVars callerState finalState)',
         'IO.println (describeIR (HelperBodyMutation.internalHelperBodyIRExecResultAsCallResult caller helper (.exceptional terminal)))'),
        ('ir-refusal-erased', '| .interpretationError message => .interpretationError message',
         '| .interpretationError message => .revert callerState',
         'IO.println (describeIR (HelperBodyMutation.internalHelperBodyIRExecResultAsCallResult caller helper (.interpretationError "precise refusal")))'),
    ]

    def run(label, module, text):
        path = job / (label + '.lean')
        path.write_text('import ' + module + '\n' + text)
        return command(['lake', 'env', 'lean', '--run', path], cwd=root,
                       timeout=180, log=job / (label + '.log')).splitlines()

    baseline = compile_definition('Baseline', body)
    positive = run('baseline', baseline, runtime)
    assert positive == ['Helper-body actual context, error bytes, exception and refusal checks passed', 'PASS'], positive
    rows = []
    for index, (name, old, new, test) in enumerate(cases):
        # The refusal arm also occurs in the assignment projection. Mutate the
        # first arm, in the actual body-to-call projection, deliberately.
        assert body.count(old) == (2 if name == 'ir-refusal-erased' else 1), (name, body.count(old))
        module = compile_definition('Mutant' + str(index), body.replace(old, new, 1))
        detected = run(name + '-mutant', module, runtime)
        assert len(detected) == 1 and detected[0].startswith('FAIL:'), detected
        minimal = witness.replace('TEST', test)
        expected = run(name + '-minimal-baseline', baseline, minimal)
        actual = run(name + '-minimal-mutant', module, minimal)
        replay = run(name + '-minimal-replay', module, minimal)
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append(dict(name=name, detected=detected, expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, clones=clones, rows=rows), indent=2))
    print('5 actual helper-body context mutants detected and independently replayed')


if __name__ == '__main__':
    main()
