"""Mutate actual typed Source CREATE2 consumption against native preparation.

Component controls, not imported whole-function A/B/C admission.
"""
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
    fixture = root/'Contracts/SolidityImportSmoke/NativePreparedCreationChecks.lean'
    source = root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.NativePreparedCreationChecks',
             '@evmyul/+EvmYul.FFI.ffi:dynlib'], cwd=root, timeout=1800, log=job/'build.log')
    extern = root/'.lake/packages/evmyul/.lake/build/lib/libleanffi.so'
    wrapper = root/'.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so'
    definitions = source.read_text().split('theorem consume_refusal', 1)[0] + '\nend Compiler.Proofs.IRGeneration.SourceStatementEvaluation\n'
    definitions = definitions.replace('SourceStatementEvaluation', 'SourceStatementEvaluationMutation')
    driver = '\n'.join(line for line in fixture.read_text().splitlines() if not line.startswith('import '))
    driver = driver.replace('SourceStatementEvaluation', 'SourceStatementEvaluationMutation')
    imports = 'import Compiler.Proofs.IRGeneration.NativeCreationBoundary\nimport Compiler.Proofs.IRGeneration.DenoteTypedCreationAgreement\n'
    smoke = driver.replace('def main : IO Unit := SolidityImportSmoke.NativePreparedCreationChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.NativePreparedCreationChecks.runChecks\n    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    minimal = driver.split('def runChecks', 1)[0] + '''def witness : IO Unit := do
  let model : Compiler.CompilationModel.CompilationModel :=
    { name := "Minimal", fields := [], functions := [], constructor := none }
  let initial : SourceSemantics.RuntimeState := { world := world, bindings := [] }
  let prepared ← match SourceStatementEvaluationMutation.execStmt model [] 32 initial
      (.mstore (.literal 0) (.literal constructorWord)) with
    | .continue state => pure state
    | _ => throw (IO.userError "preparation refused")
  let entry ← match ← IO.ofExcept (CreationCaller.run 64 before.machine) with
    | .ready machine => pure machine
    | _ => throw (IO.userError "native prefix refused")
  let ready := { prepared with executionContext := some (CreationCaller.context entry before.warm) }
  match SourceStatementEvaluationMutation.execStmt model [] 32 ready
      (.create2 "created" (.literal 0) (.literal 11) (.literal 7)) with
  | .continue state => IO.println s!"ADDRESS:{SourceSemantics.lookupValue state.bindings "created"}"
  | _ => throw (IO.userError "creation refused")
end SolidityImportSmoke.NativePreparedCreationChecks
def main : IO Unit := SolidityImportSmoke.NativePreparedCreationChecks.witness
'''
    inputs = [source, fixture, extern, wrapper, Path(__file__).resolve(),
              root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/NativeCreationBoundary.lean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    def run(name, implementation, test):
        assert unchanged()
        path = job/(name+'.lean')
        path.write_text(imports+implementation+test)
        output = command(['lake', 'env', 'lean', f'--load-dynlib={extern}',
                          f'--load-dynlib={wrapper}', '--run', str(path)],
                         cwd=root, timeout=1800, log=job/(name+'.log'))
        assert unchanged()
        return output.splitlines()
    baseline = run('baseline', definitions, smoke)
    assert len(baseline) == 4 and baseline[-1] == 'PASS' and baseline[0].startswith('ADDRESS:')
    before = '(.literal resolvedSize) (.literal resolvedSalt)'
    after = '(.literal resolvedSize) (.literal (resolvedSalt + 1))'
    assert definitions.count(before) == 1
    mutant = definitions.replace(before, after)
    failed = run('typed-create2-salt-corrupted', mutant, smoke)
    assert len(failed) == 1 and failed[0].startswith('FAIL:'), failed
    expected = run('minimal-baseline', definitions, minimal)
    actual = run('minimal-mutant', mutant, minimal)
    replay = run('minimal-replay', mutant, minimal)
    assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
    (job/'success.json').write_text(json.dumps({'exit': 0, 'sources_unchanged': unchanged(),
        'identity': identity, 'mutants': [{'name': 'typed-create2-salt-corrupted',
        'baseline': expected, 'actual': actual, 'replay': replay, 'smoke': failed}],
        'scope': 'Typed Source CREATE2 salt consumer only; not whole-function/compiler admission'}, indent=2))
    print('typed CREATE2 salt mutation detected and independently replayed')


if __name__ == '__main__':
    main()
