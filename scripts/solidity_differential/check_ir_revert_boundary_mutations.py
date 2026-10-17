"""Mutate actual opcode dispatch and public IR byte transport, with replay."""
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
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.IRRevertBoundaryChecks'],
            cwd=root, timeout=1800, log=job/'build.log')
    opcode = root/'Compiler/Proofs/IRGeneration/IRInterpreter.lean'
    public = root/'Compiler/Proofs/IRGeneration/FunctionBody/Stmt.lean'
    fixture = root/'Contracts/SolidityImportSmoke/IRRevertBoundaryChecks.lean'
    # Copy the actual total mutually recursive executors, preserving all arms.
    raw = opcode.read_text().split('def execIRStmt :', 1)[1].split('end -- mutual', 1)[0]
    interpreter = 'mutual\ndef execIRStmt :' + raw + 'end\n'
    converter = ('def irResultOfExecResult' + public.read_text().split(
        'def irResultOfExecResult', 1)[1].split('def irResultOfExecResultWithInternals', 1)[0])
    definitions = ('import Compiler.Proofs.IRGeneration.FunctionBody.Stmt\n'
                   'set_option linter.unusedVariables false\n'
                   'namespace IRRevertBoundaryMutation\n'
                   'open Compiler Compiler.Yul Verity.Core Compiler.Proofs\n'
                   'open Compiler.Proofs.IRGeneration\n' + interpreter + converter +
                   '\nend IRRevertBoundaryMutation\n')
    driver = '\n'.join(line for line in fixture.read_text().splitlines()
                       if not line.startswith('import '))
    driver = driver.replace('execIRStmt fuel', 'IRRevertBoundaryMutation.execIRStmt fuel')
    driver = driver.replace('FunctionBody.irResultOfExecResult',
                            'IRRevertBoundaryMutation.irResultOfExecResult')
    smoke = driver.replace(
        'def main : IO Unit := SolidityImportSmoke.IRRevertBoundaryChecks.runChecks',
        'def main : IO Unit := do\n  try\n'
        '    SolidityImportSmoke.IRRevertBoundaryChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = driver.split('def main : IO Unit', 1)[0] + '''
def main : IO Unit := do
  for (offset, size, fuel) in [(27, 5, 1), (30, 5, 1), (255, 0, 1), (27, 5, 0)] do
    IO.println s!"BYTES:{SolidityImportSmoke.IRRevertBoundaryChecks.probe offset size fuel}"
'''
    mutants = [
        ('ir-revert-opcode-erases-capture', '.revert (state.captureRevert offset size)',
         '.revert state'),
        ('ir-revert-opcode-ignores-offset', '.revert (state.captureRevert offset size)',
         '.revert (state.captureRevert 0 size)'),
        ('public-ir-erases-revert-bytes', 'revertData := state.revertBytes',
         'revertData := none'),
    ]
    files = [opcode, public, fixture, Path(__file__).resolve(),
             root/'.lake/build/lib/lean/Compiler/Proofs/IRGeneration/IRInterpreter.olean',
             root/'.lake/build/lib/lean/Compiler/Proofs/IRGeneration/FunctionBody/Stmt.olean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in files}

    def run(name, implementation, test):
        assert unchanged()
        path = job/f'{name}.lean'
        path.write_text(implementation + test)
        output = command(['lake', 'env', 'lean', '--run', str(path)],
                         cwd=root, timeout=180, log=job/f'{name}.log').splitlines()
        assert unchanged()
        return output

    assert run('positive', definitions, smoke) == ['PASS']
    rows = []
    for name, before, after in mutants:
        assert definitions.count(before) == 1
        mutant = definitions.replace(before, after)
        failed = run(name, mutant, smoke)
        assert len(failed) == 1 and failed[0].startswith('FAIL:'), failed
        expected = run(name+'-baseline', definitions, witness)
        actual = run(name+'-witness', mutant, witness)
        replay = run(name+'-replay', mutant, witness)
        assert len(expected) == len(actual) == 4 and expected != actual and actual == replay
        rows.append({'name': name, 'expected': expected, 'actual': actual, 'replay': replay})
        print(name, 'detected and independently replayed', flush=True)
    (job/'success.json').write_text(json.dumps({'exit': 0, 'identity': identity,
        'sources_unchanged': unchanged(), 'mutants': rows}, indent=2))


if __name__ == '__main__':
    main()
