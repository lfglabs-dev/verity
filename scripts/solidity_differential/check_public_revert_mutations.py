"""Mutate the actual public Denote byte transport, preserving its fixture."""
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
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.PublicRevertChecks'],
            cwd=root, timeout=1800, log=job/'build.log')
    source = root/'Verity/Core/Model/Denote.lean'
    fixture = root/'Contracts/SolidityImportSmoke/PublicRevertChecks.lean'
    body = 'def denoteFunction' + source.read_text().split('def denoteFunction', 1)[1].split('/-! ## Smoke checks', 1)[0]
    definitions = ('import Compiler.Proofs.IRGeneration.DenoteFunctionAgreement\n'
                   'namespace PublicDenoteMutation\n'
                   'open Compiler.CompilationModel Compiler.CompilationModel.Denote\n'
                   + body + '\nend PublicDenoteMutation\n')
    driver = '\n'.join(line for line in fixture.read_text().splitlines() if not line.startswith('import '))
    driver = driver.replace('Denote.denoteFunction', 'PublicDenoteMutation.denoteFunction')
    smoke = driver.replace('def main : IO Unit := SolidityImportSmoke.PublicRevertChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.PublicRevertChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''open Compiler.CompilationModel Compiler.Proofs.IRGeneration
def main : IO Unit := do
  let fn : FunctionSpec := { name := "probe", params := [], returnType := none, body := [.require (.literal 0) "denied"] }
  let model : CompilationModel := { name := "PublicRevert", constructor := none, fields := [], functions := [fn] }
  let result := PublicDenoteMutation.denoteFunction DenoteAgreement.sourceOracle model fn
    { sender := 0, functionSelector := 0, args := [] } Verity.defaultState
  IO.println s!"BYTES:{result.revertData}"
'''
    before = '| .revertWithData data => { revertedResult oracle spec worldWithTx with revertData := data }'
    after = '| .revertWithData data => { revertedResult oracle spec worldWithTx with revertData := if data.isEmpty then [] else [] }'
    assert definitions.count(before) == 1
    mutant = definitions.replace(before, after)
    files = [source, fixture, Path(__file__).resolve(),
             root/'.lake/build/lib/lean/Verity/Core/Model/Denote.olean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def run(name, implementation, test):
        assert unchanged()
        path = job/f'{name}.lean'
        path.write_text(implementation + test)
        output = command(['lake', 'env', 'lean', '--run', str(path)],
                         cwd=root, timeout=180, log=job/f'{name}.log').splitlines()
        assert unchanged()
        return output
    assert run('positive', definitions, smoke) == ['public entry revert bytes and rollback passed', 'PASS']
    failed = run('public-denote-erases-revert-bytes', mutant, smoke)
    assert len(failed) == 1 and failed[0].startswith('FAIL:'), failed
    expected = run('baseline', definitions, witness)
    actual = run('witness', mutant, witness)
    replay = run('replay', mutant, witness)
    assert len(expected) == len(actual) == 1 and expected != actual and replay == actual
    (job/'success.json').write_text(json.dumps({'exit': 0, 'identity': identity,
        'sources_unchanged': unchanged(), 'mutants': [{'name': 'public-denote-erases-revert-bytes',
        'expected': expected, 'actual': actual, 'replay': replay, 'smoke': failed}]}, indent=2))
    print('public Denote byte erasure detected and independently replayed')


if __name__ == '__main__':
    main()
