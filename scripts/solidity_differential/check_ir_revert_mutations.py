"""Production IR revert capture/byte mutations with unchanged kernel checks."""
import argparse
import hashlib
import json
from pathlib import Path
from .engine import command, HarnessError


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.IRRevertChecks'], cwd=root,
            timeout=1800, log=job/'build.log')
    source = root/'Compiler/Proofs/IRGeneration/IRRuntimeTypes.lean'
    fixture = root/'Contracts/SolidityImportSmoke/IRRevertChecks.lean'
    raw = source.read_text().split('def IRState.captureRevert',1)[1].split('@[simp] theorem IRState.captureRevert_observed',1)[0]
    fixture_lines = fixture.read_text().splitlines()
    imports = []
    while fixture_lines and fixture_lines[0].startswith('import '):
        imports.append(fixture_lines.pop(0))
    definitions = ('\n'.join(imports) + '\n'
        'namespace Compiler.Proofs.IRGeneration\n'
        'def IRState.captureRevert' + raw + 'end Compiler.Proofs.IRGeneration\n')
    definitions = definitions.replace('IRState.captureRevert', 'IRState.mutationCapture').replace('IRState.revertBytes', 'IRState.mutationBytes')
    smoke = '\n'.join(fixture_lines).replace('.captureRevert', '.mutationCapture').replace('.revertBytes', '.mutationBytes')
    # Opcode equations keep the original opcode theorem; mutated state capture
    # must still meet its unchanged result equality.
    witness = '''open Compiler.Proofs.IRGeneration
def main : IO Unit := do
  let state := (IRState.initial 0).writePhysicalMemoryValue 0 0x0102030405
  IO.println s!"BYTES:{(state.mutationCapture 27 5).mutationBytes}"
  IO.println s!"EMPTY:{(state.mutationCapture 255 0).mutationBytes}"
  IO.println s!"ABSENT:{state.mutationBytes}"
'''
    mutants = [
        ('ir-revert-capture-offset-shifted', 'some (offset, size)', 'some (offset + 1, size)'),
        ('ir-revert-capture-size-increased', 'some (offset, size)', 'some (offset, size + 1)'),
        ('ir-revert-byte-offset-shifted', 'readByte (offset + index)', 'readByte (offset + index + 1)'),
        ('ir-revert-unobserved-as-empty', 'state.observedRevert.map (fun (offset, size) =>',
         '(state.observedRevert.orElse (fun _ => some (0, 0))).map (fun (offset, size) =>'),
    ]
    files = [source, fixture, Path(__file__).resolve(),
             root/'.lake/build/lib/lean/Compiler/Proofs/IRGeneration/IRRuntimeTypes.olean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def run(name, impl, driver):
        assert unchanged()
        path = job/f'{name}.lean'
        path.write_text(impl+driver)
        out = command(['lake', 'env', 'lean', '--run', str(path)] if driver == witness else
                      ['lake', 'env', 'lean', str(path)], cwd=root, timeout=180, log=job/f'{name}.log')
        assert unchanged()
        return out.splitlines()
    assert run('positive', definitions, smoke) == []
    rows = []
    for name, before, after in mutants:
        assert definitions.count(before) == 1
        mutant = definitions.replace(before, after)
        try:
            run(name, mutant, smoke)
        except HarnessError:
            log = (job/f'{name}.log').read_text()
            assert 'error:' in log and ('Tactic' in log or 'Type mismatch' in log or 'unsolved goals' in log), log
        else:
            raise AssertionError(f'mutation survived: {name}')
        expected = run(name+'-baseline', definitions, witness)
        actual = run(name+'-witness', mutant, witness)
        replay = run(name+'-replay', mutant, witness)
        assert expected != actual and replay == actual
        rows.append({'name': name, 'expected': expected, 'actual': actual, 'replay': replay})
        print(name, 'detected and independently replayed', flush=True)
    (job/'success.json').write_text(json.dumps({'exit':0, 'identity':identity,
        'sources_unchanged':unchanged(), 'mutants':rows}, indent=2))


if __name__ == '__main__':
    main()
