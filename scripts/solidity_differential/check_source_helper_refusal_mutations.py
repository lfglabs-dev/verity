"""Executable mutation for Source's failed internal-call outcome projection."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=root / '.lake/source-helper-refusal-mutations')
    args = parser.parse_args()
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.SourceSemantics',
             'Contracts.SolidityImportSmoke.SourceHelperRefusal'], cwd=root,
            timeout=1800, log=job / 'build.log')
    source = root / 'Compiler/Proofs/IRGeneration/SourceSemantics.lean'
    fixture_path = root / 'Contracts/SolidityImportSmoke/SourceHelperRefusal.lean'
    original = source.read_text()
    body = original.split('def failedInternalOutcome', 1)[1].split('theorem failedInternalOutcome_error', 1)[0]
    prefix = ('import Compiler.Proofs.IRGeneration.SourceSemantics\n'
              'open Compiler.Proofs.IRGeneration.SourceSemantics\n'
              'namespace SourceHelperMutation\ndef failedInternalOutcome' + body +
              '\nend SourceHelperMutation\n')
    old = '| some message => .interpretationError message'
    new = '| some message => if message.length = 0 then .revert else .revert'
    assert prefix.count(old) == 1
    mutated = prefix.replace(old, new)
    fixture = '\n'.join(line for line in fixture_path.read_text().splitlines()
                        if not line.startswith('import '))
    fixture = fixture.replace('failedInternalOutcome', 'SourceHelperMutation.failedInternalOutcome')
    fixture = fixture.replace('def main : IO Unit := SolidityImportSmoke.SourceHelperRefusal.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourceHelperRefusal.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    witness = '''def main : IO Unit := do
      match SourceHelperMutation.failedInternalOutcome
          { interpretationError := some "refusal", success := false,
            returnValue := none, world := Verity.defaultState } with
      | .interpretationError message => IO.println s!"error:{message}"
      | .revert => IO.println "revert"
      | _ => IO.println "other"
    '''
    files = [source, fixture_path, Path(__file__).resolve(),
             root / '.lake/build/lib/lean/Compiler/Proofs/IRGeneration/SourceSemantics.olean']
    manifest = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    lean = (str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean')
            if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' and os.environ.get('LEAN_SYSROOT')
            else 'lean')

    def unchanged():
        return all(hashlib.sha256((root / p).read_bytes()).hexdigest() == h for p, h in manifest.items())

    def run(name, definitions, test):
        assert unchanged()
        driver = job / (name + '.lean')
        driver.write_text(definitions + test)
        with (job / (name + '.log')).open('w') as log:
            result = subprocess.run(['lake', 'env', lean, '--run', str(driver)], cwd=root,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=180)
        lines = (job / (name + '.log')).read_text().splitlines()
        assert result.returncode == 0 and unchanged(), (name, result.returncode, lines)
        return lines

    assert run('positive', prefix, fixture) == ['Source helper statement refusals preserved', 'PASS']
    smoke = run('mutated-smoke', mutated, fixture)
    assert len(smoke) == 1 and smoke[0].startswith('FAIL:'), smoke
    expected = run('minimal-baseline', prefix, witness)
    actual = run('minimal-mutant', mutated, witness)
    replay = run('minimal-replay', mutated, witness)
    assert expected == ['error:refusal'] and actual == replay == ['revert']
    receipt = {'sources': manifest, 'sources_unchanged': unchanged(), 'mutants': [
        {'name': 'source-helper-refusal-becomes-revert', 'expected': expected, 'actual': actual,
         'replayed': actual == replay, 'minimal': 'one failed internal outcome', 'smoke': smoke}],
        'scope': 'failed internal outcome projection; not expression helper or native context agreement'}
    (job / 'success.json').write_text(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
