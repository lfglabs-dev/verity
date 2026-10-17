"""Detect bypasses of the actual native caller's static-write and SSTORE stipend gates."""
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
    source = root / 'Compiler/Proofs/IRGeneration/CreationCaller.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/NativeCreationWorldChecks.lean'
    files = [fixture, source, Path(__file__).resolve(), root / 'lake-manifest.json', root / 'lakefile.lean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.NativeCreationWorldChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    body = 'def checkedStep' + source.read_text().split('def checkedStep', 1)[1].split('\n/-- Fuel', 1)[0]
    prefix = ('import Compiler.Proofs.IRGeneration.NativeCreationWorld\n'
              'namespace NativeCallerWorldGateMutation\n'
              'open EvmYul Compiler.Proofs.IRGeneration.CreationCaller\n')
    def definitions(implementation):
        return prefix + implementation + '\nend NativeCallerWorldGateMutation\n'
    runtime = '\nnamespace ' + fixture.read_text().split('\nnamespace ', 1)[1]
    runtime = runtime.replace('Compiler.Proofs.IRGeneration.CreationCaller.checkedStep',
                              'NativeCallerWorldGateMutation.checkedStep')
    marker = 'def main : IO Unit := SolidityImportSmoke.NativeCreationWorldChecks.runChecks'
    assert runtime.count(marker) == 1
    runtime = runtime.replace(marker,
        'def main : IO Unit := do\n  try\n'
        '    SolidityImportSmoke.NativeCreationWorldChecks.runChecks\n'
        '    IO.println "NATIVE_GATE_PASS"\n'
        '  catch error => IO.println s!"NATIVE_GATE_FAIL:{error}"')
    # Keep the same real entry state, execute one checked opcode, observe its control/gas.
    witness_prefix = runtime.split('private def expectStaticFailure', 1)[0]
    cases = [
        ('static-write-bypass', 'if !expanded.executionEnv.perm && decide (op ∈',
         'if false && decide (op ∈', 'entry 0x55 9994 true'),
        ('sstore-stipend-off-by-one', 'expanded.gasAvailable.toNat ≤ GasConstants.Gcallstipend',
         'expanded.gasAvailable.toNat < GasConstants.Gcallstipend', 'entry 0x55 2300 false'),
    ]
    def run(name, implementation, test):
        path = job / (name + '.lean')
        path.write_text(definitions(implementation) + test)
        return command(['lake', 'env', 'lean', '--run', str(path)], cwd=root,
                       timeout=180, log=job / (name + '.log')).splitlines()
    baseline = run('baseline', body, runtime)
    assert baseline == ['native exceptional component reference checks passed:5',
                        'native creation account/presence/storage/access view checks passed', 'NATIVE_GATE_PASS']
    rows = []
    for name, before, after, entry in cases:
        assert body.count(before) == 1, name
        mutant = body.replace(before, after, 1)
        detected = run(name + '-mutant', mutant, runtime)
        failures = [line for line in detected if line.startswith('NATIVE_GATE_FAIL:')]
        assert len(failures) == 1 and 'NATIVE_GATE_PASS' not in detected, detected
        witness = (witness_prefix + '\ndef witness : IO Unit := do\n'
            + f'  match NativeCallerWorldGateMutation.checkedStep ({entry}) .SSTORE none with\n'
            + '  | .error .StaticModeViolation => IO.println "WITNESS:static"\n'
            + '  | .error .OutOfGass => IO.println "WITNESS:gas"\n'
            + '  | .error _ => IO.println "WITNESS:other-error"\n'
            + '  | .ok state => IO.println s!"WITNESS:ok:{state.gasAvailable.toNat}"\n'
            + 'end SolidityImportSmoke.NativeCreationWorldChecks\n'
            + 'def main : IO Unit := SolidityImportSmoke.NativeCreationWorldChecks.witness\n')
        expected = run(name + '-minimal-baseline', body, witness)
        actual = run(name + '-minimal-mutant', mutant, witness)
        replay = run(name + '-minimal-replay', mutant, witness)
        expected = [line for line in expected if line.startswith('WITNESS:')]
        actual = [line for line in actual if line.startswith('WITNESS:')]
        replay = [line for line in replay if line.startswith('WITNESS:')]
        assert len(expected) == len(actual) == len(replay) == 1
        assert expected != actual and actual == replay
        rows.append(dict(name=name, detected=failures, expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2)+'\n')
    print('2 native caller world gates mutated and independently replayed')


if __name__ == '__main__':
    main()
