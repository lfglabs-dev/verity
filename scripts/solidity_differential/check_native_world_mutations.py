"""Mutate actual native-world views; require compiled runtime failures and minimal replays."""
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
    source = root / 'Compiler/Proofs/IRGeneration/NativeCreationWorld.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/NativeCreationWorldChecks.lean'
    files = [fixture, Path(__file__).resolve(), root / 'lake-manifest.json',
             root / 'lakefile.lean', root / 'scripts/solidity_differential/engine.py']
    for directory in ('Compiler', 'Verity', '.lake/packages/evmyul/EvmYul'):
        files.extend(sorted((root / directory).rglob('*.lean')))
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.NativeCreationWorldChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    original = source.read_text()
    original_namespace = 'Compiler.Proofs.IRGeneration.NativeCreationWorld'
    namespace = 'NativeCreationWorldMutation'
    implementation = original.replace('namespace ' + original_namespace, 'namespace ' + namespace)
    implementation = implementation.replace('end ' + original_namespace, 'end ' + namespace)
    runtime = fixture.read_text().split('\nnamespace ', 1)[1]
    runtime = '\nnamespace ' + runtime
    runtime = runtime.replace('open EvmYul ' + original_namespace, 'open EvmYul ' + namespace)
    old_main = 'def main : IO Unit := SolidityImportSmoke.NativeCreationWorldChecks.runChecks'
    assert runtime.count(old_main) == 1
    runtime = runtime.replace(old_main,
        'def main : IO Unit := do\n  try\n'
        '    SolidityImportSmoke.NativeCreationWorldChecks.runChecks\n'
        '    IO.println "NATIVE_WORLD_PASS"\n'
        '  catch error => IO.println s!"NATIVE_WORLD_FAIL:{error}"')
    witness_prefix = runtime.split('/-- Entry states', 1)[0]
    cases = [
        ('erase-logs', 'machine.substate.logSeries', '#[]', '(rawLogs native).size'),
        ('erase-presence', 'machine.accountMap.get? owner',
         'some ((machine.accountMap.get? owner).getD default)', '(account? native missing).isSome'),
        ('erase-nonce', 'nonce := (account machine owner).nonce.toNat', 'nonce := 0',
         '(creationAccount native owner).nonce'),
        ('erase-balance', 'balance := Verity.Core.Uint256.ofNat (account machine owner).balance.toNat',
         'balance := Verity.Core.Uint256.ofNat 0', '(creationAccount native owner).balance.val'),
        ('conflate-transient', '(account machine owner).tstorage.getD slot',
         '(account machine owner).storage.getD slot', '(transientWord native owner (.ofNat 7)).val'),
        ('conflate-original', 'let original := (machine.σ₀.get? owner).getD default',
         'let original := (machine.accountMap.get? owner).getD default',
         '(originalPersistentWord native owner (.ofNat 7)).val'),
        ('conflate-slot-warmth', 'machine.substate.accessedStorageKeys.contains (owner, slot)',
         'machine.substate.accessedAccounts.contains owner', 'storageWarm native owner (.ofNat 8)'),
    ]
    def run(name, definitions, test):
        path = job / (name + '.lean')
        path.write_text(definitions + test)
        return command(['lake', 'env', 'lean', '--run', str(path)], cwd=root,
                       timeout=180, log=job / (name + '.log')).splitlines()
    baseline = run('baseline', implementation, runtime)
    assert baseline == ['native exceptional component reference checks passed:5',
                        'native creation account/presence/storage/access view checks passed',
                        'NATIVE_WORLD_PASS'], baseline
    rows = []
    for name, before, after, expression in cases:
        assert implementation.count(before) == 1, name
        mutant = implementation.replace(before, after, 1)
        detected = run(name + '-mutant', mutant, runtime)
        failure = [line for line in detected if line.startswith('NATIVE_WORLD_FAIL:')]
        assert len(failure) == 1 and 'NATIVE_WORLD_PASS' not in detected, detected
        witness = (witness_prefix + '\ndef witness : IO Unit := do\n'
                   + f'  IO.println s!"WITNESS:{{{expression}}}"\n'
                   + 'end SolidityImportSmoke.NativeCreationWorldChecks\n'
                   + 'def main : IO Unit := SolidityImportSmoke.NativeCreationWorldChecks.witness\n')
        expected = run(name + '-minimal-baseline', implementation, witness)
        actual = run(name + '-minimal-mutant', mutant, witness)
        replay = run(name + '-minimal-replay', mutant, witness)
        # Generated mutant definitions may warn about their now-unused parameters.
        # The command must still compile and exit0 before a witness is considered.
        expected = [line for line in expected if line.startswith('WITNESS:')]
        actual = [line for line in actual if line.startswith('WITNESS:')]
        replay = [line for line in replay if line.startswith('WITNESS:')]
        assert len(expected) == len(actual) == len(replay) == 1
        assert expected != actual and actual == replay
        rows.append(dict(name=name, detected=failure, expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2)+'\n')
    print('7 native-world view mutants detected and independently replayed')


if __name__ == '__main__':
    main()
