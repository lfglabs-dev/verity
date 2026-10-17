"""Mutate actual paired caller effects; require runtime detection and one-step replays."""
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
    source = root / 'Compiler/Proofs/IRGeneration/NativeCreationWorldCaller.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/NativePairedCallerChecks.lean'
    files = [source, fixture, Path(__file__).resolve(), root / 'lakefile.lean', root / 'lake-manifest.json']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    production = 'Compiler.Proofs.IRGeneration.NativeCreationWorldCaller'
    body = source.read_text().split('\nprivate theorem sstore_arg', 1)[0]
    body = body.replace('namespace ' + production, 'namespace NativePairedCallerMutation\nopen Compiler.Proofs.IRGeneration')
    body += '\nend NativePairedCallerMutation\n'
    runtime = '\nnamespace ' + fixture.read_text().split('\nnamespace ', 1)[1]
    runtime = runtime.replace('open ' + production, 'open NativePairedCallerMutation')
    marker = 'def main : IO Unit := SolidityImportSmoke.NativePairedCallerChecks.runChecks'
    assert runtime.count(marker) == 1
    runtime = runtime.replace(marker, 'def main : IO Unit := do\n  try\n'
        '    SolidityImportSmoke.NativePairedCallerChecks.runChecks\n'
        '    IO.println "PAIRED_PASS"\n'
        '  catch error => IO.println s!"PAIRED_FAIL:{error}"')
    witness_prefix = runtime.split('/-- Saved real-EVM', 1)[0]
    cases = [
        ('erase-persistent-update',
         'before.world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)',
         'before.world', '.SSTORE', False, False),
        ('conflate-transient-channel', 'before.world.writeTransient slot.toNat',
         'before.world.writeSlot slot.toNat', '.TSTORE', False, False),
        ('bypass-account-presence',
         'if (before.machine.toState.lookupAccount before.machine.executionEnv.codeOwner).isNone then',
         'if false then', '.TSTORE', True, False),
        ('erase-advance-world', 'world := world, machine := next',
         'world := before.world, machine := next', '.SSTORE', False, False),
        ('erase-run-world', '| .continued next => run fuel next',
         '| .continued next => run fuel { next with world := before.world }', '.SSTORE', False, True),
    ]
    libraries = [root / '.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
                 root / '.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so']
    def run(name, implementation, test):
        path = job / (name + '.lean')
        path.write_text(implementation + test)
        return command(['lake', 'env', 'lean', *['--load-dynlib=' + str(p) for p in libraries],
                        '--run', str(path)], cwd=root, timeout=180,
                       log=job / (name + '.log')).splitlines()
    baseline = run('baseline', body, runtime)
    assert baseline == ['paired native/canonical prefix reference checks passed', 'PAIRED_PASS'], baseline
    rows = []
    for name, old, new, opcode, absent, prefix_run in cases:
        assert body.count(old) == 1, name
        mutant = body.replace(old, new, 1)
        detected = run(name + '-mutant', mutant, runtime)
        failures = [line for line in detected if line.startswith('PAIRED_FAIL:')]
        assert len(failures) == 1 and 'PAIRED_PASS' not in detected, detected
        if prefix_run:
            invocation = ('  let before := initial ⟨#[0x60,0x63,0x60,0x07,0x55,0xf5]⟩ 10000 []\n'
                '  let outcome := match run 4 before with\n'
                '    | .ok (.ready after) => Except.ok after\n'
                '    | .ok (.exceptional _ _) => Except.error "exception"\n'
                '    | .error _ => Except.error "refusal"\n')
        else:
            invocation = ('  let start := initial ⟨#[0x55,0x00]⟩ 10000 [.ofNat 7, .ofNat 99]\n'
                + ('  let before := { start with machine := { start.machine with accountMap := Inhabited.default } }\n'
                   if absent else '  let before := start\n')
                + f'  let outcome := match advance before {opcode} none with\n'
                '    | .ok (.continued after) => Except.ok after\n'
                '    | .ok (.exceptional _ _) => Except.error "exception"\n'
                '    | .error _ => Except.error "refusal"\n')
        witness = (witness_prefix + '\ndef witness : IO Unit := do\n' + invocation
            + '  match outcome with\n'
            '  | .error reason => IO.println s!"WITNESS:{reason}"\n'
            '  | .ok after =>\n'
            '      IO.println s!"WITNESS:{(after.world.readSlot 7).val}:{(after.world.transientStorage 7).val}:{(persistentWord after.machine owner (.ofNat 7)).val}:{(transientWord after.machine owner (.ofNat 7)).val}"\n'
            'end SolidityImportSmoke.NativePairedCallerChecks\n'
            'def main : IO Unit := SolidityImportSmoke.NativePairedCallerChecks.witness\n')
        expected = run(name + '-minimal-baseline', body, witness)
        actual = run(name + '-minimal-mutant', mutant, witness)
        replay = run(name + '-minimal-replay', mutant, witness)
        # Compiled mutants can introduce unused-variable warnings. Preserve the
        # complete diagnostics in logs; compare the tagged semantic observations.
        expected = [line for line in expected if line.startswith('WITNESS:')]
        actual = [line for line in actual if line.startswith('WITNESS:')]
        replay = [line for line in replay if line.startswith('WITNESS:')]
        assert len(expected) == len(actual) == len(replay) == 1
        assert expected != actual and actual == replay
        rows.append(dict(name=name, detected=failures, expected=expected, actual=actual, replay=replay))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2) + '\n')
    print('5 paired caller world mutants detected and independently replayed')


if __name__ == '__main__':
    main()
