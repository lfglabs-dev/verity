"""Mutate actual paired prefix-to-CREATE2 delegation and replay reduced witnesses."""
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
    source = root / 'Compiler/Proofs/IRGeneration/NativeCreationWorldExecution.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/NativePairedCreationChecks.lean'
    files = [source, fixture, Path(__file__).resolve(), root / 'lakefile.lean', root / 'lake-manifest.json']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    production = 'Compiler.Proofs.IRGeneration.NativeCreationWorldExecution'
    body = source.read_text().split('\n/-- Reaching CREATE2', 1)[0]
    body = body.replace('namespace ' + production,
        'namespace NativePairedCreationMutation\nopen Compiler.Proofs.IRGeneration')
    body += '\nend NativePairedCreationMutation\n'
    runtime = '\nnamespace ' + fixture.read_text().split('\nnamespace ', 1)[1]
    runtime = runtime.replace(production + '.run', 'NativePairedCreationMutation.run')
    marker = 'def main : IO Unit := SolidityImportSmoke.NativePairedCreationChecks.runChecks'
    assert runtime.count(marker) == 1
    runtime = runtime.replace(marker, 'def main : IO Unit := do\n  try\n'
        '    SolidityImportSmoke.NativePairedCreationChecks.runChecks\n'
        '    IO.println "PAIRED_CREATION_PASS"\n'
        '  catch error => IO.println s!"PAIRED_CREATION_FAIL:{error}"')
    witness_prefix = runtime.split('/-- Saved real-EVM', 1)[0]
    cases = [
        ('stale-boundary-world', '| .ready frame => CreationBytecode.execReady frame',
         '| .ready frame => CreationBytecode.execReady { frame with world := before.world }', False),
        ('stale-boundary-machine', '| .ready frame => CreationBytecode.execReady frame',
         '| .ready frame => CreationBytecode.execReady { frame with machine := before.machine }', False),
        ('erase-exceptional-prefix', '| .exceptional _ frame => pure (.exceptional frame)',
         '| .exceptional _ _ => pure (.exceptional before)', True),
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
    assert baseline == ['paired prefix through CREATE2 reference checks passed', 'PAIRED_CREATION_PASS'], baseline
    rows = []
    for name, old, new, exceptional in cases:
        assert body.count(old) == 1, name
        mutant = body.replace(old, new, 1)
        detected = run(name + '-mutant', mutant, runtime)
        failures = [line for line in detected if line.startswith('PAIRED_CREATION_FAIL:')]
        assert len(failures) == 1 and 'PAIRED_CREATION_PASS' not in detected, detected
        # Reduced inputs: a single SSTORE followed by CREATE2 with independently
        # initialized supported header memory, or SSTORE followed by underflow.
        invocation = ('  let before := initial ⟨#[0x60,0x63,0x60,0x07,0x55,0x55]⟩ 100000 []\n'
            if exceptional else
            '  let start := initial ⟨#[0x55,0xf5]⟩ 100000 [.ofNat 7,.ofNat 99,.ofNat 0,.ofNat 0,.ofNat 11,.ofNat 7]\n'
            '  let before := { start with machine := { start.machine with activeWords := .ofNat 1, memory := ⟨#[0x60,0x0b,0x38,0x03,0x80,0x60,0x0b,0x5f,0x39,0x5f,0xf3]⟩ } }\n')
        witness = (witness_prefix + '\ndef witness : IO Unit := do\n'
            + invocation
            + '  match NativePairedCreationMutation.run 10 before with\n'
            '  | .error _ => IO.println "WITNESS:refusal"\n'
            '  | .ok outcome =>\n'
            '      let (tag, after) := match outcome with\n'
            '        | .continued frame => ("continued", frame)\n'
            '        | .exceptional frame => ("exceptional", frame)\n'
            '      IO.println s!"WITNESS:{tag}:{(after.world.readSlot 7).val}:{after.machine.pc.toNat}:{after.machine.gasAvailable.toNat}"\n'
            'end SolidityImportSmoke.NativePairedCreationChecks\n'
            'def main : IO Unit := SolidityImportSmoke.NativePairedCreationChecks.witness\n')
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
    (job / 'success.json').write_text(json.dumps(dict(exit=0, identity=identity, rows=rows), indent=2) + '\n')
    print('3 paired creation delegation mutants detected and independently replayed')


if __name__ == '__main__':
    main()
