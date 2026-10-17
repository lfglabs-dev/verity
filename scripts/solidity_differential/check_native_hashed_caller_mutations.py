"""Execute hash-aware caller mutants without allowing proof failures as detection."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SUCCESS = 'HASHED_CREATION_SUCCESS: 16 storage/creation/native-iterator comparisons; 5 refusals\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / 'Compiler/Proofs/IRGeneration/NativeHashedWorldCaller.lean'
    fixture = ROOT / 'Contracts/SolidityImportSmoke/NativeHashedCallerChecks.lean'
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [source, fixture, Path(__file__)]}
    # Only executable definitions are mutated, leaving imported dependencies
    # intact. Detection must come from the runtime assertions, never elaboration.
    text = source.read_text()
    namespace = 'namespace Compiler.Proofs.IRGeneration.NativeHashedWorldCaller'
    start = text.index(namespace)
    end = text.index('/-- The extension delegates', start)
    prefix = ('import Compiler.Proofs.IRGeneration.NativeMappingStorageExecution\n'
              + text[start:end] + '\nend Compiler.Proofs.IRGeneration.NativeHashedWorldCaller\n')
    body = fixture.read_text().split('\n', 1)[1] + '\ndef main : IO Unit := SolidityImportSmoke.NativeHashedCallerChecks.runChecks\n'
    baseline = prefix + body
    mutations = {
        'zero-hash': ('machine := next })',
                     'machine := { next with stack := UInt256.ofNat 0 :: next.stack.drop 1 } })'),
        'skip-hash-step': ('machine := next })', 'machine := before.machine })'),
        'stale-world': ('else NativeCreationWorldCaller.advance before op arg',
                       'else do\n    match ← NativeCreationWorldCaller.advance before op arg with\n'
                       '    | .continued next => pure (.continued { next with world := before.world })\n'
                       '    | .exceptional reason frame => pure (.exceptional reason frame)')}
    lean = (str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean')
            if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' and os.environ.get('LEAN_SYSROOT') else 'lean')
    command = ['lake', 'env', lean,
               '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
               '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so', '--run']

    def execute(name, content):
        path = output / (name + '.lean')
        path.write_text(content)
        run = subprocess.run(command + [str(path)], cwd=ROOT, capture_output=True, text=True, timeout=180)
        (output / (name + '.log')).write_text(run.stdout + run.stderr)
        return run

    control = execute('baseline', baseline)
    assert control.returncode == 0 and control.stdout == SUCCESS and not control.stderr, control
    rows = []
    for name, (old, new) in mutations.items():
        assert baseline.count(old) == 1, name
        content = baseline.replace(old, new)
        first = execute(name, content)
        replay = execute(name + '-replay', content)
        for run in [first, replay]:
            combined = run.stdout + run.stderr
            assert run.returncode != 0 and 'uncaught exception: hash prefix' in combined, combined
            assert not re.search(r'(^|\n).*\berror:', combined), combined
        failure = lambda run: [line for line in (run.stdout + run.stderr).splitlines()
                               if line.startswith('uncaught exception:')]
        assert failure(first) == failure(replay)
        rows.append({'name': name, 'detected': failure(first), 'replay': failure(replay),
                     'sourceSha256': hashlib.sha256(content.encode()).hexdigest()})
    assert hashes == {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in hashes}
    (output / 'success.json').write_text(json.dumps({'exit': 0, 'sourceHashes': hashes, 'rows': rows}, indent=2) + '\n')
    print('pass hashed native caller mutations:3 semantic detections and replays')


if __name__ == '__main__':
    main()
