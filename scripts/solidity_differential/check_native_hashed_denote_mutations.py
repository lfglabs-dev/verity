"""Execute actual Denote boundary projection mutants without allowing proof failures as detection."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SUCCESS = 'HASHED_DENOTE_SUCCESS: 16 storage/creation/native-iterator comparisons; 37 refusals\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / 'Compiler/Proofs/IRGeneration/NativeHashedDenote.lean'
    fixture = ROOT / 'Contracts/SolidityImportSmoke/NativeHashedDenoteChecks.lean'
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [source, fixture, Path(__file__)]}
    # Only executable definitions are mutated, leaving imported dependencies
    # intact. Detection must come from the runtime assertions, never elaboration.
    text = source.read_text()
    namespace = 'namespace Compiler.Proofs.IRGeneration.NativeHashedDenote'
    start = text.index(namespace)
    end = text.index('/-- Same computed operation result', start)
    prefix = ('import Compiler.Proofs.IRGeneration.NativeHashedWorldCaller\nimport Verity.Core.Model.Denote\n'
              + text[start:end] + '\nend Compiler.Proofs.IRGeneration.NativeHashedDenote\n')
    body = fixture.read_text().split('\n', 1)[1] + '\ndef main : IO Unit := SolidityImportSmoke.NativeHashedDenoteChecks.runChecks\n'
    baseline = prefix + body
    mutations = {
        'stale-world': ('world := (CreationBytecode.atBoundary frame).world', 'world := state.world'),
        'stale-context': ('executionContext := some (CreationCaller.context frame.machine frame.warm)',
                          'executionContext := state.executionContext'),
        'erase-bindings': ('{ state with\n', '{ state with\n    bindings := []\n')}
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
            assert run.returncode != 0 and 'uncaught exception: denote' in combined, combined
            assert not re.search(r'(^|\n).*\berror:', combined), combined
        failure = lambda run: [line for line in (run.stdout + run.stderr).splitlines()
                               if line.startswith('uncaught exception:')]
        assert failure(first) == failure(replay)
        rows.append({'name': name, 'detected': failure(first), 'replay': failure(replay),
                     'sourceSha256': hashlib.sha256(content.encode()).hexdigest()})
    assert hashes == {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in hashes}
    (output / 'success.json').write_text(json.dumps({'exit': 0, 'sourceHashes': hashes, 'rows': rows}, indent=2) + '\n')
    print('pass hashed Denote mutations:3 semantic detections and replays')


if __name__ == '__main__':
    main()
