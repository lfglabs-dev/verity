"""Located rejections and positive controls for storage access after a re-entrant CALL.

A callee may call the contract back, so the importer admits a typed void call only as the
function's last state interaction. The positive controls are the shapes
`check_reentrant_callback.py` runs on three routes: state written before the call, then
nothing, or only local computation, after it. Every near miss reads or writes storage, logs,
or calls again after the call (directly, or in a `try` clause) and must still fail at the
function definition with the exact `Fixture.sol:line:column`, construct and message, and leave
no olean. This records the current boundary; it admits nothing.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

POST_CALL = ('storage reads, storage writes, logs and other interactions after an external CALL '
             'are unsupported: the call may re-enter this contract')
CALL = 'IHook(target).hook();'
TRY = 'try IHook(target).hook() {{{success}}} catch {{{failure}}}'

# name, body of `checked`, expected rejection (True) or positive control (False)
CASES = [
    ('trailing-call', f'pending = value;\n        {CALL}', False),
    ('trailing-try', 'pending = value;\n        ' + TRY.format(success='', failure=''), False),
    ('local-after-call', f'pending = value;\n        {CALL}\n        uint256 local = value + 1;\n'
                         '        require(local != 0, Failed());', False),
    ('read-after-call', f'{CALL}\n        seen = pending;', True),
    ('write-after-call', f'{CALL}\n        pending = value;', True),
    ('require-storage-after-call', f'{CALL}\n        require(pending == value, Failed());', True),
    ('emit-after-call', f'pending = value;\n        {CALL}\n        emit Poked(value);', True),
    ('second-call', f'pending = value;\n        {CALL}\n        {CALL}', True),
    ('try-success-write', TRY.format(success=' pending = value; ', failure=''), True),
    ('try-catch-write', TRY.format(success='', failure=' pending = value; '), True),
    ('try-catch-read', TRY.format(success='', failure=' seen = pending; '), True),
]


def source(statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'interface IHook {\n    function hook() external;\n}\n\n'
            'contract C {\n    error Failed();\n    event Poked(uint256 value);\n'
            '    uint256 private pending;\n    uint256 private seen;\n\n'
            '    function checked(address target, uint256 value) external {\n'
            f'        {statements}\n    }}\n}}\n')


def location(text, marker):
    start = text.index(marker)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='reentrant-callback-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, statements, rejected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(statements)
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked(address,uint256)
''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                                cwd=root, text=True, capture_output=True, timeout=300)
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if not rejected:
            if result.returncode or not artifact.exists():
                raise SystemExit(f'{name}: positive control failed\n{log}')
            diagnostic = None
        else:
            line, column = location(text, 'function checked(')
            diagnostic = (f'Fixture.sol:{line}:{column}: FunctionDefinition: '
                          f'[solidity-import:unsupported] {POST_CALL}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass reentrant-callback-{name}', flush=True)
    print(f'reentrant callback rejections passed: {output}')


if __name__ == '__main__':
    main()
