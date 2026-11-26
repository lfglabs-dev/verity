"""Positive controls and located negative controls for post-CALL state access and callbacks.

Once post-CALL storage reads, storage writes, logs, and follow-up closed calls are admitted
under `onlyClosedCallStateWindows` (carrying `reentrancyAdversarial` and
`solidity_post_call_state_access`), every closed shape below imports cleanly. Disallowed
post-CALL shapes (a code-hash read after a CALL, value-bearing calls, `delegatecall`, and a
second CALL carrying value) fail with exact `Fixture.sol:line:column` diagnostics.

All non-closed external interactions currently reject earlier during lowering with their
construct-specific diagnostics; the post-CALL `onlyClosedCallStateWindows` check at the
function definition in `Import.lean` is defense in depth (pinned on hand-built `Stmt` bodies
in `PostCallStateAccessChecks.lean` and exercised via mutation in `check_memory_call_mutations.py`).
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'codehash-after-call': 'code hash read after an external call or create2 is unsupported',
    'external-call': 'external contract calls are outside this slice',
    'post-call': ('storage reads, storage writes and logs after an external CALL are '
                  'supported only when every external interaction of the function is a '
                  'closed transport: another interaction follows a CALL that may re-enter '
                  'this contract'),
}
CALL = 'IHook(target).hook();'
TRY = 'try IHook(target).hook() {{{success}}} catch {{{failure}}}'

# name, body of `checked`, expected: None (positive control) or (marker, construct, message key)
CASES = [
    ('trailing-call', f'pending = value;\n        {CALL}', None),
    ('trailing-try', 'pending = value;\n        ' + TRY.format(success='', failure=''), None),
    ('emit-before-call', f'emit Poked(value);\n        {CALL}', None),
    ('local-after-call', f'pending = value;\n        {CALL}\n        uint256 local = value + 1;\n'
                         '        require(local != 0, Failed());', None),
    ('read-after-call', f'{CALL}\n        seen = pending;', None),
    ('write-after-call', f'{CALL}\n        pending = value;', None),
    ('require-storage-after-call', f'{CALL}\n        require(pending == value, Failed());', None),
    ('emit-after-call', f'pending = value;\n        {CALL}\n        emit Poked(value);', None),
    ('second-call', f'pending = value;\n        {CALL}\n        {CALL}', None),
    ('try-success-write', TRY.format(success=' pending = value; ', failure=''), None),
    ('try-catch-write', TRY.format(success='', failure=' pending = value; '), None),
    ('try-catch-read', TRY.format(success='', failure=' seen = pending; '), None),
    # Located negative controls for disallowed post-call shapes.
    ('call-then-codehash', f'{CALL}\n        lastHash = target.codehash;',
     ('target.codehash;', 'MemberAccess', 'codehash-after-call')),
    ('value-call-then-write',
     '(bool ok, bytes memory data) = target.call{value: 1}("");\n'
     '        require(ok, Failed());\n        pending = value + data.length;',
     ('function checked', 'FunctionDefinition', 'post-call')),
    ('delegatecall-then-write',
     '(bool ok,) = target.delegatecall("");\n        require(ok, Failed());\n        pending = value;',
     ('target.delegatecall', 'MemberAccess', 'external-call')),
    ('second-call-value',
     f'{CALL}\n        IPayableHook(target).hook{{value: 1}}();',
     ('IPayableHook(target).hook{value: 1}', 'FunctionCallOptions', 'external-call')),
]


def source(statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'interface IHook {\n    function hook() external;\n}\n\n'
            'interface IPayableHook {\n    function hook() external payable;\n}\n\n'
            'contract C {\n    error Failed();\n    event Poked(uint256 value);\n'
            '    uint256 private pending;\n    uint256 private seen;\n'
            '    bytes32 private lastHash;\n\n'
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
    if args.only and args.only not in {name for name, _, _ in CASES}:
        parser.error(f'unknown case {args.only}')
    results = []
    for name, statements, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir(exist_ok=True)
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
        if expected is None:
            if result.returncode or not artifact.exists():
                raise SystemExit(f'{name}: positive control failed\n{log}')
            diagnostic = None
        else:
            marker, construct, message_key = expected
            line, column = location(text, marker)
            diagnostic = (f'Fixture.sol:{line}:{column}: {construct}: '
                          f'[solidity-import:unsupported] {MESSAGES[message_key]}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass reentrant-callback-{name}', flush=True)
    print(f'reentrant callback rejections passed: {output}')


if __name__ == '__main__':
    main()
