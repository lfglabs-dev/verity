"""Located evaluation-order rejections and positive controls for inline-assembly `call`.

Yul evaluates the operands of a builtin right to left, while the importer hoists a `call`
ahead of its enclosing expression. Each case is imported on its own. A positive control
(the call is the rightmost operand, or its siblings are call-independent) must elaborate and
leave an olean; a near miss (a sibling that reads memory or returndata, a second call, an
operand that would be hoisted ahead of the call) must fail with the exact
`Fixture.sol:line:column` position of the enclosing builtin, its construct and message, and
leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'observer': 'Yul external call is evaluated after an operand that could observe it; '
                'assign the call to a variable first',
    'hoisted': 'Yul operands left of an external call must not need hoisting; '
               'assign the call to a variable first',
}

CALL = 'call(gas(), token, 0, 0x00, 0x20, 0x00, 0x20)'

# name, assembly expression assigned to `ok`, expected
# expected: None (positive control) or (marker, message key)
CASES = [
    ('call-only', CALL, None),
    ('call-rightmost', f'and(eq(mload(0x00), 1), {CALL})', None),
    ('call-with-call-independent-sibling', f'and({CALL}, amount)', None),
    ('call-with-hoisted-call', f'iszero(iszero({CALL}))', None),
    ('memory-sibling', f'and({CALL}, eq(mload(0x00), 1))', ('and(call(', 'observer')),
    ('returndata-sibling', f'and({CALL}, iszero(returndatasize()))', ('and(call(', 'observer')),
    ('two-calls', f'and({CALL}, {CALL})', ('and(call(', 'observer')),
    ('nested-memory-sibling', f'and(or({CALL}, 0), eq(mload(0x00), 1))', ('and(or(', 'observer')),
    ('hoisted-sibling', f'and(extcodesize(token), {CALL})', ('and(extcodesize(', 'hoisted')),
]


def source(expression):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'contract C {\n    uint256 private pushes;\n    uint256 private lastAmount;\n\n'
            '    function f(address token, uint256 amount) external returns (bool ok) {\n'
            '        pushes += 1;\n        lastAmount = amount;\n'
            '        assembly ("memory-safe") {\n'
            '            mstore(0x00, amount)\n'
            f'            ok := {expression}\n'
            '        }\n    }\n}\n')


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
              Path(tempfile.mkdtemp(prefix='yul-memory-call-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, expression, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(expression)
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function f(address,uint256)
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
            marker, key = expected
            line, column = location(text, marker)
            diagnostic = (f'Fixture.sol:{line}:{column}: YulFunctionCall: '
                          f'[solidity-import:unsupported] {MESSAGES[key]}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass yul-memory-call-rejections-{name}', flush=True)
    print(f'yul memory call rejections passed: {output}')


if __name__ == '__main__':
    main()
