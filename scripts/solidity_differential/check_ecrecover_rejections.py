"""Positive controls and located rejections for the imported `ecrecover` builtin.

Each case is imported on its own. A positive control (the issue's pure signer check,
`ecrecover` inside a `require` condition, the right operand of `&&`, and a conditional
branch) must elaborate and leave an olean; a rejection (a discarded `ecrecover(...)`
expression statement) must fail with the exact `Fixture.sol:line:column` position, its
construct and message, and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HEADER = '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.20;\n\ncontract C {\n    uint256 private uses;\n\n'

# name, signature, function body, expected: None (positive control) or (marker, construct, message)
CASES = [
    ('pure-signer-check', 'bytes32,uint8,bytes32,bytes32,address',
     '    function f(bytes32 digest, uint8 v, bytes32 r, bytes32 s, address expected)\n'
     '        external pure returns (bool)\n    {\n'
     '        address recovered = ecrecover(digest, v, r, s);\n'
     '        return recovered != address(0) && recovered == expected;\n    }\n', None),
    ('require-condition', 'bytes32,uint8,bytes32,bytes32',
     '    function f(bytes32 digest, uint8 v, bytes32 r, bytes32 s) external {\n'
     '        require(ecrecover(digest, v, r, s) == msg.sender, "bad signer");\n'
     '        uses += 1;\n    }\n', None),
    ('short-circuit-operand', 'bool,bytes32,uint8,bytes32,bytes32,address',
     '    function f(bool check, bytes32 digest, uint8 v, bytes32 r, bytes32 s, address expected)\n'
     '        external pure returns (bool)\n    {\n'
     '        return check && ecrecover(digest, v, r, s) == expected;\n    }\n', None),
    ('conditional-branch', 'bool,bytes32,uint8,bytes32,bytes32',
     '    function f(bool check, bytes32 digest, uint8 v, bytes32 r, bytes32 s)\n'
     '        external pure returns (address)\n    {\n'
     '        return check ? ecrecover(digest, v, r, s) : address(0);\n    }\n', None),
    ('discarded-result', 'bytes32,uint8,bytes32,bytes32',
     '    function f(bytes32 digest, uint8 v, bytes32 r, bytes32 s) external {\n'
     '        ecrecover(digest, v, r, s);\n        uses += 1;\n    }\n',
     ('ecrecover(digest, v, r, s);', 'Identifier',
      'only builtin require calls are supported as expression statements')),
]


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
              Path(tempfile.mkdtemp(prefix='ecrecover-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, signature, body, expected in CASES:
        if args.only and args.only != name:
            continue
        text = HEADER + body + '}\n'
        directory = output / name
        directory.mkdir()
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function f({signature})
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
            marker, construct, message = expected
            line, column = location(text, marker)
            diagnostic = f'Fixture.sol:{line}:{column}: {construct}: [solidity-import:unsupported] {message}'
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass ecrecover-rejections-{name}', flush=True)
    print(f'ecrecover rejections passed: {output}')


if __name__ == '__main__':
    main()
