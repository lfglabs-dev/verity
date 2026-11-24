"""Positive controls and located rejections for Yul `calldataload` over `bytes calldata` (#2920).

Each case is imported on its own. A positive control (OpenZeppelin's `tryRecoverCalldata`
split inside a helper, the same reads in a root function or a modifier, and either operand
order of `add`) must elaborate and leave an olean; a rejection must fail with the exact
`Fixture.sol:line:column` position, its construct and message, and leave no olean. A root
`string calldata` parameter has the same payload layout. The rejections are the near misses
of the admitted shape: a literal or computed offset, an offset literal at or above `2^64`, a
calldata slice (whose payload offset is not a decoded root head), a memory-backed conditional
argument, a `msg.data` slice, `.offset` outside `calldataload` and the Yul `.length` suffix.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HEADER = '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.20;\n\ncontract C {\n'

READS = ('            r := calldataload(signature.offset)\n'
         '            s := calldataload(add(signature.offset, 0x20))\n'
         '            v := byte(0, calldataload(add(signature.offset, 0x40)))\n')

HELPER = ('    function split(bytes calldata signature) internal pure returns (bytes32 r, bytes32 s, uint8 v) {\n'
          '        assembly ("memory-safe") {\n' + READS + '        }\n    }\n\n')

MESSAGE = ('Yul calldataload must read at p.offset or add(p.offset, k) of a root bytes calldata '
           'parameter p, with a literal k below 2^64')


def root(body):
    return ('    function f(bytes calldata signature) external pure returns (bytes32 r, bytes32 s, uint8 v) {\n'
            + body + '    }\n')


def asm(lines):
    return '        assembly ("memory-safe") {\n' + lines + '        }\n'


# name, signature, contract body, expected: None (positive control) or (marker, construct, message)
CASES = [
    ('helper-split', 'bytes',
     HELPER + root('        (r, s, v) = split(signature);\n'), None),
    ('root-split', 'bytes', root(asm(READS)), None),
    ('nested-helper-split', 'bytes',
     HELPER + '    function relay(bytes calldata signature) internal pure returns (bytes32, bytes32, uint8) {\n'
     '        return split(signature);\n    }\n\n'
     + root('        (r, s, v) = relay(signature);\n'), None),
    ('literal-first-add', 'bytes',
     root(asm('            r := calldataload(add(0x20, signature.offset))\n')), None),
    ('string-root', 'string',
     '    function f(string calldata signature) external pure returns (bytes32 r) {\n'
     + asm('            r := calldataload(add(signature.offset, 0x20))\n') + '    }\n', None),
    ('modifier-argument', 'bytes',
     '    bytes32 private seen;\n\n'
     '    modifier m(bytes calldata signature) {\n        bytes32 r;\n'
     + asm('            r := calldataload(add(signature.offset, 0x20))\n')
     + '        seen = r;\n        _;\n    }\n\n'
     '    function f(bytes calldata signature) external m(signature) returns (bytes32 r) {\n'
     '        r = seen;\n    }\n', None),
    ('literal-offset', 'bytes',
     root(asm('            r := calldataload(0x44)\n')),
     ('0x44', 'YulLiteral', MESSAGE)),
    ('computed-offset', 'bytes',
     root(asm('            let k := 0x20\n            r := calldataload(add(signature.offset, k))\n')),
     ('add(signature.offset, k)', 'YulFunctionCall', MESSAGE)),
    ('wide-literal', 'bytes',
     root(asm('            r := calldataload(add(signature.offset, 0x10000000000000000))\n')),
     ('add(signature.offset, 0x10000000000000000)', 'YulFunctionCall', MESSAGE)),
    ('slice-argument', 'bytes',
     HELPER + root('        (r, s, v) = split(signature[1:]);\n'),
     ('signature.offset)\n            s', 'YulIdentifier', MESSAGE)),
    ('conditional-argument', 'bytes,bytes,bool',
     HELPER + '    function f(bytes calldata a, bytes calldata b, bool c)\n'
     '        external pure returns (bytes32 r, bytes32 s, uint8 v)\n    {\n'
     '        (r, s, v) = split(c ? a : b);\n    }\n',
     ('signature.offset)\n            s', 'YulIdentifier', MESSAGE)),
    ('msg-data-slice', '',
     HELPER + '    function f() external pure returns (bytes32 r, bytes32 s, uint8 v) {\n'
     '        (r, s, v) = split(msg.data[4:]);\n    }\n',
     ('signature.offset)\n            s', 'YulIdentifier', MESSAGE)),
    ('offset-outside-calldataload', 'bytes',
     root(asm('            r := signature.offset\n')),
     ('signature.offset\n', 'YulIdentifier', 'unbound Yul identifier signature.offset')),
    ('yul-length', 'bytes',
     root(asm('            r := signature.length\n')),
     ('signature.length', 'YulIdentifier', 'unbound Yul identifier signature.length')),
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
    workspace = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='signature-calldata-rejections-', dir=workspace / '.lake')))
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
                                cwd=workspace, text=True, capture_output=True, timeout=300)
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
        print(f'pass signature-calldata-rejections-{name}', flush=True)
    print(f'signature calldata rejections passed: {output}')


if __name__ == '__main__':
    main()
