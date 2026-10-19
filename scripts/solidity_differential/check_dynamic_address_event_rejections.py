"""Located near-miss rejections and positive controls for dynamic `T[] calldata` event payloads.

Each case is imported on its own. A positive control must elaborate and leave
an olean; a near miss must fail with the exact `Fixture.sol:line:column`
position of the named node, its construct and message, and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'indexed-array': 'unsupported event parameter type address[]',
    'calldata-only': 'dynamic event array arguments must be calldata array parameters',
    'element-bytes4': 'unsupported dynamic event array type bytes4[]',
    'struct-mix': 'struct and dynamic array event arguments together are unsupported',
    'anonymous': 'anonymous events are unsupported',
    'total-companion': 'event arguments currently require total scalar expressions',
}
PARAMS = 'address[] calldata a, uint256[] calldata b, address t'
SIGNATURE = '«address[]», «uint256[]», address'
PAIR = 'event Pair(address indexed caller, address[] a, uint256[] b, address indexed t);'

# name, declarations, contract members, parameters, model signature, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('two-arrays-two-topics', '', PAIR, PARAMS, SIGNATURE, 'emit Pair(msg.sender, a, b, t);', None),
    ('array-only', '', 'event Only(address[] a);', PARAMS, SIGNATURE, 'emit Only(a);', None),
    ('scalar-companions', '', 'event Mixed(uint256 n, address[] a, address w, uint256[] b);',
     PARAMS, SIGNATURE, 'emit Mixed(7, a, t, b);', None),
    ('library-event', 'library L {\n    event Pair(address[] a, uint256[] indexed n);\n}\n'
     'library Q {\n    event Pair(address[] a, address indexed t);\n}\n', '', PARAMS, SIGNATURE,
     'emit Q.Pair(a, t);', None),
    ('validated-kinds', '', 'event Kinds(bool[] f, uint8[] s, bytes32[] k, int256[] i);',
     'bool[] calldata f, uint8[] calldata s, bytes32[] calldata k, int256[] calldata i',
     '«bool[]», «uint8[]», «bytes32[]», «int256[]»', 'emit Kinds(f, s, k, i);', None),
    ('same-array-twice', '', 'event Twice(address[] a, address[] c);', PARAMS, SIGNATURE,
     'emit Twice(a, a);', None),
    ('indexed-array', '', 'event Indexed(address[] indexed a);', PARAMS, SIGNATURE, 'emit Indexed(a);',
     ('address[] indexed a', 0, 'VariableDeclaration', 'indexed-array')),
    ('memory-array', '', 'event Only(address[] a);', PARAMS, SIGNATURE,
     'emit Only(new address[](1));', ('new address[](1)', 0, 'FunctionCall', 'calldata-only')),
    ('calldata-slice', '', 'event Only(address[] a);', PARAMS, SIGNATURE, 'emit Only(a[1:]);',
     ('a[1:]', 0, 'IndexRangeAccess', 'calldata-only')),
    ('bytes4-elements', '', 'event Tags(bytes4[] s);', 'bytes4[] calldata s, address t',
     '«bytes4[]», address', 'emit Tags(s);', ('s);', 1, 'Identifier', 'element-bytes4')),
    ('struct-and-array', 'struct Leg {\n    address token;\n    uint256[] weights;\n}\n',
     'event Both(Leg leg, address[] a);', 'Leg memory leg, address[] calldata a', 'Leg, «address[]»',
     'emit Both(leg, a);',
     ('leg, a)', 0, 'Identifier', 'struct-mix')),
    ('anonymous-array-event', '', 'event Only(address[] a) anonymous;', PARAMS, SIGNATURE,
     'emit Only(a);', ('event Only', 0, 'EventDefinition', 'anonymous')),
    ('indexed-element-companion', '', 'event Mixed(uint256 n, address[] a);', PARAMS, SIGNATURE,
     'emit Mixed(b[0], a);', ('b[0]', 0, 'IndexAccess', 'total-companion')),
]


def source(declarations, members, parameters, statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            f'{declarations}\ncontract C {{\n    {members}\n'
            f'    function checked({parameters}) external {{\n'
            f'        {statements}\n    }}\n}}\n')


def location(text, marker, occurrence):
    start = -1
    for _ in range(occurrence + 1):
        start = text.index(marker, start + 1)
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
              Path(tempfile.mkdtemp(prefix='dynamic-address-event-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, declarations, members, parameters, signature, statements, expected in CASES:
        if args.only and args.only not in name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(declarations, members, parameters, statements)
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked({signature})
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
            marker, occurrence, construct, key = expected
            line, column = location(text, marker, occurrence)
            diagnostic = (f'Fixture.sol:{line}:{column}: {construct}: '
                          f'[solidity-import:unsupported] {MESSAGES[key]}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass dynamic-address-event-{name}', flush=True)
    print(f'dynamic-event rejections passed: {output}')


if __name__ == '__main__':
    main()
