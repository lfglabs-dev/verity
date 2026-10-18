"""Located near-miss rejections and positive controls for CREATE2 code storage and struct events.

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

PREFIX = 'hex"600b380380600b5f395ff3"'
MESSAGES = {
    'value': 'create2 with a nonzero or computed value is unsupported',
    'offset': 'create2 initcode offset must be add(buffer, 0x20) of a bytes memory local',
    'size': 'create2 initcode size must be mload of the same bytes memory local',
    'template': 'create2 initcode must start with a checked deployment-prefix literal',
    'placement': 'Yul create2 must be the whole value of a Yul assignment or variable declaration',
    'create': 'unsupported Yul builtin create',
    'indexed-struct': 'indexed struct event parameters are unsupported',
    'struct-argument': 'struct event arguments must be memory struct variables',
    'indexed-type': 'unsupported event parameter type string',
    'anonymous': 'anonymous events are unsupported',
    'indexed-narrow': 'unsupported indexed struct-event parameter type bytes4',
    'reassigned': 'encoded byte locals are limited to hash and packed encoding operands',
}


def deploy(value='0', offset='add(code, 0x20)', size='mload(code)', salt='salt'):
    return f'create2({value}, {offset}, {size}, {salt})'


def body(init=f'abi.encodePacked({PREFIX}, abi.encode(leg))', assembly=None, after=''):
    assembly = assembly or f'deployed := {deploy()}'
    return (f'bytes memory code = {init};\n        assembly {{ {assembly} }}\n'
            f'        {after}')


EVENT = 'event Stored(Leg leg, bytes32 indexed key, address indexed at);'
EMIT = 'emit Stored(leg, salt, deployed);'

# name, declarations, contract members, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('root-assignment', '', '', body(), None),
    ('yul-let', '', '', body(assembly=f'let created := {deploy()} deployed := created'), None),
    ('reversed-offset', '', '', body(assembly=f'deployed := {deploy(offset="add(0x20, code)")}'), None),
    ('concat-constant', '', f'bytes constant PREFIX = {PREFIX};',
     body(init='bytes.concat(PREFIX, abi.encode(leg))'), None),
    ('expanded-template', '', '',
     body(init='abi.encodePacked(hex"600d380380600d6000396000f3", abi.encode(leg))'), None),
    ('library-helper',
     'library Store {\n    function put(bytes32 salt, uint256 w) internal returns (address deployed) {\n'
     f'        bytes memory code = abi.encodePacked({PREFIX}, abi.encode(w));\n'
     f'        assembly ("memory-safe") {{ deployed := {deploy()} }}\n'
     '        if (deployed == address(0)) revert();\n    }\n}\n', '',
     'deployed = Store.put(salt, leg.weight);', None),
    ('struct-event', '', EVENT, body(after=EMIT), None),
    ('struct-and-scalar-event', '', 'event Pair(uint256 indexed n, Leg leg, uint256 w);',
     body(after='emit Pair(1, leg, leg.weight);'), None),
    ('nonzero-value', '', '', body(assembly=f'deployed := {deploy(value="1")}'),
     ('1, add(code', 0, 'YulLiteral', 'value')),
    ('computed-value', '', '', body(assembly=f'deployed := {deploy(value="callvalue()")}'),
     ('callvalue()', 0, 'YulFunctionCall', 'value')),
    ('unaligned-offset', '', '', body(assembly=f'deployed := {deploy(offset="add(code, 0x21)")}'),
     ('add(code, 0x21)', 0, 'YulFunctionCall', 'offset')),
    ('raw-offset', '', '', body(assembly=f'deployed := {deploy(offset="0x80")}'),
     ('0x80', 0, 'YulLiteral', 'offset')),
    ('short-size', '', '', body(assembly=f'deployed := {deploy(size="sub(mload(code), 1)")}'),
     ('sub(mload(code), 1)', 0, 'YulFunctionCall', 'size')),
    ('other-buffer-size', '', '',
     'bytes memory other = abi.encode(leg);\n        ' +
     body(assembly=f'deployed := {deploy(size="mload(other)")}'),
     ('mload(other)', 0, 'YulFunctionCall', 'size')),
    ('unchecked-template', '', '',
     body(init='bytes.concat(hex"600b5981380380925939f3", abi.encode(leg))'),
     ('add(code, 0x20)', 0, 'YulFunctionCall', 'template')),
    ('no-template', '', '', body(init='abi.encode(leg)'),
     ('add(code, 0x20)', 0, 'YulFunctionCall', 'template')),
    ('reassigned-buffer', '', '',
     f'bytes memory code = abi.encodePacked({PREFIX}, abi.encode(leg));\n'
     f'        code = abi.encodePacked({PREFIX}, abi.encode(salt));\n'
     f'        assembly {{ deployed := {deploy()} }}',
     (f'code = abi.encodePacked({PREFIX}, abi.encode(salt))', 0, 'Identifier', 'reassigned')),
    ('nested-create2', '', '',
     body(assembly=f'deployed := and({deploy()}, 0xffffffffffffffffffffffffffffffffffffffff)'),
     ('create2(', 0, 'YulFunctionCall', 'placement')),
    ('create-opcode', '', '', body(assembly='deployed := create(0, add(code, 0x20), mload(code))'),
     ('create(0', 0, 'YulFunctionCall', 'create')),
    ('indexed-struct', '', 'event Stored(Leg indexed leg);', body(after='emit Stored(leg);'),
     ('Leg indexed leg', 0, 'VariableDeclaration', 'indexed-struct')),
    ('struct-constructor-argument', '', EVENT,
     body(after='emit Stored(Leg(deployed, 1), salt, deployed);'),
     ('Leg(deployed, 1)', 0, 'FunctionCall', 'struct-argument')),
    ('storage-struct-argument', '', 'Leg stored;\n    ' + EVENT,
     body(after='emit Stored(stored, salt, deployed);'),
     ('stored, salt', 0, 'Identifier', 'struct-argument')),
    ('indexed-string', '', 'event Named(Leg leg, string indexed name);',
     body(after='emit Named(leg, "x");'),
     ('string indexed name', 0, 'VariableDeclaration', 'indexed-type')),
    ('indexed-bytes4', '', 'event Tagged(Leg leg, bytes4 indexed tag);',
     body(after='emit Tagged(leg, bytes4(salt));'),
     ('bytes4 indexed tag', 0, 'VariableDeclaration', 'indexed-narrow')),
    ('anonymous-struct-event', '', 'event Stored(Leg leg) anonymous;', body(after='emit Stored(leg);'),
     ('event Stored', 0, 'EventDefinition', 'anonymous')),
]


def source(declarations, members, statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'struct Leg {\n    address token;\n    uint256 weight;\n}\n\n'
            f'{declarations}\ncontract C {{\n    {members}\n'
            '    function checked(Leg memory leg, bytes32 salt) external returns (address deployed) {\n'
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
              Path(tempfile.mkdtemp(prefix='create2-struct-emit-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, declarations, members, statements, expected in CASES:
        if args.only and args.only not in name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(declarations, members, statements)
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked(Leg,bytes32)
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
        print(f'pass create2-struct-emit-{name}', flush=True)
    print(f'CREATE2/struct-event rejections passed: {output}')


if __name__ == '__main__':
    main()
