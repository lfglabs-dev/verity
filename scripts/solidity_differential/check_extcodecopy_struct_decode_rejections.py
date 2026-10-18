"""Located near-miss rejections and positive controls for `<address>.code` and dynamic-struct `abi.decode`.

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
    'this-code': 'code of the executing contract is unsupported',
    'code-read': 'external contract code reads are outside this slice',
    'calldata-source': 'abi.decode of a dynamic struct requires a bytes memory source',
    'only-target': 'abi.decode of a dynamic struct requires it as the only target type',
    'bytes-member': 'unsupported abi.decode struct member type bytes',
    'nested-member': 'unsupported abi.decode struct member type struct Inner',
    'fixed-member': 'unsupported abi.decode struct member type uint256[2]',
    'named-return': 'named dynamic struct return parameters are unsupported',
    'calldata-return': 'dynamic struct returns require a memory struct with a complete ABI schema',
    'other-return': 'dynamic struct returns require abi.decode or a memory struct variable',
    'reassigned': 'reassigned struct locals are outside this slice',
    'flat-only': 'struct abi.decode requires a flat struct target type',
    'scalar-only': 'scalar abi.decode expression requires a scalar target type',
}

SPEC = 'Spec memory'
RETURNS_SPEC = f'returns ({SPEC})'

# name, declarations, signature, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('return-decode', '', f'(address pointer) external view {RETURNS_SPEC}',
     'return abi.decode(pointer.code, (Spec));', None),
    ('local-decode', '', f'(address pointer) external view {RETURNS_SPEC}',
     'Spec memory spec = abi.decode(pointer.code, (Spec));\n        return spec;', None),
    ('bytes-local', '', f'(address pointer) external view {RETURNS_SPEC}',
     'bytes memory data = pointer.code;\n        return abi.decode(data, (Spec));', None),
    ('bytes-memory-param', '', f'(bytes memory raw) external pure {RETURNS_SPEC}',
     'return abi.decode(raw, (Spec));', None),
    ('memory-param-return', '', f'(Spec memory spec) external pure {RETURNS_SPEC}',
     'return spec;', None),
    ('field-reads', '', '(address pointer, uint256 i) external view returns (uint256, uint256)',
     'Spec memory spec = abi.decode(pointer.code, (Spec));\n'
     '        return (spec.legs[i].weight, spec.marks.length);', None),
    ('scalar-from-code', '', '(address pointer) external view returns (uint256)',
     'return abi.decode(pointer.code, (uint256));', None),
    ('hash-code', '', '(address pointer) external view returns (bytes32)',
     'return keccak256(pointer.code);', ('pointer.code', 0, 'MemberAccess', 'code-read')),
    ('library-helper',
     'library Reader {\n    function first(address pointer) internal view returns (uint256) {\n'
     '        Spec memory spec = abi.decode(pointer.code, (Spec));\n'
     '        return spec.tag;\n    }\n}\n',
     '(address pointer) external view returns (uint256)', 'return Reader.first(pointer);', None),
    ('this-code', '', f'() external view {RETURNS_SPEC}',
     'return abi.decode(address(this).code, (Spec));',
     ('address(this).code', 0, 'MemberAccess', 'this-code')),
    ('code-index', '', '(address pointer) external view returns (uint256)',
     'return uint8(pointer.code[0]);', ('pointer.code', 0, 'MemberAccess', 'code-read')),
    ('calldata-source', '', f'(bytes calldata raw) external pure {RETURNS_SPEC}',
     'return abi.decode(raw, (Spec));', ('raw, (Spec)', 0, 'Identifier', 'calldata-source')),
    ('extra-target', '', '(address pointer) external view returns (uint256)',
     '(Spec memory spec, uint256 n) = abi.decode(pointer.code, (Spec, uint256));\n'
     '        return spec.tag + n;', ('(Spec, uint256)', 0, 'TupleExpression', 'only-target')),
    ('bytes-member', 'struct Blob {\n    uint256 tag;\n    bytes data;\n}\n',
     '(address pointer) external view returns (uint256)',
     'Blob memory blob = abi.decode(pointer.code, (Blob));\n        return blob.tag;',
     ('bytes data;', 0, 'VariableDeclaration', 'bytes-member')),
    ('nested-member',
     'struct Inner {\n    uint256[] values;\n}\n\nstruct Outer {\n    uint256 tag;\n    Inner inner;\n}\n',
     '(address pointer) external view returns (uint256)',
     'Outer memory outer = abi.decode(pointer.code, (Outer));\n        return outer.tag;',
     ('Inner inner;', 0, 'VariableDeclaration', 'nested-member')),
    ('fixed-member', 'struct Pair {\n    uint256[2] values;\n    uint256[] rest;\n}\n',
     '(address pointer) external view returns (uint256)',
     'Pair memory pair = abi.decode(pointer.code, (Pair));\n        return pair.rest.length;',
     ('uint256[2] values;', 0, 'VariableDeclaration', 'fixed-member')),
    ('named-return', '', '(address pointer) external view returns (Spec memory result)',
     'result = abi.decode(pointer.code, (Spec));',
     ('Spec memory result', 0, 'VariableDeclaration', 'named-return')),
    ('calldata-return', '', f'(Spec calldata spec) external pure {RETURNS_SPEC}',
     'return spec;', ('spec;', 0, 'Identifier', 'calldata-return')),
    ('helper-return',
     'library Reader {\n    function load(address pointer) internal view returns (Spec memory) {\n'
     '        return abi.decode(pointer.code, (Spec));\n    }\n}\n',
     f'(address pointer) external view {RETURNS_SPEC}', 'return Reader.load(pointer);',
     ('Reader.load(pointer)', 0, 'FunctionCall', 'other-return')),
    ('reassigned-local', '', f'(address pointer, address other) external view {RETURNS_SPEC}',
     'Spec memory spec = abi.decode(pointer.code, (Spec));\n'
     '        spec = abi.decode(other.code, (Spec));\n        return spec;',
     ('Spec memory spec', 0, 'VariableDeclaration', 'reassigned')),
    ('member-of-decode', '', '(address pointer) external view returns (uint256)',
     'return abi.decode(pointer.code, (Spec)).tag;',
     ('abi.decode(pointer.code, (Spec))', 0, 'FunctionCall', 'flat-only')),
    ('tuple-return', '', '(address pointer) external view returns (Spec memory, uint256)',
     'return (abi.decode(pointer.code, (Spec)), 1);',
     ('abi.decode(pointer.code, (Spec))', 0, 'FunctionCall', 'scalar-only')),
]


def source(declarations, signature, statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'struct Leg {\n    address token;\n    uint96 weight;\n    bool active;\n}\n\n'
            'struct Spec {\n    uint256 tag;\n    address owner;\n    Leg[] legs;\n'
            '    uint64[] marks;\n}\n\n'
            f'{declarations}\ncontract C {{\n'
            f'    function checked{signature} {{\n'
            f'        {statements}\n    }}\n}}\n')


def location(text, marker, occurrence):
    start = -1
    for _ in range(occurrence + 1):
        start = text.index(marker, start + 1)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def parameter_types(signature):
    inner = signature[1:signature.index(')')]
    types = []
    for parameter in filter(None, (p.strip() for p in inner.split(','))):
        ty = parameter.split()[0]
        types.append({'Spec': 'Spec', 'Leg': 'Leg'}.get(ty, ty))
    return ','.join(types)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='extcodecopy-struct-decode-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, declarations, signature, statements, expected in CASES:
        if args.only and args.only not in name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(declarations, signature, statements)
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked({parameter_types(signature)})
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
        print(f'pass extcodecopy-struct-decode-{name}', flush=True)
    print(f'code-decoding rejections passed: {output}')


if __name__ == '__main__':
    main()
