"""Located rejections and positive controls for `this` as a value and low-level `staticcall`.

Each case is imported on its own (solc 0.8.34, via-IR and legacy). A positive control must
elaborate and leave an olean; a near miss must fail with the exact `Fixture.sol:line:column`
position of the rejected node, its construct and message, and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'options': 'low-level staticcall options are outside this slice',
    'external': 'external contract calls are outside this slice',
    'this-member': 'member {member} of this is outside this slice',
    'reassigned': 'reassigned low-level staticcall return data is outside this slice',
    'payload': 'low-level staticcall payload must be bytes memory, found {found}',
    'yul-mload': 'Yul word load from low-level staticcall return data is outside this slice',
    'effectful-abi': 'effectful ABI encoding argument is unsupported',
    'codehash-after-call': 'code hash read after an external call or create2 is unsupported',
}

# name, statements of `f`'s body, expected: None (positive control) or
# (marker, message key, construct, format arguments).
CASES = [
    ('this-encode', 'ok = keccak256(abi.encode(h, this)) != bytes32(0);', None),
    ('this-compare', 'ok = this == C(token);', None),
    ('staticcall-tuple',
     '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); ok = s && r.length > 0;',
     None),
    ('staticcall-success-only', '(bool s, ) = token.staticcall(abi.encode(h)); ok = s;',
     None),
    ('staticcall-store-after', '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'stored = r.length; ok = s;', None),
    ('staticcall-struct-selector-member',
     'Box memory b = Box(bytes4(h)); '
     '(bool s, ) = token.staticcall(abi.encodeWithSelector(b.selector, h)); ok = s;',
     None),
    ('staticcall-yul-mload-length',
     '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'uint256 n; assembly { n := mload(r) } ok = s && n > 0;',
     None),
    ('staticcall-then-codehash',
     '(bool s, ) = token.staticcall(abi.encode(h)); ok = s && token.codehash != bytes32(0);',
     None),
    ('call-then-staticcall-store',
     'IHook(token).hook(); (bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'stored = r.length; ok = s;',
     None),
    ('staticcall-erc1271-bytes-calldata',
     '(bool s, bytes memory r) = token.staticcall('
     'abi.encodeWithSelector(bytes4(0x1626ba7e), h, msg.data)); '
     'ok = s && bytes4(r) == bytes4(0x1626ba7e);',
     None),
    ('self-delegatecall-coexists',
     '(bool s, ) = address(this).delegatecall(abi.encodeWithSelector(C.g.selector)); ok = s;',
     None),
    # An external CALL to this contract, not its address word.
    ('this-call', 'ok = this.g() > 0;', ('this.g', 'external', 'MemberAccess', {})),
    ('this-paren-call', 'ok = (this).g() > 0;', ('(this).g', 'external', 'MemberAccess', {})),
    ('this-function-address', 'ok = this.g.address == token;',
     ('this.g.address', 'this-member', 'MemberAccess', {'member': 'g'})),
    ('staticcall-gas-option', '(bool s, ) = token.staticcall{gas: 5000}(abi.encode(h)); ok = s;',
     ('token.staticcall{gas: 5000}', 'options', 'FunctionCallOptions', {})),
    ('staticcall-statement', 'token.staticcall(abi.encode(h)); ok = true;',
     ('token.staticcall', 'external', 'MemberAccess', {})),
    ('staticcall-assignment',
     'bool s; bytes memory r; (s, r) = token.staticcall(abi.encode(h)); ok = s;',
     ('token.staticcall', 'external', 'MemberAccess', {})),
    ('staticcall-reassigned-data', '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'r = abi.encode(s); ok = r.length > 0;',
     ('bytes memory r)', 'reassigned', 'VariableDeclaration', {})),
    ('staticcall-yul-mload',
     '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'bytes32 w; assembly { w := mload(add(r, 0x20)) } ok = s && w != bytes32(0);',
     ('mload(add(r, 0x20))', 'yul-mload', 'YulFunctionCall', {})),
    ('staticcall-yul-mload-alias',
     '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); bytes memory c = r; '
     'bytes32 w; assembly { w := mload(add(c, 0x20)) } ok = s && w != bytes32(0);',
     ('mload(add(c, 0x20))', 'yul-mload', 'YulFunctionCall', {})),
    ('staticcall-yul-mload-cross-file',
     '(bool s, bytes memory r) = token.staticcall(abi.encode(h)); '
     'ok = s && Helper.readWord(r) != bytes32(0);',
     ('mload(add(r, 0x20))', 'yul-mload', 'YulFunctionCall',
      {'file': 'Helper.sol', 'closure': 'C.f -> Helper.readWord'})),
    ('selector-struct-effect',
     'uint256 y = 1; bytes32 d = keccak256(abi.encodeWithSelector('
     'bytes4(0x11223344), y, ((y = 2) > 0 ? Box(bytes4(h)) : Box(bytes4(0))).selector)); '
     'ok = d != bytes32(0);',
     ('y = 2)', 'effectful-abi', 'Assignment', {})),
    ('selector-value-effect',
     'bytes4 y = 0x00000001; bytes32 d = keccak256(abi.encodeWithSelector('
     'bytes4(0xaaaaaaaa), y, keccak256(abi.encodeWithSelector(y = 0x11223344)))); '
     'ok = d != bytes32(0);',
     ('y = 0x11223344)', 'effectful-abi', 'Assignment', {})),
    ('staticcall-calldata-payload', '(bool s, ) = token.staticcall(msg.data); ok = s;',
     ('msg.data)', 'payload', 'MemberAccess', {'found': 'bytes calldata'})),
    ('delegatecall', '(bool s, ) = token.delegatecall(abi.encode(h)); ok = s;',
     ('token.delegatecall', 'external', 'MemberAccess', {})),
    ('call-then-staticcall-codehash',
     'IHook(token).hook(); (bool s, ) = token.staticcall(abi.encode(h)); '
     'ok = s && token.codehash != bytes32(0);',
     ('token.codehash', 'codehash-after-call', 'MemberAccess', {})),
]
PIPELINES = {'via-ir': 'true', 'legacy': 'false'}


HELPER_SOURCE = ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
                 'library Helper {\n'
                 '    function readWord(bytes memory r) internal pure returns (bytes32 w) {\n'
                 '        assembly { w := mload(add(r, 0x20)) }\n'
                 '    }\n}\n')


def source(body):
    header = 'import {Helper} from "./Helper.sol";\n\n' if 'Helper.' in body else ''
    hook = 'interface IHook { function hook() external; }\n\n' if 'IHook(' in body else ''
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            f'{header}{hook}'
            'contract C {\n    struct Box { bytes4 selector; }\n    uint256 private stored;\n\n'
            '    function g() external view returns (uint256) {\n        return stored;\n    }\n\n'
            '    function f(address token, bytes32 h) external returns (bool ok) {\n'
            f'        {body}\n'
            '    }\n}\n')


def location(text, marker):
    start = text.index(marker)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--pipeline', action='append', choices=sorted(PIPELINES))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='low-level-staticcall-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for pipeline in args.pipeline or sorted(PIPELINES):
        for name, body, expected in CASES:
            if args.only and args.only != name:
                continue
            text = source(body)
            directory = output / pipeline / name
            directory.mkdir(parents=True)
            (directory / 'Fixture.sol').write_text(text)
            if 'Helper.' in body:
                (directory / 'Helper.sol').write_text(HELPER_SOURCE)
            driver = directory / 'Check.lean'
            driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := {PIPELINES[pipeline]},
           optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function f(address,bytes32)
''')
            artifact = directory / 'Check.olean'
            result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                                    cwd=root, text=True, capture_output=True, timeout=300)
            log = result.stdout + result.stderr
            (directory / 'check.log').write_text(log)
            if expected is None:
                if result.returncode or not artifact.exists():
                    raise SystemExit(f'{pipeline}/{name}: positive control failed\n{log}')
                diagnostic = None
            else:
                marker, key, construct, values = expected
                target_file = values.get('file', 'Fixture.sol')
                target_text = HELPER_SOURCE if target_file == 'Helper.sol' else text
                line, column = location(target_text, marker)
                fmt_values = {k: v for k, v in values.items() if k not in ('file', 'closure')}
                diagnostic = (f'{target_file}:{line}:{column}: {construct}: '
                              f'[solidity-import:unsupported] {MESSAGES[key].format(**fmt_values)}')
                closure = values.get('closure')
                if closure:
                    diagnostic += f'\nclosure: {closure}'
                if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                    raise SystemExit(f'{pipeline}/{name}: expected exact located rejection '
                                     f'{diagnostic!r}\n{log}')
            results.append({'pipeline': pipeline, 'case': name, 'diagnostic': diagnostic,
                            'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
            (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            print(f'pass low-level-staticcall-rejections-{pipeline}-{name}', flush=True)
    print(f'low-level staticcall rejections passed: {output}')


if __name__ == '__main__':
    main()
