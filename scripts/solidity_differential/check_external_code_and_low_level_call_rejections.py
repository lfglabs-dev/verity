"""Located near-miss rejections and positive controls for code-length reads and low-level calls.

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
    'external': 'external contract calls are outside this slice',
    'placement': ('low-level call must be a (bool success, bytes memory returndata) declaration '
                  'followed by returndata forwarding and optional-bool validation'),
    'bind': 'low-level call must bind both success and returndata, and validate the returndata',
    'sequence': 'low-level call must be followed by returndata forwarding and optional-bool validation',
    'forward': ('a failed low-level call must forward its returndata: '
                'if (!success) { assembly { revert(add(returndata, 0x20), mload(returndata)) } }'),
    'validation': ('low-level call returndata must be validated by '
                   'require(returndata.length == 0 || abi.decode(returndata, (bool)), ...)'),
    'reuse': 'low-level call results are read only by the returndata forwarding and validation',
    'encoding': ('low-level call data must be abi.encodeCall of an external function '
                 'with address, bool, bytes32 or uint256 parameters'),
    'param-type': 'unsupported low-level call parameter type bytes',
    'order': 'low-level call operands require explicit evaluation-order support',
    'this-code': 'code length of the executing contract is unsupported',
    'code-read': 'external contract code reads are outside this slice',
}

INTERFACE = ('interface IToken {\n'
             '    function transfer(address to, uint256 amount) external returns (bool);\n'
             '    function transferFrom(address from, address to, uint256 amount) external returns (bool);\n'
             '    function approveAndCall(address to, bytes memory data) external returns (bool);\n'
             '}\n')
DECLARE = 'bytes memory returndata'
CALL = 'token.call(abi.encodeCall(IToken.transfer, (to, amount)))'
FORWARD = ('if (!success) {\n            assembly ("memory-safe") {\n'
           '                revert(add(returndata, 0x20), mload(returndata))\n            }\n        }')
VALIDATE = 'require(returndata.length == 0 || abi.decode(returndata, (bool)), TransferFailed());'


def sequence(call=CALL, declare=f'(bool success, {DECLARE})', forward=FORWARD, validate=VALIDATE):
    return f'{declare} = {call};\n        {forward}\n        {validate}'


LIBRARY = ('library SafeCalls {\n    error Failed();\n'
           '    function push(address token, address to, uint256 amount) internal {\n'
           '        require(token.code.length > 0, Failed());\n'
           f'        (bool success, {DECLARE}) = {CALL};\n        {FORWARD}\n'
           '        require(returndata.length == 0 || abi.decode(returndata, (bool)), Failed());\n'
           '    }\n}\n')

# name, declarations, contract members, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('root-sequence', '', '', sequence(), None),
    ('code-length-check', '', '',
     'require(token.code.length > 0, NoCode());\n        ' + sequence(), None),
    ('library-helper', LIBRARY, '', 'counter += 1;\n        SafeCalls.push(token, to, amount);', None),
    ('reversed-offset', '', '',
     sequence(forward=FORWARD.replace('add(returndata, 0x20)', 'add(32, returndata)')), None),
    ('string-reason', '', '',
     sequence(validate='require(returndata.length == 0 || abi.decode(returndata, (bool)), "failed");'),
     None),
    ('transfer-from', '', '',
     sequence(call='token.call(abi.encodeCall(IToken.transferFrom, (msg.sender, to, amount)))'), None),
    ('code-length-branch', '', '',
     'if (token.code.length == 0) revert NoCode();\n        counter = to.code.length;', None),
    ('call-value', '', '',
     sequence(call='token.call{value: 1}(abi.encodeCall(IToken.transfer, (to, amount)))'),
     ('token.call{value: 1}', 0, 'FunctionCallOptions', 'external')),
    ('call-value-zero', '', '',
     sequence(call='token.call{value: 0}(abi.encodeCall(IToken.transfer, (to, amount)))'),
     ('token.call{value: 0}', 0, 'FunctionCallOptions', 'external')),
    ('call-gas', '', '',
     sequence(call='token.call{gas: 50000}(abi.encodeCall(IToken.transfer, (to, amount)))'),
     ('token.call{gas: 50000}', 0, 'FunctionCallOptions', 'external')),
    ('missing-returndata', '', '',
     f'(bool success, ) = {CALL};\n        require(success, TransferFailed());',
     ('(bool success, )', 0, 'VariableDeclarationStatement', 'bind')),
    ('missing-validation', '', '', f'(bool success, {DECLARE}) = {CALL};\n        {FORWARD}',
     ('(bool success,', 0, 'VariableDeclarationStatement', 'sequence')),
    ('strict-bool-validation', '', '',
     sequence(validate='require(abi.decode(returndata, (bool)), TransferFailed());'),
     ('require(abi.decode', 0, 'ExpressionStatement', 'validation')),
    ('unchecked-success', '', '',
     sequence(forward='require(success, TransferFailed());'),
     ('require(success', 0, 'ExpressionStatement', 'forward')),
    ('truncated-forward', '', '',
     sequence(forward=FORWARD.replace('mload(returndata)', '4')),
     ('if (!success)', 0, 'IfStatement', 'forward')),
    ('returndata-reuse', '', '', sequence() + '\n        counter = returndata.length;',
     ('counter = returndata.length;', 0, 'ExpressionStatement', 'reuse')),
    ('encode-with-selector', '', '',
     sequence(call='token.call(abi.encodeWithSelector(IToken.transfer.selector, to, amount))'),
     ('abi.encodeWithSelector(', 0, 'FunctionCall', 'encoding')),
    ('raw-calldata', '', '', sequence(call='token.call("")'),
     ('""', 0, 'Literal', 'encoding')),
    ('bytes-parameter', '', '',
     sequence(call='token.call(abi.encodeCall(IToken.approveAndCall, (to, "")))'),
     ('bytes memory data', 0, 'VariableDeclaration', 'param-type')),
    ('stateful-operand', '', '',
     sequence(call='token.call(abi.encodeCall(IToken.transfer, (to, bump())))'),
     ('bump()', 0, 'FunctionCall', 'order')),
    ('call-statement', '', '', f'{CALL};', ('token.call', 0, 'MemberAccess', 'placement')),
    ('helper-with-return', '', '', 'counter = send(token, to, amount);',
     ('token.call', 0, 'MemberAccess', 'placement')),
    ('staticcall', '', '',
     sequence(call='token.staticcall(abi.encodeCall(IToken.transfer, (to, amount)))'),
     ('token.staticcall', 0, 'MemberAccess', 'external')),
    ('delegatecall', '', '',
     sequence(call='token.delegatecall(abi.encodeCall(IToken.transfer, (to, amount)))'),
     ('token.delegatecall', 0, 'MemberAccess', 'external')),
    ('this-code-length', '', '', 'require(address(this).code.length > 0, NoCode());',
     ('address(this).code', 0, 'MemberAccess', 'this-code')),
    ('code-bytes', '', '', 'counter = uint8(token.code[0]);',
     ('token.code', 0, 'MemberAccess', 'code-read')),
]

HELPERS = (
    '    function bump() internal returns (uint256) {\n        counter += 1;\n        return counter;\n    }\n'
    '    function send(address token, address to, uint256 amount) internal returns (uint256) {\n'
    f'        (bool success, {DECLARE}) = {CALL};\n        {FORWARD}\n        {VALIDATE}\n'
    '        return amount;\n    }\n')


def source(declarations, members, statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            f'{INTERFACE}\n{declarations}\ncontract C {{\n'
            '    error NoCode();\n    error TransferFailed();\n    uint256 private counter;\n'
            f'    {members}\n'
            '    function checked(address token, address to, uint256 amount) external {\n'
            f'        {statements}\n    }}\n{HELPERS}}}\n')


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
              Path(tempfile.mkdtemp(prefix='external-code-low-level-call-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, declarations, members, statements, expected in CASES:
        if args.only and args.only != name:
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
  function checked(address,address,uint256)
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
        print(f'pass external-code-low-level-call-{name}', flush=True)
    print(f'code-length/low-level call rejections passed: {output}')


if __name__ == '__main__':
    main()
