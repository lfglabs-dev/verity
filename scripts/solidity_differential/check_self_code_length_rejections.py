"""Located near-miss rejections and positive controls for `address(this).code.length`.

Only a comparison of the executing account's code length with zero is admitted:
the routes' codes differ, but both have code exactly when the account is
deployed. Each case is imported on its own. A positive control must elaborate
and leave an olean; a near miss must fail with the exact `Fixture.sol:line:column`
position of the named node, its construct and message, and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'this-length': 'code length of the executing contract is unsupported outside a zero test',
    'self-alias-length': 'code length of an account that may be the executing contract is unsupported',
    'code-read': 'external contract code reads are outside this slice',
}

# name, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('equal-zero', 'flag = address(this).code.length == 0;', None),
    ('not-equal-zero', 'flag = address(this).code.length != 0;', None),
    ('greater-than-zero', 'flag = address(this).code.length > 0;', None),
    ('zero-equal', 'flag = 0 == address(this).code.length;', None),
    ('zero-not-equal', 'flag = 0 != address(this).code.length;', None),
    ('zero-less-than', 'flag = 0 < address(this).code.length;', None),
    ('parenthesized', 'flag = (address(this).code.length) == (0);', None),
    ('hex-zero', 'flag = address(this).code.length != 0x0;', None),
    ('payable-this', 'flag = payable(address(this)).code.length == 0;', None),
    ('require-code', 'require(address(this).code.length > 0, NoCode());\n        counter += 1;', None),
    ('if-no-code', 'if (address(this).code.length == 0) counter += 1;', None),
    ('short-circuit', 'flag = counter == 1 && address(this).code.length == 0;', None),
    ('parenthesized-this', 'flag = (address(this)).code.length != 0;', None),
    # The length itself, or a comparison that is not a zero test, differs between routes.
    ('value', 'counter = address(this).code.length;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('bound-local', 'uint256 size = address(this).code.length;\n        flag = size == 0;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('equal-one', 'flag = address(this).code.length == 1;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('greater-or-equal-zero', 'flag = address(this).code.length >= 0;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('less-than-zero-mirrored', 'flag = 0 > address(this).code.length;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('less-or-equal-zero', 'flag = address(this).code.length <= 0;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('arithmetic-zero', 'flag = address(this).code.length + 0 == 0;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('zero-constant', 'flag = address(this).code.length == ZERO;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    ('compare-lengths', 'flag = address(this).code.length == msg.sender.code.length;',
     ('address(this).code', 0, 'MemberAccess', 'this-length')),
    # The admitted shape is syntactic on `address(this)`; an alias still rejects.
    ('self-alias', 'address self = address(this);\n        flag = self.code.length == 0;',
     ('self.code', 0, 'MemberAccess', 'self-alias-length')),
    # Inline assembly reads the length itself: the executing contract rejects there too.
    ('yul-self', 'uint256 size;\n        assembly {\n            size := extcodesize(address())\n'
     '        }\n        counter = size;',
     ('extcodesize(address())', 0, 'YulFunctionCall', 'self-alias-length')),
    ('yul-self-zero-test', 'bool empty;\n        assembly {\n            empty := iszero(extcodesize(address()))\n'
     '        }\n        flag = empty;',
     ('extcodesize(address())', 0, 'YulFunctionCall', 'self-alias-length')),
    ('yul-self-local', 'uint256 size;\n        assembly {\n            let self := address()\n'
     '            size := extcodesize(self)\n        }\n        counter = size;',
     ('extcodesize(self)', 0, 'YulFunctionCall', 'self-alias-length')),
    ('yul-self-compound', 'uint256 size;\n        assembly {\n            size := extcodesize(or(address(), 0))\n'
     '        }\n        counter = size;',
     ('extcodesize(or(address(), 0))', 0, 'YulFunctionCall', 'self-alias-length')),
    ('yul-foreign', 'uint256 size;\n        assembly {\n            size := extcodesize(caller())\n'
     '        }\n        counter = size;', None),
    ('yul-foreign-compound', 'uint256 size;\n        assembly {\n'
     '            size := extcodesize(and(caller(), sub(shl(160, 1), 1)))\n'
     '        }\n        counter = size;', None),
    ('this-code-copy', 'flag = address(this).code.length == 0 && address(this).code[0] == 0;',
     ('address(this).code[0]', 0, 'MemberAccess', 'code-read')),
]


def source(statements):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'contract C {\n'
            '    uint256 internal constant ZERO = 0;\n'
            '    error NoCode();\n'
            '    uint256 private counter;\n    bool private flag;\n'
            '    function checked() external {\n'
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
              Path(tempfile.mkdtemp(prefix='self-code-length-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, statements, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(statements)
        (directory / 'Fixture.sol').write_text(text)
        compile_guard = ('import Compiler.Codegen\n' if expected is None else '')
        compile_check = ('#guard (Compiler.CompilationModel.compile tested.model [0x1] .osaka).isOk\n'
                         if expected is None else '')
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
{compile_guard}solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked()
{compile_check}''')
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
        print(f'pass self-code-length-{name}', flush=True)
    print(f'self code-length rejections passed: {output}')


if __name__ == '__main__':
    main()
