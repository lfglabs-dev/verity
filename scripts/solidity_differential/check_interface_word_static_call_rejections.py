"""Located near-miss rejections and positive controls for typed-interface word staticcalls.

Covers static word arguments, `bool`/`bytes32` returns and short-circuit /
`require`-condition placement. Each case is imported on its own. A positive
control must elaborate and leave an olean; a near miss must fail with the exact
`Fixture.sol:line:column` position of the named node, its construct and message,
and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from .check_interface_static_call_rejections import location

WORD = ('interface IWord {\n'
        '    function allowed(address account) external view returns (bool);\n'
        '    function quote(uint256 amount, bytes32 tag) external view returns (uint256);\n'
        '    function tagOf(address account, bool flag) external view returns (bytes32);\n'
        '}\n')
ERROR = 'error Gated();'
MESSAGES = {
    'placement': 'typed interface staticcall must be a whole variable initializer, '
                 'assignment right-hand side, expression statement, require condition or '
                 'short-circuit operand of one',
    'parameters': 'typed interface staticcall parameters must be address, uint256, bytes32 or bool',
    'return': 'typed interface staticcall must return exactly one uint256, bytes32 or bool',
    'named': 'named call arguments are outside this slice',
    'effects': 'typed interface staticcall arguments must lower without side effects',
    'non-view': 'typed interface calls to non-view functions are outside this slice',
    'external': 'external contract calls are outside this slice',
}


def single(signature, returns='uint256'):
    return f'interface IWord {{\n    function f({signature}) external view returns ({returns});\n}}\n'


def mismatch(argument, parameter):
    return f'typed interface staticcall argument type {argument} differs from parameter type {parameter}'


# name, declarations, contract members, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key or literal)
CASES = [
    ('address-argument', WORD, '', 'bool b = IWord(oracle).allowed(msg.sender); return b ? 1 : 0;', None),
    ('word-arguments', WORD, '', 'uint256 v = IWord(oracle).quote(x, bytes32(x)); return v;', None),
    ('literal-argument', WORD, '', 'uint256 v = IWord(oracle).quote(7, bytes32(0)); return v;', None),
    ('bool-argument', WORD, '',
     'bytes32 t = IWord(oracle).tagOf(oracle, x > 1); return uint256(t);', None),
    ('or-operand', WORD, '',
     'bool b = oracle == address(0) || IWord(oracle).allowed(msg.sender); return b ? 1 : 0;', None),
    ('and-operands', WORD, '',
     'bool b = IWord(oracle).allowed(msg.sender) && IWord(oracle).allowed(oracle); return b ? 1 : 0;',
     None),
    ('require-condition', WORD, ERROR,
     'require(oracle == address(0) || IWord(oracle).allowed(msg.sender), Gated()); return x;', None),
    ('require-string', WORD, '',
     'require(IWord(oracle).allowed(msg.sender), "gated"); return x;', None),
    ('narrow-parameter', single('uint128 amount'), '',
     'uint256 v = IWord(oracle).f(1); return v;',
     ('IWord(oracle).f(1)', 0, 'FunctionCall', 'parameters')),
    ('payable-parameter', single('address payable account'), '',
     'uint256 v = IWord(oracle).f(payable(oracle)); return v;',
     ('IWord(oracle).f(payable(oracle))', 0, 'FunctionCall', 'parameters')),
    ('bytes-parameter', single('bytes calldata data'), '',
     'uint256 v = IWord(oracle).f(""); return v;',
     ('IWord(oracle).f("")', 0, 'FunctionCall', 'parameters')),
    ('bytes4-parameter', single('bytes4 tag'), '',
     'uint256 v = IWord(oracle).f(bytes4(0)); return v;',
     ('IWord(oracle).f(bytes4(0))', 0, 'FunctionCall', 'parameters')),
    ('address-return', single('uint256 amount', 'address'), '',
     'address a = IWord(oracle).f(x); return uint256(uint160(a));',
     ('IWord(oracle).f', 0, 'MemberAccess', 'return')),
    ('narrow-argument', WORD, '',
     'uint8 small = uint8(x); uint256 v = IWord(oracle).quote(small, bytes32(0)); return v;',
     ('small, bytes32(0)', 0, 'Identifier', mismatch('uint8', 'uint256'))),
    ('checked-argument', WORD, '',
     'uint256 v = IWord(oracle).quote(x + 1, bytes32(0)); return v;',
     ('x + 1', 0, 'BinaryOperation', 'effects')),
    # Named arguments in declaration order lower as the positional call; any other order
    # keeps its located rejection.
    ('named-arguments', WORD, '',
     'bool b = IWord(oracle).allowed({account: oracle}); return b ? 1 : 0;', None),
    ('named-arguments-declared-order', WORD, '',
     'uint256 v = IWord(oracle).quote({amount: x, tag: bytes32(x)}); return v;', None),
    ('named-arguments-reordered', WORD, '',
     'uint256 v = IWord(oracle).quote({tag: bytes32(x), amount: x}); return v;',
     ('IWord(oracle).quote({tag: bytes32(x), amount: x})', 0, 'FunctionCall', 'named')),
    ('nested-argument', WORD, '',
     'uint256 v = IWord(oracle).quote(IWord(oracle).quote(1, bytes32(0)), bytes32(0)); return v;',
     ('IWord(oracle).quote(1, bytes32(0))', 0, 'FunctionCall', 'placement')),
    ('not-operand', WORD, ERROR,
     'require(!IWord(oracle).allowed(msg.sender), Gated()); return x;',
     ('IWord(oracle).allowed(msg.sender)', 0, 'FunctionCall', 'placement')),
    ('equality-operand', WORD, ERROR,
     'require(IWord(oracle).quote(1, bytes32(0)) == 5, Gated()); return x;',
     ('IWord(oracle).quote(1, bytes32(0))', 0, 'FunctionCall', 'placement')),
    ('conditional-operand', WORD, '',
     'bool b = x > 1 ? IWord(oracle).allowed(oracle) : false; return b ? 1 : 0;',
     ('IWord(oracle).allowed(oracle)', 0, 'FunctionCall', 'placement')),
    ('if-condition', WORD, '',
     'if (IWord(oracle).allowed(oracle)) { return 1; } return 0;',
     ('IWord(oracle).allowed(oracle)', 0, 'FunctionCall', 'placement')),
    ('error-argument', WORD, 'error Coded(uint256 code);',
     'require(x > 1, Coded(IWord(oracle).quote(1, bytes32(0)))); return x;',
     ('IWord(oracle).quote(1, bytes32(0))', 0, 'FunctionCall',
      'custom-error arguments currently require literals or scalar bindings')),
    ('non-view-call', 'interface IWord {\n    function f(address a) external returns (bool);\n}\n', '',
     'bool b = IWord(oracle).f(oracle); return b ? 1 : 0;',
     ('IWord(oracle).f', 0, 'MemberAccess', 'non-view')),
    ('value-option', 'interface IWord {\n    function f(address a) external payable returns (bool);\n}\n', '',
     'bool b = IWord(oracle).f{value: 1}(oracle); return b ? 1 : 0;',
     ('IWord(oracle).f{value: 1}', 0, 'FunctionCallOptions', 'external')),
]


def source(declarations, members, body):
    return (f'// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n{declarations}\n'
            f'contract C {{\n    {members}\n'
            f'    function checked(address oracle, uint256 x) external returns (uint256) {{\n'
            f'        {body}\n    }}\n}}\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='interface-word-static-call-rejections-',
                                    dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, declarations, members, body, expected in CASES:
        if args.only and args.only not in name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(declarations, members, body)
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
            marker, occurrence, construct, key = expected
            line, column = location(text, marker, occurrence)
            diagnostic = (f'Fixture.sol:{line}:{column}: {construct}: '
                          f'[solidity-import:unsupported] {MESSAGES.get(key, key)}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass interface-word-static-call-{name}', flush=True)
    print(f'interface word staticcall rejections passed: {output}')


if __name__ == '__main__':
    main()
