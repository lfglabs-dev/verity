"""Located near-miss rejections and positive controls for typed-interface staticcalls.

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

ORACLE = 'interface IPriceOracle {\n    function price() external view returns (uint256);\n}\n'
MESSAGES = {
    'placement': 'typed interface staticcall must be a whole variable initializer, '
                 'assignment right-hand side or expression statement',
    'non-view': 'typed interface calls to non-view functions are outside this slice',
    'arguments': 'typed interface staticcall arguments are outside this slice',
    'return': 'typed interface staticcall must return a single uint256, bytes32 or bool',
    'receiver': 'typed interface call receiver must be an explicit interface conversion of an address',
    'external': 'external contract calls are outside this slice',
    'try': 'unsupported statement TryStatement',
}

# name, interface/contract declarations, contract members, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('declaration', ORACLE, '', 'uint256 v = IPriceOracle(oracle).price(); return v;', None),
    ('assignment', ORACLE, '', 'uint256 v; v = IPriceOracle(oracle).price(); return v;', None),
    ('discarded', ORACLE, '', 'IPriceOracle(oracle).price(); return 1;', None),
    ('storage-assignment', ORACLE, 'uint256 s;', 's = IPriceOracle(oracle).price(); return s;', None),
    ('this-address', ORACLE, '', 'uint256 v = IPriceOracle(address(this)).price(); return v;', None),
    ('helper-statement', ORACLE,
     'function q(address o) internal view returns (uint256) { uint256 v = IPriceOracle(o).price(); return v; }',
     'return q(oracle) + q(oracle);', None),
    ('non-view',
     'interface IPriceOracle {\n    function price() external returns (uint256);\n}\n', '',
     'uint256 v = IPriceOracle(oracle).price(); return v;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'non-view')),
    ('pure',
     'interface IPriceOracle {\n    function price() external pure returns (uint256);\n}\n', '',
     'uint256 v = IPriceOracle(oracle).price(); return v;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'non-view')),
    ('argument',
     'interface IPriceOracle {\n    function price(uint256) external view returns (uint256);\n}\n', '',
     'uint256 v = IPriceOracle(oracle).price(1); return v;',
     None),
    ('bool-return',
     'interface IPriceOracle {\n    function price() external view returns (bool);\n}\n', '',
     'bool b = IPriceOracle(oracle).price(); return b ? 1 : 0;',
     None),
    ('bytes32-return',
     'interface IPriceOracle {\n    function digest(uint256, address) external view returns (bytes32);\n}\n', '',
     'bytes32 d = IPriceOracle(oracle).digest(1, oracle); return uint256(d);',
     None),
    ('require-bool-gate',
     'interface IPriceOracle {\n    function allowed(uint256, uint256, uint256, uint256) external view returns (bool);\n}\n', '',
     'require(IPriceOracle(oracle).allowed(1, 2, 3, 4), "denied"); return 1;',
     None),
    ('require-or-bool-gate',
     'interface IPriceOracle {\n    function allowed(uint256, uint256, address) external view returns (bool);\n}\n', '',
     'require(msg.sender == oracle || IPriceOracle(oracle).allowed(1, 2, msg.sender), "denied"); return 1;',
     None),
    ('require-bytes32-eq',
     'struct Payload { address target; uint256 value; bytes data; uint256 nonce; }\n'
     'interface IPriceOracle {\n    function check(address, address, Payload memory, bytes memory) external view returns (bytes32);\n}\n',
     'bytes32 constant OK = keccak256("OK");',
     'Payload memory p = Payload(oracle, 7, hex"1234", 9); bytes memory sig = hex"abcd"; '
     'require(IPriceOracle(oracle).check(address(this), msg.sender, p, sig) == OK, "failed"); return 1;',
     None),
    ('unsupported-argument',
     'interface IPriceOracle {\n    function price(int128) external view returns (uint256);\n}\n', '',
     'uint256 v = IPriceOracle(oracle).price(1); return v;',
     ('IPriceOracle(oracle).price(1)', 0, 'FunctionCall', 'arguments')),
    ('narrow-return',
     'interface IPriceOracle {\n    function price() external view returns (uint128);\n}\n', '',
     'uint128 v = IPriceOracle(oracle).price(); return v;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'return')),
    ('two-returns',
     'interface IPriceOracle {\n    function price() external view returns (uint256, uint256);\n}\n', '',
     '(uint256 a, uint256 b) = IPriceOracle(oracle).price(); return a + b;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'external')),
    ('return-placement', ORACLE, '', 'return IPriceOracle(oracle).price();',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('binary-placement', ORACLE, '', 'uint256 v = IPriceOracle(oracle).price() + 1; return v;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('compound-assignment', ORACLE, '', 'uint256 v = 1; v += IPriceOracle(oracle).price(); return v;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('indexed-target', ORACLE, 'mapping(uint256 => uint256) m;',
     'm[1] = IPriceOracle(oracle).price(); return m[1];',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('conditional', ORACLE, '', 'uint256 v = oracle == address(0) ? 0 : IPriceOracle(oracle).price(); return v;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('nested-receiver', ORACLE, '',
     'uint256 v = IPriceOracle(address(uint160(IPriceOracle(oracle).price()))).price(); return v;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'placement')),
    ('helper-return', ORACLE,
     'function q(address o) internal view returns (uint256) { return IPriceOracle(o).price(); }',
     'uint256 v = q(oracle); return v;',
     ('IPriceOracle(o).price()', 0, 'FunctionCall', 'placement')),
    ('typed-local-receiver', ORACLE, '',
     'IPriceOracle feed = IPriceOracle(oracle); uint256 v = feed.price(); return v;',
     ('feed.price', 0, 'Identifier', 'receiver')),
    ('try-catch', ORACLE, '',
     'try IPriceOracle(oracle).price() returns (uint256 v) { return v; } catch { return 0; }',
     ('try', 0, 'TryStatement', 'try')),
    ('void-return',
     'interface IPriceOracle {\n    function price() external view;\n}\n', '',
     'IPriceOracle(oracle).price(); return 1;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'return')),
    ('payable-receiver', ORACLE, '', 'uint256 v = IPriceOracle(payable(oracle)).price(); return v;',
     ('IPriceOracle(payable(oracle))', 0, 'FunctionCall', 'receiver')),
    ('call-options', ORACLE, '', 'uint256 v = IPriceOracle(oracle).price{gas: 50000}(); return v;',
     ('IPriceOracle(oracle).price{gas: 50000}', 0, 'FunctionCallOptions', 'external')),
    ('contract-receiver',
     'contract PriceOracle {\n    function price() external view returns (uint256) { return 1; }\n}\n', '',
     'uint256 v = PriceOracle(oracle).price(); return v;',
     ('PriceOracle(oracle).price', 0, 'MemberAccess', 'external')),
    ('low-level-staticcall', ORACLE, '',
     '(bool ok, bytes memory data) = oracle.staticcall(abi.encodeCall(IPriceOracle.price, ())); '
     'return ok ? data.length : 0;',
     ('oracle.staticcall', 0, 'MemberAccess', 'external')),
]


def source(declarations, members, body):
    return (f'// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n{declarations}\n'
            f'contract C {{\n    {members}\n    function checked(address oracle) external returns (uint256) {{\n'
            f'        {body}\n    }}\n}}\n')


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
              Path(tempfile.mkdtemp(prefix='interface-static-call-rejections-', dir=root / '.lake')))
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
  function checked(address)
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
        print(f'pass interface-static-call-{name}', flush=True)
    print(f'interface staticcall rejections passed: {output}')


if __name__ == '__main__':
    main()
