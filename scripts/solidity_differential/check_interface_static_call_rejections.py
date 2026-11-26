"""Located near-miss rejections and positive controls for typed-interface staticcalls
and for external `try` of interface functions without return values, including the
post-CALL rule: storage reads, storage writes and logs after a closed CALL are admitted
(the model runs them against the world the callee committed).

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
    'key-order': 'typed interface staticcall in an assignment to an array element or computed key '
                 'is unsupported: solc evaluates the right-hand side first',
    'non-view': 'typed interface calls to non-view functions are outside this slice',
    'return': 'typed interface staticcall must return exactly one uint256, uint8..uint248, int256, bytes32, bytes4, bool or address',
    'tuple-return': 'typed interface staticcall tuple return elements must be uint256, uint8..uint248, int256, bytes32, bytes4, bool or address',
    'receiver': 'typed interface call receiver must be an explicit interface conversion of an address',
    'external': 'external contract calls are outside this slice',
    'try-returns': 'external try/catch of a function with several return values is unsupported',
    'try-return-type': 'external try/catch of a function returning int8 is unsupported',
    'try-clause': ('external try/catch supports exactly one catch clause: `catch { }` or '
                   '`catch (bytes memory reason) { }`'),
    'try-shape': 'unsupported statement TryStatement',
    'try-named': 'named arguments in an external try call are unsupported',
    'try-self': 'try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice',
}
HOOK = 'interface IHook {\n    function hook() external;\n}\n'

# name, interface/contract declarations, contract members, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('selector-comparison', ORACLE.replace('uint256', 'bytes4'), '',
     'return IPriceOracle(oracle).price() == IPriceOracle.price.selector;', None, 'bool'),
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
     'uint256 v = IPriceOracle(oracle).price(1); return v;', None),
    ('bool-return',
     'interface IPriceOracle {\n    function price() external view returns (bool);\n}\n', '',
     'bool b = IPriceOracle(oracle).price(); return b ? 1 : 0;', None),
    # One narrow unsigned word (#2914): solc's decoder reverts with no data on a word >= 2^N.
    ('uint16-return',
     'interface IPriceOracle {\n    function price() external view returns (uint16);\n}\n', '',
     'uint16 v = IPriceOracle(oracle).price(); return v;', None),
    ('uint128-return',
     'interface IPriceOracle {\n    function price() external view returns (uint128);\n}\n', '',
     'uint128 v = IPriceOracle(oracle).price(); return v;', None),
    ('uint248-discarded',
     'interface IPriceOracle {\n    function price() external view returns (uint248);\n}\n', '',
     'IPriceOracle(oracle).price(); return 1;', None),
    # Signed narrow, fixed-bytes and enum words keep the located rejection.
    ('narrow-return',
     'interface IPriceOracle {\n    function price() external view returns (int128);\n}\n', '',
     'int128 v = IPriceOracle(oracle).price(); return uint256(int256(v));',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'return')),
    ('bytes2-return',
     'interface IPriceOracle {\n    function price() external view returns (bytes2);\n}\n', '',
     'bytes2 v = IPriceOracle(oracle).price(); return uint256(uint16(v));',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'return')),
    ('enum-return',
     'interface IPriceOracle {\n    enum Kind { A, B }\n    function price() external view returns (Kind);\n}\n',
     '', 'return uint256(IPriceOracle(oracle).price());',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'return')),
    ('narrow-tuple-return',
     'interface IPriceOracle {\n    function price() external view returns (uint16, bool);\n}\n', '',
     '(uint16 a, bool b) = IPriceOracle(oracle).price(); return b ? a : 0;',
     None),
    ('two-returns',
     'interface IPriceOracle {\n    function price() external view returns (uint256, uint256);\n}\n', '',
     '(uint256 a, uint256 b) = IPriceOracle(oracle).price(); return a + b;',
     None),
    ('unsupported-tuple-return',
     'interface IPriceOracle {\n    function price() external view returns (int128, bool);\n}\n', '',
     '(int128 a, bool b) = IPriceOracle(oracle).price(); return b ? uint256(int256(a)) : 0;',
     ('IPriceOracle(oracle).price', 0, 'MemberAccess', 'tuple-return')),
    # Any expression position, in every contract (#2830, `InterfaceStaticCallStateCountChecks`).
    ('return-placement', ORACLE, '', 'return IPriceOracle(oracle).price();', None),
    ('binary-placement', ORACLE, '', 'uint256 v = IPriceOracle(oracle).price() + 1; return v;', None),
    ('compound-assignment', ORACLE, '', 'uint256 v = 1; v += IPriceOracle(oracle).price(); return v;',
     None),
    ('indexed-target', ORACLE, 'mapping(uint256 => uint256) m;',
     'm[1] = IPriceOracle(oracle).price(); return m[1];', None),
    ('conditional', ORACLE, '', 'uint256 v = oracle == address(0) ? 0 : IPriceOracle(oracle).price(); return v;',
     None),
    ('nested-receiver', ORACLE, '',
     'uint256 v = IPriceOracle(address(uint160(IPriceOracle(oracle).price()))).price(); return v;', None),
    ('helper-return', ORACLE,
     'function q(address o) internal view returns (uint256) { return IPriceOracle(o).price(); }',
     'uint256 v = q(oracle); return v;', None),
    ('typed-local-receiver', ORACLE, '',
     'IPriceOracle feed = IPriceOracle(oracle); uint256 v = feed.price(); return v;', None),
    # solc evaluates the right-hand side before the target's keys and bounds checks.
    ('computed-key-target', ORACLE, 'mapping(uint256 => uint256) m;',
     'm[uint256(uint160(oracle)) + 1] = IPriceOracle(oracle).price(); return 1;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'key-order')),
    ('computed-key-compound', ORACLE, 'mapping(uint256 => uint256) m;',
     'm[uint256(uint160(oracle)) + 1] += IPriceOracle(oracle).price(); return 1;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'key-order')),
    ('call-key-target', ORACLE, 'mapping(uint256 => uint256) m;',
     'm[IPriceOracle(oracle).price()] = 1; return 1;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'key-order')),
    ('helper-computed-key-target', ORACLE,
     'mapping(uint256 => uint256) m;\n'
     '    function q(address o) internal view returns (uint256) { return IPriceOracle(o).price(); }',
     'm[uint256(uint160(oracle)) + 1] = q(oracle); return 1;',
     ('q(oracle)', 0, 'Identifier', 'key-order')),
    ('modifier-computed-key-target', ORACLE,
     'mapping(uint256 => uint256) m;\n'
     '    modifier priced(address o) { require(IPriceOracle(o).price() == 7); _; }\n'
     '    function q(address o) internal view priced(o) returns (uint256) { return 1; }',
     'm[uint256(uint160(oracle)) + 1] = q(oracle); return 1;',
     ('q(oracle)', 0, 'Identifier', 'key-order')),
    ('modifier-argument-computed-key-target', ORACLE,
     'mapping(uint256 => uint256) m;\n'
     '    modifier atLeast(uint256 v) { require(v > 0); _; }\n'
     '    function q(address o) internal view atLeast(IPriceOracle(o).price()) returns (uint256) '
     '{ return 1; }',
     'm[uint256(uint160(oracle)) + 1] = q(oracle); return 1;',
     ('q(oracle)', 0, 'Identifier', 'key-order')),
    # `super` resolves from the callee being inspected, not the root frame.
    ('super-computed-key-target', ORACLE +
     'abstract contract Base {\n'
     '    function f(address o) internal view virtual returns (uint256) { return IPriceOracle(o).price(); }\n'
     '}\n'
     'abstract contract Middle is Base {\n'
     '    function f(address o) internal view virtual override returns (uint256) { return super.f(o); }\n'
     '}\n',
     'mapping(uint256 => uint256) m;',
     'm[uint256(uint160(oracle)) + 1] = f(oracle); return 1;',
     ('f(oracle)', 0, 'Identifier', 'key-order'), 'uint256', ' is Middle'),
    # A function value passed to a callee is followed; an unresolved pointer counts as a call.
    ('pointer-argument-computed-key-target', ORACLE,
     'mapping(uint256 => uint256) m;\n'
     '    function g(address o) internal view returns (uint256) { return IPriceOracle(o).price(); }\n'
     '    function callPtr(function (address) internal view returns (uint256) p, address o)\n'
     '        internal view returns (uint256) { return p(o); }',
     'm[uint256(uint160(oracle)) + 1] = callPtr(g, oracle); return 1;',
     ('g, oracle)', 0, 'Identifier', 'key-order')),
    ('tuple-target', ORACLE, '',
     'uint256 v; uint256 w; (v, w) = (IPriceOracle(oracle).price(), 1); return v + w;', None),
    ('array-target', ORACLE, 'uint256[] a;',
     'a[0] = IPriceOracle(oracle).price(); return 1;',
     ('IPriceOracle(oracle).price()', 0, 'FunctionCall', 'key-order')),
    ('try-catch', ORACLE, '',
     'try IPriceOracle(oracle).price() returns (uint256 v) { return v; } catch { return 0; }', None),
    ('try-catch-unnamed-result', ORACLE, '',
     'try IPriceOracle(oracle).price() { return 1; } catch (bytes memory reason) '
     '{ return reason.length; }', None),
    ('try-catch-two-returns',
     'interface IPriceOracle {\n    function price() external view returns (uint256, uint256);\n}\n',
     '', 'try IPriceOracle(oracle).price() returns (uint256 v, uint256) { return v; } '
     'catch { return 0; }',
     ('try', 0, 'TryStatement', 'try-returns')),
    ('try-catch-narrow-signed',
     'interface IPriceOracle {\n    function price() external view returns (int8);\n}\n',
     '', 'try IPriceOracle(oracle).price() returns (int8) { return 1; } catch { return 0; }',
     ('try', 0, 'TryStatement', 'try-return-type')),
    ('try-void', HOOK, '', 'try IHook(oracle).hook() { return 1; } catch { return 0; }', None),
    # The callee may re-enter. State written before the call is trailing; storage reads,
    # writes and logs after it (clauses or continuation) run against the committed world.
    ('try-void-empty-clauses', HOOK, 'uint256 s;',
     's = 1; try IHook(oracle).hook() {} catch {} return 1;', None),
    ('void-call-after-write', HOOK, 'uint256 s;', 's = 1; IHook(oracle).hook(); return 1;', None),
    ('try-void-statement-shape', HOOK, 'uint256 s;',
     's += 1; try IHook(oracle).hook() { s = 2; } catch { s += 1000; } s += 1; return s;', None),
    ('try-void-success-write', HOOK, 'uint256 s;',
     'try IHook(oracle).hook() { s = 1; } catch {} return 1;', None),
    ('try-void-failure-write', HOOK, 'uint256 s;',
     'try IHook(oracle).hook() {} catch { s = 1; } return 1;', None),
    ('try-void-continuation-read', HOOK, 'uint256 s;',
     'try IHook(oracle).hook() {} catch {} return s;', None),
    ('try-void-checked-arithmetic', HOOK, 'uint256 s;',
     's = 1; uint256 n = 1; try IHook(oracle).hook() { n = n + 1; } catch { return 0; } '
     'return n * 3;', None),
    # The self-call form rejects at the `try` in every contract, whatever its state count
    # (here two state variables; `try-self` below has none).
    ('try-self-success-write', HOOK, 'uint256 s;\n    uint256 t;\n    function hook() external {}',
     'try this.hook() { s = 1; } catch {} return 1;',
     ('try', 0, 'TryStatement', 'try-self')),
    ('void-call-then-write', HOOK, 'uint256 s;', 'IHook(oracle).hook(); s = 1; return 1;', None),
    ('void-call-then-read', HOOK, 'uint256 s;', 'IHook(oracle).hook(); return s;', None),
    ('void-call-then-log', HOOK, 'event Called();',
     'IHook(oracle).hook(); emit Called(); return 1;', None),
    ('try-void-error-clause', HOOK, '',
     'try IHook(oracle).hook() { return 1; } catch Error(string memory) { return 2; } '
     'catch { return 0; }',
     ('try', 0, 'TryStatement', 'try-clause')),
    ('try-void-bytes-clause', HOOK, '',
     'try IHook(oracle).hook() { return 1; } catch (bytes memory) { return 0; }', None),
    ('try-void-panic-clause', HOOK, '',
     'try IHook(oracle).hook() { return 1; } catch Panic(uint256) { return 2; }',
     ('try', 0, 'TryStatement', 'try-clause')),
    ('try-void-named-arguments',
     'interface IHook {\n    function hook(uint256 amount) external;\n}\n', '',
     'try IHook(oracle).hook({amount: 1}) { return 1; } catch { return 0; }',
     None),
    ('try-void-named-competing-panics',
     'interface IHook {\n    function hook(uint256 a, uint256 b) external;\n}\n', '',
     'uint256 x = uint256(uint160(oracle)); try IHook(oracle).hook({b: 1 / x, a: x - 1}) { return 1; } catch { return 0; }',
     ('IHook(oracle).hook({b: 1 / x, a: x - 1})', 0, 'FunctionCall', 'try-named')),
    ('try-void-call-options', HOOK, '',
     'try IHook(oracle).hook{gas: 50000}() { return 1; } catch { return 0; }',
     ('try', 0, 'TryStatement', 'try-shape')),
    ('try-self', HOOK, 'function hook() external {}',
     'try this.hook() { return 1; } catch { return 0; }',
     ('try', 0, 'TryStatement', 'try-self')),
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


def source(declarations, members, body, result_type='uint256', bases=''):
    return (f'// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n{declarations}\n'
            f'contract C{bases} {{\n    {members}\n    function checked(address oracle) external returns ({result_type}) {{\n'
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
    for name, declarations, members, body, expected, *result_type in CASES:
        if args.only and args.only not in name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(declarations, members, body, *result_type)
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
