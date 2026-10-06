"""Exact scalar storage controls and located near-miss rejections."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path.cwd()
    output = Path(tempfile.mkdtemp(prefix='storage-rejections-', dir=root / '.lake'))
    cases = [
        ('helper-for', 'function helper(uint256 n) internal pure returns (uint256) { uint256 total; for (uint256 i = 0; i < n; i++) { total = total + i; } return total; }', 'return helper(x);', 'uint256', None),
        ('helper-for-return', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i++) { return i; } return 0; }', 'return helper(x);', 'uint256', 'return inside an inlined helper loop'),
        ('helper-for-conditional-return', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i++) { if (i == 1) return i; } return 0; }', 'return helper(x);', 'uint256', 'return inside an inlined helper loop'),
        ('helper-for-break', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i++) { break; } return 0; }', 'return helper(x);', 'uint256', 'unsupported helper loop statement Break'),
        ('helper-for-continue', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i++) { continue; } return 0; }', 'return helper(x);', 'uint256', 'unsupported helper loop statement Continue'),
        ('helper-for-step', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i += 2) {} return 0; }', 'return helper(x);', 'uint256', 'increment its counter by one'),
        ('helper-for-inclusive', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i <= n; i++) {} return 0; }', 'return helper(x);', 'uint256', 'condition must be counter < bound'),
        ('helper-for-counter', 'function helper(uint256 n) internal pure returns (uint256) { for (uint256 i = 0; i < n; i++) { i = 2; } return 0; }', 'return helper(x);', 'uint256', 'counter must not be assigned'),
        ('helper-for-bound', 'function helper(uint256 n) internal pure returns (uint256) { uint256 bound = n; for (uint256 i = 0; i < bound; i++) { bound = 0; } return 0; }', 'return helper(x);', 'uint256', 'bound must be a literal'),
        ('helper-for-nested-bound', 'function helper(uint256 n) internal pure returns (uint256) { uint256 bound = n; for (uint256 i = 0; i < bound; i++) { for (uint256 j = 0; j < 1; bound++) {} } return 0; }', 'return helper(x);', 'uint256', 'bound must be a literal'),
        ('for-scalar', '', 'uint256 total; for (uint256 i = 0; i < 3; i++) { total = total + i; } return total;', 'uint256', None),
        ('for-nonzero', '', 'for (uint256 i = 1; i < 3; i++) {} return x;', 'uint256', 'counter must start at 0'),
        ('for-inclusive', '', 'for (uint256 i = 0; i <= 3; i++) {} return x;', 'uint256', 'condition must be counter < bound'),
        ('for-variable-step', '', 'for (uint256 i = 0; i < 3; i += 2) {} return x;', 'uint256', 'increment its counter by one'),
        ('for-counter-write', '', 'for (uint256 i = 0; i < 3; i++) { i = 2; } return x;', 'uint256', 'counter must not be assigned'),
        ('for-bound-write', '', 'uint256 n = x; for (uint256 i = 0; i < n; i++) { n = 0; } return x;', 'uint256', 'bound must be a literal'),
        ('for-nested-bound-step', '', 'uint256 n = x; for (uint256 i = 0; i < n; i++) { for (uint256 j = 0; j < 1; n++) {} } return x;', 'uint256', 'bound must be a literal'),
        ('for-break', '', 'for (uint256 i = 0; i < 3; i++) { break; } return x;', 'uint256', 'unsupported statement Break'),
        ('for-continue', '', 'for (uint256 i = 0; i < 3; i++) { continue; } return x;', 'uint256', 'unsupported statement Continue'),
        ('default-uint', '', 'uint256 zero; return x + zero;', 'uint256', None),
        ('default-narrow', '', 'uint8 zero; return uint256(zero);', 'uint256', None),
        ('default-address', '', 'address zero; return zero;', 'address', None),
        ('default-bool', '', 'bool zero; return zero;', 'bool', None),
        ('default-bytes32', '', 'bytes32 zero; return zero;', 'bytes32', None),
        ('default-signed', '', 'int256 zero; return zero;', 'int256', 'unsupported default local type int256'),
        ('default-bytes', '', 'bytes memory zero; return x;', 'uint256', 'uninitialized reference locals'),
        ('default-array', '', 'uint256[] memory zero; return x;', 'uint256', 'uninitialized reference locals'),
        ('modulo-unsigned', '', 'return x % 7;', 'uint256', None),
        ('modulo-narrow', '', 'return uint8(x) % uint8(7);', 'uint256', None),
        ('modulo-signed', '', 'return uint256(int256(x) % int256(7));', 'uint256', 'unsupported cast target int256'),
        ('modulo-rational-constant', '', 'return x + (7 % 2);', 'uint256', 'unsupported operand type'),
        ('inline-constant-array', 'uint256 constant A = 3;', 'return [A, 7][x];', 'uint256', None),
        ('inline-constant-array-narrow', 'uint8 constant A = 255; uint8 constant B = 0;', 'return [A, B][x];', 'uint256', None),
        ('inline-array-variable', '', 'return [x, 7][x];', 'uint256', 'inline array elements must be exact natural constants'),
        ('inline-array-guarded-element', '', 'return [uint256(1), 100 / x][x];', 'uint256', 'inline array elements must be exact natural constants'),
        ('inline-array-bool', '', 'return [true, false][x];', 'bool', 'inline constant arrays require unsigned scalar elements'),
        ('inline-array-signed', '', 'return uint256([int256(-1), int256(2)][x]);', 'uint256', 'inline constant arrays require unsigned scalar elements'),
        ('inline-array-escape', '', 'uint256[2] memory a = [uint256(1), 2]; return a[x];', 'uint256', 'inline arrays are outside this slice'),
        ('if-else', '', 'if (x > 1) { return 1; } else { return 2; }', 'uint256', None),
        ('if-early-return', 'uint256 value;', 'if (x == 0) return 0; value = x; return value;', 'uint256', None),
        ('if-helper-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) return 1; require(y == 0, "one"); return 0; }', 'return h(x);', 'uint256', None),
        ('if-bare-return', 'uint256 value;', 'if (x == 0) return; value = x;', '', 'bare return requires'),
        ('if-dead-remainder', '', 'if (false) { return x % 2; } return x;', 'uint256', None),
        ('if-dead-rational-remainder', '', 'if (false) { return x % (6 / 3); } return x;', 'uint256', 'unsupported operand type'),
        ('if-after-both-return', 'uint256 value;', 'if (x > 1) { return 1; } else { return 2; } value = x;', 'uint256', 'statement after root return'),
        ('if-helper-missing-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) return 1; }', 'return h(x);', 'uint256', 'does not return on every path'),
        ('if-helper-after-both-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) { return 1; } else { return 2; } require(y > 0, "dead"); }', 'return h(x);', 'uint256', 'statement after helper result'),
        ('if-helper-effect', 'uint256 value; function h(uint256 y) internal returns (uint256) { if (y > 1) { value = y; } return y; }', 'return h(x);', 'uint256', 'only builtin require calls'),
        ('if-unchecked-branch', '', 'if (x > 1) { unchecked { return x - 2; } } return x;', 'uint256', 'unsupported statement UncheckedBlock'),
        ('logical-or', '', 'return x == 0 || 100 / x > 1;', 'bool', None),
        ('logical-and', '', 'return x != 0 && 100 / x > 1;', 'bool', None),
        ('logical-dead-effect', 'uint256 value; function bump() internal returns (bool) { value = 1; return true; }', 'return true || bump();', 'bool', 'only builtin require calls'),
        ('logical-dead-remainder', '', 'return false && x % 2 == 0;', 'bool', None),
        ('logical-dead-rational-remainder', '', 'return false && x % (6 / 3) == 0;', 'bool', 'unsupported operand type'),
        ('logical-external', 'function probe() external pure returns (bool) { return true; }', 'return true || this.probe();', 'bool', 'unresolved builtin identifier'),

        ('effectful-helper', 'uint256 value; function bump() internal returns (uint256) { value = value + 1; return value; }', 'return bump() + bump();', 'uint256', 'only builtin require calls'),
        ('helper-argument-effects', 'uint256 value; function bump() internal returns (uint256) { value = value + 1; return value; } function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }', 'return add(bump(), bump());', 'uint256', 'only builtin require calls'),
        ('bare-return', 'uint256 value;', 'value = x; return;', '', 'bare return requires'),
        ('scalar', 'uint256 value;', 'value = x; return value;', 'uint256', None),
        ('packed', 'uint128 low; uint128 high;', 'high = uint128(x); return high;', 'uint128', None),
        ('delete', 'uint256 value;', 'delete value; return value;', 'uint256', None),
        ('void', 'uint256 value;', 'value = x;', '', None),
        ('bool', 'bool value;', 'value = true; return x;', 'uint256', 'unsupported scalar storage type'),
        ('signed', 'int256 value;', 'value = int256(x); return x;', 'uint256', 'unsupported scalar storage type'),
        ('bytes16', 'bytes16 value;', 'delete value; return x;', 'uint256', 'unsupported scalar storage type'),
        ('array', 'uint256[] value;', 'delete value; return x;', 'uint256', 'unsupported storage encoding'),
        ('mapping-target', 'mapping(uint256 => uint256) value;', 'value[x] = x; return x;', 'uint256', None),
        ('mapping-bool', 'mapping(uint256 => bool) value;', 'value[x] = true; return value[x];', 'bool', None),
        ('mapping-delete', 'mapping(uint256 => uint128) value;', 'value[x] = uint128(x); delete value[x]; return value[x];', 'uint128', None),
        ('mapping-two-keys', 'mapping(address => mapping(bytes32 => uint128)) value;', 'value[msg.sender][bytes32(x)] = uint128(x); return value[msg.sender][bytes32(x)];', 'uint128', None),
        ('mapping-three-keys', 'mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256))) value;', 'return value[x][x][x];', 'uint256', 'unsupported scalar mapping value encoding'),
        ('mapping-signed-value', 'mapping(uint256 => int256) value;', 'return value[x];', 'int256', 'unsupported scalar mapping value type'),
        ('mapping-bytes16-value', 'mapping(uint256 => bytes16) value;', 'return value[x];', 'bytes16', 'unsupported scalar mapping value type'),
        ('mapping-signed-key', 'mapping(int256 => uint256) value;', 'return value[0];', 'uint256', 'unsupported mapping key'),
        ('mapping-narrow-key', 'mapping(uint128 => uint256) value;', 'return value[uint128(x)];', 'uint256', 'unsupported mapping key'),
        ('mapping-dynamic-value', 'mapping(uint256 => bytes) value;', 'delete value[x]; return x;', 'uint256', 'unsupported mapping value encoding'),
        ('mapping-compound', 'mapping(uint256 => uint256) value;', 'value[x] += x; return value[x];', 'uint256', 'only scalar storage assignment'),
        ('literal-constant-product', '', 'return x + (2 * 3);', 'uint256', None),
        ('literal-constant-product-units', '', 'return x + (100 * 365 days);', 'uint256', None),
        ('literal-fractional-product', '', 'return x + (.5 * 2);', 'uint256', 'fractional numeric literal'),
        ('literal-rational-division', '', 'return x + (6 / 3);', 'uint256', 'unsupported operand type'),
        ('literal-product-oversized-intermediate', '', 'return x + (57896044618658097711785492504343953926634992332820282019728792003956564819968 * 2 / 2);', 'uint256', 'unsupported integer constant product'),
        ('literal-leading-dot', '', 'return .5 hours;', 'uint256', None),
        ('literal-separators', '', 'return 1_000 + 0x2_0;', 'uint256', None),
        ('literal-fractional-result', '', 'return x + (.5 / .5);', 'uint256', 'fractional numeric literal'),
        ('literal-bool-constant', 'bool constant ENABLED = true;', 'return ENABLED;', 'bool', None),
        ('literal-narrow-constant', 'uint8 constant LIMIT = 255;', 'return x + LIMIT;', 'uint256', None),
        ('literal-bytes-constant', 'bytes32 constant BAD = bytes32(uint256(1));', 'return uint256(BAD);', 'uint256', 'unsupported numeric constant type bytes32'),
        ('literal-address-constant', 'address constant BAD = address(1);', 'return uint256(uint160(BAD));', 'uint256', 'unsupported numeric constant type address'),
        ('literal-signed-constant', 'int256 constant BAD = -1;', 'return uint256(BAD);', 'uint256', 'unsupported numeric constant type int256'),
        ('literal-named-rational', 'uint256 constant STEP = (1 days / 7) * 7;', 'return x + STEP;', 'uint256', 'unsupported operand type'),
        ('literal-constant-fraction', '', 'return x + (1 days / 7) * 7;', 'uint256', 'unsupported operand type'),
        ('literal-oversized-intermediate', '', 'return x + (2**256 / 2);', 'uint256', 'unsupported operand type'),
        ('literal-denomination', '', 'return 1 ether;', 'uint256', None),
        ('literal-string', '', 'return bytes32("123");', 'bytes32', 'unsupported non-numeric literal'),
        ('struct-target', 'struct Pair { uint128 a; uint128 b; } Pair value;', 'value.a = uint128(x); return x;', 'uint256', 'only a resolved scalar storage identifier'),
        ('compound', 'uint256 value;', 'value += x; return value;', 'uint256', 'only scalar storage assignment'),
        ('increment', 'uint256 value;', 'value++; return value;', 'uint256', 'only scalar storage assignment'),
        ('local', '', 'uint256 value = 0; value = x; return value;', 'uint256', None),
        ('local-delete', '', 'uint256 value = x; delete value; return value;', 'uint256', None),
        ('local-compound', '', 'uint256 value = 0; value += x; return value;', 'uint256', 'only scalar storage assignment'),
        ('local-increment', '', 'uint256 value = 0; value++; return value;', 'uint256', 'only scalar storage assignment'),
        ('parameter-write', '', 'x = 0; return x;', 'uint256', 'only materialized scalar locals are writable'),
        ('helper-parameter-write', 'function h(uint256 y) internal pure returns (uint256) { y = 0; return y; }', 'uint256 local = x; return h(local);', 'uint256', 'only builtin require calls'),
        ('local-array-write', '', 'uint256[2] memory a; a[0] = x; return x;', 'uint256', 'uninitialized reference locals'),
        ('named-return', 'uint256 value;', 'value = x;', 'uint256 result', 'return'),
    ]
    for name, fields, body, returns, expected in cases:
        directory = output / name
        directory.mkdir()
        result_clause = f'returns ({returns})' if returns else ''
        (directory / 'Fixture.sol').write_text(f'''pragma solidity 0.8.34;
contract C {{
 {fields}
 function checked(uint256 x) external {result_clause} {{
  {body}
 }}
}}
''')
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked(uint256)
''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                                cwd=root, text=True, capture_output=True, timeout=120)
        text = result.stdout + result.stderr
        (directory / 'check.log').write_text(text)
        if expected is None:
            if result.returncode or not artifact.exists():
                raise RuntimeError(f'{name}: positive control failed\n{text}')
        elif (result.returncode == 0 or artifact.exists() or expected not in text or
              not re.search(r'Fixture\.sol:\d+:\d+:', text)):
            raise RuntimeError(f'{name}: expected located rejection {expected!r}\n{text}')
        print(f'pass storage-{name}', flush=True)
    print(output)


if __name__ == '__main__':
    main()
