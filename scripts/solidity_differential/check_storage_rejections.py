"""Exact scalar storage controls and located near-miss rejections."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path.cwd()
    output = Path(tempfile.mkdtemp(prefix='storage-rejections-', dir=root / '.lake'))
    cases = [
        ('if-else', '', 'if (x > 1) { return 1; } else { return 2; }', 'uint256', None),
        ('if-early-return', 'uint256 value;', 'if (x == 0) return 0; value = x; return value;', 'uint256', None),
        ('if-helper-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) return 1; require(y == 0, "one"); return 0; }', 'return h(x);', 'uint256', None),
        ('if-bare-return', 'uint256 value;', 'if (x == 0) return; value = x;', '', 'bare return requires'),
        ('if-dead-remainder', '', 'if (false) { return x | 2; } return x;', 'uint256', 'unsupported operator |'),
        ('if-after-both-return', 'uint256 value;', 'if (x > 1) { return 1; } else { return 2; } value = x;', 'uint256', 'statement after root return'),
        ('if-helper-missing-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) return 1; }', 'return h(x);', 'uint256', 'does not return on every path'),
        ('if-helper-after-both-return', 'function h(uint256 y) internal pure returns (uint256) { if (y > 1) { return 1; } else { return 2; } require(y > 0, "dead"); }', 'return h(x);', 'uint256', 'statement after helper result'),
        ('if-helper-effect', 'uint256 value; function h(uint256 y) internal returns (uint256) { if (y > 1) { value = y; } return y; }', 'return h(x);', 'uint256', 'only builtin require calls'),
        ('if-unchecked-branch', '', 'if (x > 1) { unchecked { return x - 2; } } return x;', 'uint256', 'unsupported statement UncheckedBlock'),
        ('logical-or', '', 'return x == 0 || 100 / x > 1;', 'bool', None),
        ('logical-and', '', 'return x != 0 && 100 / x > 1;', 'bool', None),
        ('logical-dead-effect', 'uint256 value; function bump() internal returns (bool) { value = 1; return true; }', 'return true || bump();', 'bool', 'only builtin require calls'),
        ('logical-dead-remainder', '', 'return false && x | 2 == 3;', 'bool', 'unsupported operator |'),
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
        ('mapping-compound', 'mapping(uint256 => uint256) value;', 'value[x] += x; return value[x];', 'uint256', None),
        ('literal-denomination', '', 'return 1 ether + 2 weeks + 1_000;', 'uint256', None),
        ('literal-scientific', '', 'return x / 2 + 0.5e3 + 2.5e-1 * 4;', 'uint256', None),
        ('literal-rational-intermediate', '', 'return x / 2 + 5 / 2 * 2 + (1 - 2 + 3);', 'uint256', None),
        ('literal-exponent', '', 'return x / 2 + 2 ** 254;', 'uint256', None),
        ('constant-chain', 'uint256 constant A = 3 days; uint256 constant B = A * 1e18;', 'return x / 2 + B;', 'uint256', None),
        ('constant-keccak', 'bytes32 constant H = keccak256("k"); uint256 constant U = uint256(H);', 'return x / 2 + U / 2;', 'uint256', None),
        ('constant-narrow', 'uint8 constant S = 200; uint32 constant R = uint32(uint256(1e18) / 7);', 'return x / 2 + S + R;', 'uint256', None),
        ('constant-bool', 'bool constant F = true;', 'return F ? x : 0;', 'uint256', 'constant of type bool is outside this slice'),
        ('constant-signed', 'int256 constant N = -1;', 'return uint256(N) - x;', 'uint256', 'constant of type int256 is outside this slice'),
        ('constant-shift', '', 'return x / 2 + (1 << 3);', 'uint256', 'unsupported constant operator <<'),
        ('constant-modulo', '', 'return x / 2 + 7 % 4;', 'uint256', 'unsupported constant operator %'),
        ('constant-bitwise-not', '', 'return x / 2 + (~uint8(0));', 'uint256', 'unsupported expression UnaryOperation'),
        ('literal-string', '', 'return bytes32("123");', 'bytes32', 'unsupported non-numeric literal'),
        ('struct-target', 'struct Pair { uint128 a; uint128 b; } Pair value;', 'value.a = uint128(x); return x;', 'uint256', 'only a resolved scalar storage identifier'),
        ('compound', 'uint256 value;', 'value += x; value -= 1; value *= 3; value /= 2; value %= 7; return value;', 'uint256', None),
        ('increment', 'uint256 value;', 'value++; --value; ++value; value--; return value;', 'uint256', None),
        ('compound-narrow', 'uint8 value; mapping(uint256 => uint64) m;', 'value += 7; m[x] *= 3; m[x]++; return value;', 'uint8', None),
        ('compound-order', 'mapping(uint256 => mapping(address => uint256)) m;', 'm[x - 1][msg.sender] -= 100 / x; return m[x][msg.sender];', 'uint256', None),
        ('modulo', '', 'return x % 7 + uint128(x) % 3;', 'uint256', None),
        ('compound-bitwise', 'uint256 value;', 'value |= x; return value;', 'uint256', 'unsupported assignment operator |='),
        ('compound-shift', 'uint256 value;', 'value <<= 1; return value;', 'uint256', 'unsupported assignment operator <<='),
        ('compound-local', '', 'uint256 value = 1; value += x; return value;', 'uint256', 'assignment target is not scalar storage'),
        ('compound-struct', 'struct Pair { uint128 a; uint128 b; } Pair value;', 'value.a += 1; return x;', 'uint256', 'only a resolved scalar storage identifier'),
        ('increment-local', '', 'uint256 value = x; value++; return value;', 'uint256', 'assignment target is not scalar storage'),
        ('increment-expression', 'uint256 value;', 'return value++;', 'uint256', 'unsupported expression UnaryOperation'),
        ('compound-expression', 'uint256 value;', 'return value += x;', 'uint256', 'unsupported expression Assignment'),
        ('modulo-signed', '', 'return uint256(int256(x) % 3);', 'uint256', 'unsupported'),
        ('local', '', 'uint256 value = 0; value = x; return value;', 'uint256', 'assignment target is not scalar storage'),
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
