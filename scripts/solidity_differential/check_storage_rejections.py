"""Exact scalar storage controls and located near-miss rejections."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path.cwd()
    output = Path(tempfile.mkdtemp(prefix='storage-rejections-', dir=root / '.lake'))
    cases = [
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
        ('mapping-target', 'mapping(uint256 => uint256) value;', 'value[x] = x; return x;', 'uint256', 'only a resolved scalar storage identifier'),
        ('struct-target', 'struct Pair { uint128 a; uint128 b; } Pair value;', 'value.a = uint128(x); return x;', 'uint256', 'only a resolved scalar storage identifier'),
        ('compound', 'uint256 value;', 'value += x; return value;', 'uint256', 'only scalar storage assignment'),
        ('increment', 'uint256 value;', 'value++; return value;', 'uint256', 'only scalar storage assignment'),
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
