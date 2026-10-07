"""Exact event controls and located near-miss rejections."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path.cwd()
    output = Path(tempfile.mkdtemp(prefix='emit-rejections-', dir=root / '.lake'))
    cases = [
        ('wide-direct-widening', 'uint8', 'event E(uint256 value);', 'emit E(x); return x;', None),
        ('inlined-widening', 'uint8', 'event E(uint128 value); function widen(uint8 v) internal pure returns (uint128) { return v; }', 'emit E(widen(x)); return x;', 'event direct parameter type differs from its declaration'),
('qualified-collision', 'uint256', '', 'emit A.E(x); emit B.E(x); return x;', 'event name resolves to multiple declarations'),
    ('scalar',
      'uint256',
      'event E(address indexed owner, uint256 value, bool flag, bytes32 tag);',
      'emit E(msg.sender, x, true, bytes32(x)); return x;',
      None),
     ('narrow-direct', 'uint128', 'event E(uint128 value);', 'emit E(x); return x;', None),
     ('narrow8-direct', 'uint8', 'event E(uint8 value);', 'emit E(x); return x;', None),
     ('narrow8-max-constant', 'uint256', 'event E(uint8 value);', 'emit E(type(uint8).max); return x;', None),
     ('narrow-local',
      'uint256',
      'event E(uint8 value);',
      'uint8 low = uint8(x); emit E(low); return x;',
      'narrow event arguments currently require a matching direct parameter'),
     ('narrow-widened',
      'uint8',
      'event E(uint128 value);',
      'emit E(x); return x;',
      'event direct parameter type differs from its declaration'),
     ('anonymous',
      'uint256',
      'event E(uint256 value) anonymous;',
      'emit E(x); return x;',
      'anonymous events are unsupported'),
     ('dynamic',
      'uint256',
      'event E(bytes value);',
      'emit E(hex"12"); return x;',
      'unsupported event parameter type bytes'),
     ('named',
      'uint256',
      'event E(uint256 value);',
      'emit E({value: x}); return x;',
      'named event arguments are unsupported'),
     ('guarded',
      'uint256',
      'event E(uint256 value); function guarded(uint256 v) internal pure returns (uint256) { require(v != 0, '
      '"guard"); return v; }',
      'emit E(guarded(x)); return x;',
      'event arguments currently require total scalar expressions'),
     ('panic',
      'uint256',
      'event E(uint256 value);',
      'emit E(100 / x); return x;',
      'event arguments currently require total scalar expressions'),
     ('overloaded',
      'uint256',
      'event E(uint256 value); event E(address value);',
      'emit E(x); emit E(msg.sender); return x;',
      'ambiguous declaration'),
     ('bytes16',
      'uint256',
      'event E(bytes16 value);',
      'emit E(bytes16(bytes32(x))); return x;',
      'unsupported event parameter type bytes16'),
     ('empty', 'uint256', 'event E();', 'emit E(); return x;', None)]
    for name, parameter_type, fields, body, expected in cases:
        returns = parameter_type
        directory = output / name
        directory.mkdir()
        result_clause = f'returns ({returns})' if returns else ''
        prefix = 'library A { event E(uint256 value); } library B { event E(uint256 value); }' if name == 'qualified-collision' else ''
        (directory / 'Fixture.sol').write_text(f'''pragma solidity 0.8.34;
{prefix}
contract C {{
 {fields}
 function checked({parameter_type} x) external {result_clause} {{
  {body}
 }}
}}
''')
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked({parameter_type})
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
        print(f'pass emit-{name}', flush=True)
    print(output)


if __name__ == '__main__':
    main()
