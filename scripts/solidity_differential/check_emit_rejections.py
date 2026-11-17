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
      None),
     ('narrow64-expr',
      'uint256',
      'event E(uint64 indexed a, uint32 b, bytes4 indexed sel, bytes1 flag);',
      'uint64 a = uint64(x + 1); bytes4 sel = bytes4(uint32(x)); emit E(a, uint32(x >> 8), sel, bytes1(uint8(x))); return x;',
      None),
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
     # Named arguments in declaration order lower as the positional call.
     ('named',
      'uint256',
      'event E(uint256 value);',
      'emit E({value: x}); return x;',
      None),
     ('named-declared-order',
      'uint256',
      'event E(uint256 a, bytes32 b);',
      'emit E({a: x, b: bytes32(x)}); return x;',
      None),
     ('named-reordered',
      'uint256',
      'event E(uint256 a, bytes32 b);',
      'emit E({b: bytes32(x), a: x}); return x;',
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
     ('nested-mapping-read',
      'uint256',
      'struct S { mapping(uint256 => uint256) inner; uint256 total; } mapping(uint256 => S) m; '
      'event E(uint256 indexed a, uint256 b);',
      'uint256[3] memory arr = [uint256(1), 2, 3]; emit E(x, m[arr[x]].inner[x]); return x;',
      None),
     ('nested-mapping-read-competing',
      'uint256',
      'struct S { mapping(uint256 => uint256) inner; uint256 total; } mapping(uint256 => S) m; '
      'event E(uint256 a, uint256 indexed b);',
      'uint256[3] memory arr = [uint256(1), 2, 3]; emit E(arr[x], m[arr[x]].inner[x]); return x;',
      'event arguments with competing revert paths require explicit evaluation-order support'),
     ('nested-mapping-read-unguarded-competing',
      'uint256',
      'struct S { mapping(uint256 => uint256) inner; uint256 total; } mapping(uint256 => S) m; '
      'event E(uint256 a, uint256 indexed b, uint256 c);',
      'uint256[3] memory arr = [uint256(1), 2, 3]; uint256[2] memory two = [uint256(4), 5]; '
      'emit E(two[x], arr[x], m[x].inner[x]); return x;',
      'event arguments with competing revert paths require explicit evaluation-order support'),
     ('assignment-argument',
      'uint256',
      'uint256 first; uint256 second; event E(uint256 a, uint256 b);',
      'uint256 y = x; emit E(y, y = 5); return y;',
      'event arguments with assignments require explicit evaluation-order support'),
     ('increment-argument',
      'uint256',
      'event E(uint256 a, uint256 b);',
      'uint256 y = x; emit E(y, y++); return y;',
      'event arguments with assignments require explicit evaluation-order support'),
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
     ('string-data',
      'uint256',
      'event E(uint64 indexed id, string label);',
      'string memory label = "a label"; emit E(uint64(x), label); emit E(1, "literal"); return x;',
      None),
     ('string-variable-before-indexed',
      'uint256',
      'event E(string note, uint256 indexed value, string tail);',
      'string memory note = "n"; emit E(note, x, string.concat(note, note)); return x;',
      None),
     ('string-computed-before-indexed',
      'uint256',
      'event E(string note, uint256 indexed value); function tag(uint256 v) internal pure returns (string memory) '
      '{ require(v != 7, "seven"); return "t"; }',
      'emit E(tag(x), x); return x;',
      'event data arguments before an indexed argument must be variables or literals'),
     ('string-event-scalar-before-indexed',
      'uint256',
      'event E(uint256 a, uint256 indexed b, string s); function inc(uint256 v) internal pure returns (uint256) '
      '{ return v + 1; }',
      'emit E(inc(x), x, "s"); return x;',
      'event data arguments before an indexed argument must be variables or literals'),
     ('string-indexed',
      'uint256',
      'event E(uint256 value, string indexed name);',
      'emit E(x, "n"); return x;',
      'unsupported event parameter type string'),
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
