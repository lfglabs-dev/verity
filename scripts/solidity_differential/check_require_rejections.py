"""Actual importer near-miss checks with precise source locations and no olean."""
from pathlib import Path
import re
import subprocess
import tempfile
from cases import generate


def main():
    boolean_cases = generate({'variables': {'flag': 1}}, 256, 2451, [])
    if {values['flag'] for _, values in boolean_cases} != {0, 1}:
        raise RuntimeError('one-bit generated variables must cover exactly canonical booleans')
    root = Path(__file__).resolve().parents[2]
    output = Path(tempfile.mkdtemp(prefix='require-rejections-', dir=root / '.lake'))
    cases = [
        ('literal', 'require(value > 7, "message");', None),
        ('no-message', 'require(value > 7);', 'supported Solidity builtin signature'),
        ('custom-error', 'require(value > 7, Failure(value));', None),
        ('custom-error-expression', 'require(value > 7, Failure(value + 1));', 'literals or scalar bindings'),
        ('custom-error-named', 'require(value > 7, Failure({value: value}));', 'named custom-error arguments'),
        ('custom-error-signed', 'require(value > 7, Failure(int256(value)));', 'unsupported custom-error parameter type int256'),
        ('custom-error-dynamic', 'require(value > 7, Failure(bytes("x")));', 'unsupported custom-error parameter type bytes'),
        ('dynamic-message', 'require(value > 7, reason);', 'literal string message'),
        ('byte-string-cast', 'require(value > 7, string(hex"61"));', 'literal string message'),
        ('other-call', 'helper(value);', 'only builtin require calls'),
    ]
    for name, statement, expected in cases:
        directory = output / name
        directory.mkdir()
        source = '''pragma solidity 0.8.34;
contract C {
 error Failure(uint256 value);
 function helper(uint256 value) internal pure returns (uint256) { return value; }
 function checked(uint256 value, string memory reason) external pure returns (uint256) {
  ''' + statement + '''
  return value;
 }
}
'''
        source = source.replace(', string memory reason', '')
        if name == 'custom-error-signed':
            source = source.replace('error Failure(uint256 value)', 'error Failure(int256 value)')
        if name == 'custom-error-dynamic':
            source = source.replace('error Failure(uint256 value)', 'error Failure(bytes value)')
        (directory / 'Fixture.sol').write_text(source)
        # Dynamic parameters themselves are unsupported; use a local string
        # expression so the rejection is pinned specifically to require lowering.
        if name == 'dynamic-message':
            source = (directory / 'Fixture.sol').read_text().replace(', string memory reason', '')
            source = source.replace('require(value > 7, reason);', 'require(value > 7, string.concat("a", "b"));')
            (directory / 'Fixture.sol').write_text(source)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked(uint256)
''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                                cwd=root, text=True, capture_output=True)
        text = result.stdout + result.stderr
        (directory / 'check.log').write_text(text)
        if expected is None:
            if result.returncode or not artifact.exists():
                raise RuntimeError(f'{name}: positive control failed\n{text}')
        elif (result.returncode == 0 or artifact.exists() or expected not in text or
              not re.search(r'Fixture\.sol:\d+:\d+:', text)):
            raise RuntimeError(f'{name}: expected located importer rejection {expected!r}\n{text}')
        print(f'pass require-{name}')


if __name__ == '__main__':
    main()
