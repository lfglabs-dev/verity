"""Located near misses around flat static struct ABI, with positive controls."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    output = Path(tempfile.mkdtemp(prefix='struct-abi-rejections-', dir='.lake')).resolve()
    cases = [
        ('memory', 'uint8 small;', 'Pair memory pair', 'Pair', 'return pair.small;', True),
        ('calldata', 'uint8 small;', 'Pair calldata pair', 'Pair', 'return pair.small;', True),
        ('unused', 'uint8 small;', 'Pair calldata pair', 'Pair', 'return 7;', True),
        ('signed', 'int8 small;', 'Pair calldata pair', 'Pair', 'return uint256(int256(pair.small));', False),
        ('fixed-bytes', 'bytes16 small;', 'Pair calldata pair', 'Pair', 'return uint256(bytes32(pair.small));', False),
        ('array-read', 'uint8[2] small;', 'Pair calldata pair', 'Pair', 'return pair.small[0];', False),
        ('collision', 'uint8 small;', 'Pair calldata pair, uint256 pair_1', 'Pair,uint256', 'return pair.small + pair_1;', False),
        ('member-write', 'uint8 small;', 'Pair memory pair', 'Pair', 'pair.small = 3; return pair.small;', False),
    ]
    for index, (name, member, declaration, signature, body, valid) in enumerate(cases):
        directory = output / str(index)
        directory.mkdir()
        (directory / 'Fixture.sol').write_text(f'''pragma solidity 0.8.34;
contract C {{
    struct Pair {{ uint256 pad; {member} }}
    function checked({declaration}) external pure returns (uint256) {{ {body} }}
}}
''')
        signature_lean = ','.join('«' + item + '»' for item in signature.split(','))
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked({signature_lean})
''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
            text=True, capture_output=True, timeout=120)
        text = result.stdout + result.stderr
        (directory / 'check.log').write_text(text)
        if valid:
            if result.returncode or not artifact.exists():
                raise RuntimeError(f'{signature}: positive control failed\n{text}')
        elif (not result.returncode or artifact.exists()
              or not re.search(r'Fixture\.sol:\d+:\d+:', text)):
            raise RuntimeError(f'{signature}: expected located struct rejection\n{text}')
        print(f'pass struct ABI {name}', flush=True)
    print(output)


if __name__ == '__main__':
    main()
