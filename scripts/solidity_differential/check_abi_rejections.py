"""Located rejections around the scalar ABI fragment, with positive controls."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    output = Path(tempfile.mkdtemp(prefix='abi-rejections-', dir='.lake')).resolve()
    cases = [(ty, ty, True) for ty in ('uint8', 'uint16', 'uint248', 'uint256', 'address', 'bool')]
    cases += [(ty, ty, False) for ty in ('int8', 'int256', 'bytes16')]
    cases += [('bytes', 'bytes memory', False), ('string', 'string memory', False),
              ('uint256[]', 'uint256[] calldata', False), ('uint8[2]', 'uint8[2] calldata', False)]
    for index, (signature, declaration, valid) in enumerate(cases):
        directory = output / str(index)
        directory.mkdir()
        (directory / 'Fixture.sol').write_text(f'''pragma solidity 0.8.34;
contract C {{
    function checked({declaration} value) external pure returns (uint256) {{ return 7; }}
}}
''')
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked(«{signature}»)
''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
            text=True, capture_output=True, timeout=120)
        text = result.stdout + result.stderr
        (directory / 'check.log').write_text(text)
        if valid:
            if result.returncode or not artifact.exists():
                raise RuntimeError(f'{signature}: positive control failed\n{text}')
        elif (not result.returncode or artifact.exists() or 'unsupported parameter type' not in text
              or not re.search(r'Fixture\.sol:\d+:\d+:', text)):
            raise RuntimeError(f'{signature}: expected located unsupported-parameter rejection\n{text}')
        print(f'pass ABI {signature}', flush=True)
    print(output)


if __name__ == '__main__':
    main()
