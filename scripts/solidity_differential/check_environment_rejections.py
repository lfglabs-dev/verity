"""Reject unsupported context near misses with located importer diagnostics."""
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path.cwd()
    output = Path(tempfile.mkdtemp(prefix='environment-rejections-', dir=root / '.lake'))
    cases = [
        ('shadow-msg', 'uint256', 'msg.sender', 'pure', None),
        ('shadow-block', 'uint256', 'block.number', 'pure', None),
        ('sender', 'address', 'msg.sender', 'view', None),
        ('this', 'address', 'address(this)', 'view', None),
        ('number', 'uint256', 'block.number', 'view', None),
        ('chainid', 'uint256', 'block.chainid', 'view', None),
        ('timestamp', 'uint256', 'block.timestamp', 'view', None),
        ('value', 'uint256', 'msg.value', 'payable', 'payable'),
        ('payable-constant', 'uint256', '1', 'payable', 'payable'),
        ('basefee', 'uint256', 'block.basefee', 'view', 'unsupported block context member basefee'),
        ('prevrandao', 'uint256', 'block.prevrandao', 'view', 'unsupported block context member prevrandao'),
        ('coinbase', 'address', 'block.coinbase', 'view', 'unsupported block context member coinbase'),
        ('origin', 'address', 'tx.origin', 'view', 'unresolved builtin identifier'),
        ('signature', 'bytes4', 'msg.sig', 'view', 'unsupported'),
        ('data', 'uint256', 'msg.data.length', 'view', 'unsupported message context member data'),
    ]
    for name, ty, expr, mutability, expected in cases:
        directory = output / name
        directory.mkdir()
        (directory / 'Fixture.sol').write_text(f'''pragma solidity 0.8.34;
contract C {{
 function checked() external {mutability} returns ({ty}) {{
  return {expr};
 }}
}}
''')
        signature = 'checked()'
        if name.startswith('shadow-'):
            binding = name.removeprefix('shadow-')
            source = (directory / 'Fixture.sol').read_text()
            source = source.replace('contract C {',
                                    'contract C { struct Context { uint256 sender; uint256 number; }')
            source = source.replace('function checked()', f'function checked(Context calldata {binding})')
            (directory / 'Fixture.sol').write_text(source)
            signature = 'checked(Context)'
        driver = directory / 'Check.lean' 
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function {signature}
''')
        if mutability == 'payable':
            source = (directory / 'Fixture.sol').read_text()
            source = source.replace('contract C {',
                'contract C { function safe() external pure returns (uint256) { return 1; }')
            (directory / 'Fixture.sol').write_text(source)
            driver.write_text(driver.read_text().replace('  function checked()',
                '  function safe()\n  function checked()'))
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
            raise RuntimeError(f'{name}: expected located importer rejection {expected!r}\n{text}')
        if mutability == 'payable' and 'closure: C.checked' not in text:
            raise RuntimeError(f'{name}: payable rejection names the wrong root\n{text}')
        print(f'pass environment-{name}', flush=True)
    print(output)


if __name__ == '__main__':
    main()
