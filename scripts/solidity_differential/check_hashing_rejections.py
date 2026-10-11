"""Located boundaries and positive controls for ABI encoding and Keccak."""
import argparse
import json
from pathlib import Path
import subprocess
from .engine import HarnessError, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cases = [
        ('empty', '', '', 'keccak256(abi.encode())', None, None),
        ('hex-number', '', '', 'keccak256(abi.encodePacked(uint8(0xff)))', None, None),
        ('hex-bytes', '', '', 'keccak256(hex"00ff")', None, None),
        ('unicode', '', '', 'keccak256(unicode"é")', None, None),
        ('packed-call', 'function h() internal pure returns(uint256) { require(false, "hidden"); return 0; }',
         '', 'keccak256(abi.encodePacked(uint256(h())))', 'h()', 'effectful ABI encoding argument is unsupported'),
        ('encode-call', 'function h() internal pure returns(uint256) { require(false, "hidden"); return 0; }',
         '', 'keccak256(abi.encode(uint256(h())))', 'h()', 'effectful ABI encoding argument is unsupported'),
        ('packed-arithmetic', '', 'uint256 x', 'keccak256(abi.encodePacked(x + 1))',
         'x + 1', 'effectful ABI encoding argument is unsupported'),
        ('packed-struct', 'struct S { uint256 a; }', 'S memory s', 'keccak256(abi.encodePacked(abi.encode(s), s.a))', None, None),
        ('packed-member-array', 'struct S { uint256[] a; }', 'S memory s', 'keccak256(abi.encodePacked(s.a))',
         's.a', 'hash input must be a supported ABI encoding'),
        ('multi-struct', 'struct S { uint256 a; }', 'S memory s', 'keccak256(abi.encode(s, uint256(0)))', None, None),
        ('multi-dynamic-struct', 'struct S { uint256[] a; }', 'S memory s', 'keccak256(abi.encode(s, uint256(0)))',
         's, uint256', 'unsupported ABI encoding argument type struct'),
        ('dynamic-bytes', '', 'bytes calldata value', 'keccak256(value)', None, None),
        ('msg-data-bytes', '', '', 'keccak256(msg.data)',
         'msg.data', 'hash input must be a supported ABI encoding'),
    ]
    results = []
    for name, declarations, params, expression, token, diagnostic in cases:
        source = ('pragma solidity 0.8.34;\ncontract C {\n' + declarations + '\n' +
                  f'function f({params}) external pure returns(bytes32) {{ return {expression}; }}\n}}\n')
        signature_types = ','.join(p.strip().split()[0] for p in params.split(',') if p.strip())
        project = output / name
        project.mkdir()
        (project / 'Case.sol').write_text(source)
        driver = project / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            f'  contract C\n  function f({signature_types})\n')
        result = subprocess.run(['lake', 'env', 'lean', str(driver)], capture_output=True,
                                text=True, timeout=180)
        log = result.stdout + result.stderr
        (project / 'import.log').write_text(log)
        if diagnostic is None:
            if result.returncode:
                raise HarnessError(f'{name}: positive control failed: {log}')
        else:
            offset = source.rindex(token)
            line = source.count('\n', 0, offset) + 1
            column = len(source[:offset].split('\n')[-1].encode()) + 1
            location = f'Case.sol:{line}:{column}:'
            if result.returncode == 0 or diagnostic not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {diagnostic}: {log}')
        results.append({'case': name, 'exit': result.returncode, 'diagnostic': diagnostic})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(cases)})
    print(f'{len(cases)} hashing acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
