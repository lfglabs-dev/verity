"""Located near misses around complete scalar-array ABI roots."""
import argparse
import json
from pathlib import Path
import re
import subprocess
from .engine import HarnessError, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    results = []
    types = [(ty + '[]', None) for ty in ('uint8', 'uint128', 'uint256', 'address', 'bool', 'bytes32')]
    types += [('int128[]', 'unsupported scalar int128'),
              ('bytes16[]', 'unsupported scalar bytes16'),
              ('uint128[][]', 'expected a flat struct array element'),
              ('uint128[2]', 'fixed arrays are unsupported')]
    cases = [(ty, location, '7', message) for location in ('memory', 'calldata')
             for ty, message in types]
    cases.append(('uint128[]', 'calldata', 'box.values[flag + 1]', None))
    cases.append(('uint128[]', 'calldata', 'box.values[flag += 1]', 'compound assignment expressions are outside this slice'))
    # Keep every original case and exercise the same schema boundaries at length access.
    cases += [(ty, location, 'box.values.length', message)
              for location in ('memory', 'calldata') for ty, message in types]

    for index, (ty, location, expression, expected) in enumerate(cases):
        directory = output / str(index)
        directory.mkdir()
        source = ('pragma solidity 0.8.34;\n'
                  f'struct Box {{ {ty} values; uint256[] anchor; }}\n'
                  f'contract C {{ function f(Box {location} box, uint256 flag) '
                  f'external pure returns (uint256) {{ return {expression}; }} }}\n')
        (directory / 'Fixture.sol').write_text(source)
        driver = directory / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
                          f'solidity_import tested from {json.dumps(str(directory))} entry "Fixture.sol"\n'
                          '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
                          '  contract C\n  function f(Box,uint256)\n')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', '-j1', str(driver), '-o', str(artifact)],
                                text=True, capture_output=True, timeout=120)
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if expected is None:
            if result.returncode or not artifact.exists():
                raise HarnessError(f'{ty} {location}: positive control failed: {directory}')
        elif (result.returncode == 0 or artifact.exists() or expected not in log
              or not re.search(r'Fixture\.sol:\d+:\d+:', log)):
            raise HarnessError(f'{ty} {location}: missing precise rejection: {directory}')
        results.append({'type': ty, 'location': location, 'expected': expected,
                        'accepted': result.returncode == 0})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(results)})
    print(f'All {len(results)} scalar-array acceptance/rejection controls pass: {output}')


if __name__ == '__main__':
    main()
