"""Located near misses for exact internal struct reference binding."""
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
    prefix = 'pragma solidity 0.8.34;\nstruct S { uint256 x; }\ncontract C {\n'
    cases = [
        ('memory', 'memory', 'memory', 's', None, None),
        ('calldata', 'calldata', 'calldata', 's', None, None),
        ('copy', 'calldata', 'memory', 's', 'S memory item',
         'reference argument location conversion is unsupported'),
        ('storage', 'memory', 'storage', 'state', None, None),
        ('storage-reassigned', 'memory', 'storage', 'state', 'S storage item',
         'reassigned storage struct parameters are outside this slice'),
        ('recursive', 'memory', 'memory', 's', 'h(item)', 'recursive call'),
        ('parenthesized', 'memory', 'memory', '(s)', '(s)',
         'unsupported reference TupleExpression'),
    ]
    cases += [
        ('external-library', 'memory', 'memory', 's', 'L.h(s)',
         'external reference helper calls are unsupported'),
        ('yul-shadow', 'memory', 'memory', 's', 'item }',
         'unbound Yul identifier item'),
    ]
    results = []
    for name, root, helper, argument, token, diagnostic in cases:
        source = prefix + (
            f'function f(S {root} s) external pure returns (uint256) {{ return h({argument}); }}\n'
            f'function h(S {helper} item) internal pure returns (uint256) {{ return item.x; }}\n'
            '}\n')
        if name in ('storage', 'storage-reassigned'):
            source = source.replace('contract C {', 'contract C { S state;').replace('external pure', 'external view').replace('internal pure', 'internal view')
        if name == 'storage-reassigned':
            source = source.replace('return item.x;', 'item = state; return item.x;')
        if name == 'recursive':
            source = source.replace('return item.x;', 'return h(item);')
        signature = 'f(S)'
        if name == 'external-library':
            source = ('pragma solidity 0.8.34;\nstruct S { uint256 x; }\n'
                'library L { function h(S memory item) external pure returns (uint256) { return item.x; } }\n'
                'contract C { function f(S memory s) external pure returns (uint256) { return L.h(s); } }\n')
        if name == 'yul-shadow':
            source = prefix + (
                'function f(S memory s, uint256 value) external pure returns (uint256) { uint256 item = value; return h(s); }\n'
                'function h(S memory item) internal pure returns (uint256 result) { assembly { result := item } }\n'
                '}\n')
            signature = 'f(S,uint256)'
        project = output / name
        project.mkdir()
        (project / 'Case.sol').write_text(source)
        driver = project / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            f'  contract C\n  function {signature}\n')
        result = subprocess.run(['lake', 'env', 'lean', str(driver)], capture_output=True,
                                text=True, timeout=180)
        log = result.stdout + result.stderr
        (project / 'import.log').write_text(log)
        if diagnostic is None:
            if result.returncode:
                raise HarnessError(f'{name}: positive control failed: {log}')
        else:
            offset = source.index(token)
            line = source.count('\n', 0, offset) + 1
            column = offset - source.rfind('\n', 0, offset)
            location = f'Case.sol:{line}:{column}:'
            if result.returncode == 0 or diagnostic not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {diagnostic}: {log}')
        results.append({'case': name, 'exit': result.returncode, 'diagnostic': diagnostic})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(cases)})
    print(f'{len(cases)} reference acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
