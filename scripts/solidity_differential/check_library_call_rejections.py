"""Located rejections for calls that solc lowers to a DELEGATECALL into a linked library.

A `public` or `external` library function called from outside its library runs the
bytecode linked at deployment, which the source does not determine: the body may be a
stub for code produced by another toolchain. The importer must reject the call at its
source location instead of inlining the body. Calls that solc inlines (internal library
functions, and public ones called by name inside their own library) stay supported.
"""
import argparse
import json
from pathlib import Path
import subprocess
from .engine import HarnessError, write_json

PRAGMA = 'pragma solidity 0.8.34;\n'
DIAGNOSTIC = 'external library calls are outside this slice'
CONTRACT = ('contract C {\n'
            '    bytes32 public root;\n'
            '    function f(bytes32 a, bytes32 b) external {\n'
            '        {body}\n'
            '    }\n'
            '{members}'
            '}\n')

# name, library source, contract body, extra contract members, rejected call (None: imports)
CASES = [
    ('public-stub',
     'library H {\n    function h(bytes32 a, bytes32 b) public pure returns (bytes32) {}\n}\n',
     'root = H.h(a, b);', '', 'H.h(a, b)'),
    ('external-stub',
     'library H {\n    function h(bytes32 a, bytes32 b) external pure returns (bytes32) {}\n}\n',
     'root = H.h(a, b);', '', 'H.h(a, b)'),
    ('public-body',
     'library H {\n    function h(bytes32 a, bytes32 b) public pure returns (bytes32) { return a ^ b; }\n}\n',
     'root = H.h(a, b);', '', 'H.h(a, b)'),
    ('using-for',
     'library H {\n    function h(bytes32 a, bytes32 b) public pure returns (bytes32) { return a ^ b; }\n}\n',
     'root = a.h(b);', '    using H for bytes32;\n', 'a.h(b)'),
    ('discarded',
     'library H {\n    function touch(bytes32 a) public pure {}\n}\n',
     'H.touch(a);\n        root = b;', '', 'H.touch(a)'),
    ('stub-revert-in-void-helper',
     'library H {\n    function check(bytes32) public pure { revert(); }\n}\n',
     'g(a, b);',
     '    function g(bytes32 a, bytes32 b) internal {\n        H.check(a);\n        root = b;\n    }\n',
     'H.check(a)'),
    ('internal-member',
     'library H {\n    function h(bytes32 a, bytes32 b) internal pure returns (bytes32) { return a ^ b; }\n}\n',
     'root = H.h(a, b);', '', None),
    ('internal-using-for',
     'library H {\n    function h(bytes32 a, bytes32 b) internal pure returns (bytes32) { return a ^ b; }\n}\n',
     'root = a.h(b);', '    using H for bytes32;\n', None),
    ('public-by-name-inside-library',
     'library H {\n    function h(bytes32 a, bytes32 b) public pure returns (bytes32) { return a ^ b; }\n'
     '    function wrap(bytes32 a, bytes32 b) internal pure returns (bytes32) { return h(a, b); }\n}\n',
     'root = H.wrap(a, b);', '', None),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    results = []
    for name, library, body, members, token in CASES:
        source = PRAGMA + library + CONTRACT.replace('{body}', body).replace('{members}', members)
        project = output / name
        project.mkdir()
        (project / 'Case.sol').write_text(source)
        driver = project / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            '  contract C\n  function f(bytes32, bytes32)\n')
        result = subprocess.run(['lake', 'env', 'lean', str(driver)], capture_output=True,
                                text=True, timeout=180)
        log = result.stdout + result.stderr
        (project / 'import.log').write_text(log)
        if token is None:
            if result.returncode:
                raise HarnessError(f'{name}: positive control failed: {log}')
        else:
            offset = source.index(token)
            line = source.count('\n', 0, offset) + 1
            column = offset - source.rfind('\n', 0, offset)
            location = f'Case.sol:{line}:{column}:'
            if result.returncode == 0 or DIAGNOSTIC not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {DIAGNOSTIC}: {log}')
        results.append({'case': name, 'exit': result.returncode,
                        'diagnostic': DIAGNOSTIC if token else None})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(CASES)})
    print(f'{len(CASES)} library call acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
