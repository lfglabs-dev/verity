"""Ordinary lexical blocks must not admit unsupported nested statements."""
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
        ('nested-return', '{ { return 7; } }', None, None),
        ('empty-block', '{} return 7;', None, None),
        ('unchecked', '{ unchecked { return 7; } }', 'unchecked', 'unsupported statement UncheckedBlock'),
        ('conditional', '{ if (true) { return 7; } } return 8;', 'if', 'unsupported statement IfStatement'),
        ('loop', '{ while (false) {} } return 7;', 'while', 'unsupported statement WhileStatement'),
        ('after-return', '{ return 7; } return 8;', 'return 8', 'statement after root return'),
        ('uninitialized', '{ uint256 x; } return 7;', 'uint256 x', 'local declarations without an initializer'),
    ]
    results = []
    for name, body, token, diagnostic in cases:
        project = output / name
        project.mkdir()
        source = 'pragma solidity 0.8.34;\ncontract C { function f() external pure returns (uint256) {\n    ' + body + '\n} }\n'
        (project / 'Case.sol').write_text(source)
        driver = project / 'Check.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
            f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            '  contract C\n  function f()\n')
        proc = subprocess.run(['lake', 'env', 'lean', str(driver)],
                              capture_output=True, text=True, timeout=180)
        log = proc.stdout + proc.stderr
        (project / 'import.log').write_text(log)
        if diagnostic is None:
            if proc.returncode:
                raise HarnessError(f'{name}: positive control failed: {log}')
        else:
            column = 5 + body.index(token)
            location = f'Case.sol:3:{column}:'
            if not proc.returncode or diagnostic not in log or location not in log:
                raise HarnessError(f'{name}: expected {location} {diagnostic}: {log}')
        results.append({'case': name, 'exit': proc.returncode, 'diagnostic': diagnostic})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(cases)})
    print(f'{len(cases)} block acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
