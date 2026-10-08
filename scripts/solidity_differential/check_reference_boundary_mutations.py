"""Detect removal of reference call-boundary guards using located rejections.

A build/tool failure is not mutation detection: each mutant must first admit
its specific unsupported input successfully.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys
from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', choices=['external-library', 'yul-shadow'])
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    rules = [
        ('external-library',
         'if optStr fn "visibility" == some "external" then',
         'if false then'),
        ('yul-shadow', 'yul := yul.erase pname', 'pure ()'),
    ]
    results = []
    for name, anchor, replacement in rules:
        if args.only and name != args.only:
            continue
        root = output / name
        root.mkdir()
        directory = root / 'snapshot'
        snapshot(directory)
        env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))
        baseline = directory / '.lake/boundary-baseline'
        checker = [sys.executable, '-m',
                   'solidity_differential.check_reference_argument_rejections']
        positive = subprocess.run(checker + ['--output', str(baseline)],
            cwd=directory, env=env, capture_output=True, text=True, timeout=900)
        (root / 'baseline.log').write_text(positive.stdout + positive.stderr)
        if positive.returncode or not (baseline / 'complete.json').exists():
            raise HarnessError(f'{name}: positive rejection suite failed')
        source = directory / 'Compiler/SolidityImport/Import.lean'
        original = source.read_text()
        if original.count(anchor) != 1:
            raise HarnessError(f'{name}: mutation anchor not unique')
        source.write_text(original.replace(anchor, replacement))
        command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
                timeout=600, log=root / 'build.log')
        admitted = subprocess.run(['lake', 'env', 'lean', str(baseline / name / 'Check.lean')],
            cwd=directory, env=env, capture_output=True, text=True, timeout=180)
        (root / 'admitted.log').write_text(admitted.stdout + admitted.stderr)
        if admitted.returncode:
            raise HarnessError(f'{name}: mutant did not admit unsupported input')
        check = subprocess.run(checker + ['--output', str(directory / '.lake/boundary-mutated')],
            cwd=directory, env=env, capture_output=True, text=True, timeout=900)
        log = check.stdout + check.stderr
        (root / 'detected.log').write_text(log)
        if check.returncode == 0 or f'{name}: expected Case.sol:' not in log:
            raise HarnessError(f'{name}: suite did not detect admission')
        result = {'mutant': name, 'baselinePassed': True, 'detected': True,
                  'unsupportedInputImported': True,
                  'mode': 'located rejection regression, not runtime differential'}
        write_json(root / 'complete.json', result)
        results.append(result)
    write_json(output / 'complete.json', {'exit': 0, 'results': results})


if __name__ == '__main__':
    main()
