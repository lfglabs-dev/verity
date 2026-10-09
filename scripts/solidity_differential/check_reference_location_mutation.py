"""Detect removal of the same-location reference binding guard."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    directory = output / 'import-reference-location-guard'
    snapshot(directory)
    env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))
    baseline = directory / '.lake/location-baseline'
    positive = subprocess.run([sys.executable, '-m',
        'solidity_differential.check_reference_argument_rejections', '--output', str(baseline)],
        cwd=directory, env=env, capture_output=True, text=True, timeout=600)
    (output / 'baseline.log').write_text(positive.stdout + positive.stderr)
    if positive.returncode or not (baseline / 'complete.json').exists():
        raise HarnessError('location mutation positive rejection suite failed')
    source = directory / 'Compiler/SolidityImport/Import.lean'
    original = source.read_text()
    anchor = 'else if location == expected then'
    if original.count(anchor) != 1:
        raise HarnessError('location mutation anchor not unique')
    source.write_text(original.replace(anchor, 'else if true then'))
    command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=600, log=output / 'build.log')
    # A tool error is not detection: require that the unsupported copy actually
    # imports successfully with the guard deleted.
    driver = baseline / 'copy/Check.lean'
    admitted = subprocess.run(['lake', 'env', 'lean', str(driver)], cwd=directory,
        env=env, capture_output=True, text=True, timeout=180)
    (output / 'admitted.log').write_text(admitted.stdout + admitted.stderr)
    if admitted.returncode:
        raise HarnessError('location mutant did not admit the unsupported copy')
    check = subprocess.run([sys.executable, '-m',
        'solidity_differential.check_reference_argument_rejections',
        '--output', str(directory / '.lake/location-mutated')], cwd=directory,
        env=env, capture_output=True, text=True, timeout=600)
    log = check.stdout + check.stderr
    (output / 'detected.log').write_text(log)
    if check.returncode == 0 or 'copy: expected Case.sol:' not in log:
        raise HarnessError('located rejection suite failed to detect admitted copy')
    write_json(output / 'complete.json', {'mutant': 'import-reference-location-guard',
        'detected': True, 'baselinePassed': True, 'unsupportedCopyImported': True,
        'mode': 'located rejection regression, not runtime differential'})


if __name__ == '__main__':
    main()
