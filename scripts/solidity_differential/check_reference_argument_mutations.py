"""Detect wrong internal reference roots through the real composition A/B/C routes."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    directory = output / 'import-reference-wrong-root'
    snapshot(directory)
    env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))

    def run(label):
        target = directory / '.lake' / label
        result = subprocess.run([sys.executable, '-m',
            'solidity_differential.check_reference_arguments', '--variant', 'baseline',
            '--output', str(target)], cwd=directory, env=env, capture_output=True,
            text=True, timeout=1200)
        (output / (label + '.log')).write_text(result.stdout + result.stderr)
        return result.returncode, target / 'baseline' / 'abc'

    code, baseline = run('baseline')
    if code or not (baseline / 'complete.json').is_file():
        raise HarnessError('reference mutation positive control failed')
    source = directory / 'Compiler/SolidityImport/Import.lean'
    text = source.read_text()
    anchor = 'e.mems.insert pid descriptor'
    if text.count(anchor) != 1:
        raise HarnessError('reference mutation anchor not unique')
    source.write_text(text.replace(anchor, 'e.mems.insert pid ((saved.mems.toList.head?.map Prod.snd).getD descriptor)'))
    command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=600, log=output / 'build.log')
    code, campaign = run('mutated')
    if not (campaign / 'campaign.json').is_file():
        raise HarnessError('reference mutation tool failure is not detection')
    report = json.loads((campaign / 'campaign.json').read_text())
    if not code or not report['divergences']:
        raise HarnessError('reference mutation survived')
    witness = json.loads((campaign / 'reduced.json').read_text())
    if not witness['deletion_minimal'] or not witness['transactions']:
        raise HarnessError('reference mutation lacks minimal runtime witness')
    write_json(output / 'complete.json', {'mutant': 'import-reference-wrong-root',
        'detected': True, 'baselinePassed': True, 'witness': witness})
    print('import-reference-wrong-root detected and reduced')


if __name__ == '__main__':
    main()
