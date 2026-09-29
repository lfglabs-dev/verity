"""Detect an executable model mutation and verify real A/B/C sequence reduction."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from .engine import HarnessError, write_json


def main():
    output = Path(tempfile.mkdtemp(prefix='stateful-mutations-', dir='.lake')).resolve()
    original = Path('Contracts/SolidityImportSmoke/SequenceModel.lean').read_text()
    before = '.setStorage "stored" (.param "value")'
    after = '.setStorage "stored" (.literal 0)'
    if original.count(before) != 1:
        raise HarnessError('write-zero mutation anchor is not unique')
    driver = output / 'MutatedSequence.lean'
    driver.write_text(original.replace(before, after))
    campaign = output / 'campaign'
    argv = [sys.executable, '-m', 'solidity_differential.check_stateful',
            '--model-driver', str(driver), '--output', str(campaign),
            '--transactions', '6', '--seed', '2448', '--shrink-attempts', '30']
    result = subprocess.run(argv, text=True, capture_output=True, timeout=600)
    (output / 'campaign.log').write_text(result.stdout + result.stderr)
    # Tool/build failures cannot count as detection: require a completed comparison
    # and the reducer's separately reproduced, deletion-minimal semantic witness.
    if result.returncode == 0:
        raise HarnessError('write-zero model mutation survived')
    full = json.loads((campaign / 'campaign.json').read_text())
    reduced = json.loads((campaign / 'reduced.json').read_text())
    if not full['divergences'] or not reduced['deletion_minimal']:
        raise HarnessError('mutation did not produce a minimal semantic divergence')
    witness = reduced['transactions']
    if len(witness) != 1 or witness[0]['function'] != 'change' or witness[0]['args'] == [0]:
        raise HarnessError('unexpected minimal write-zero witness')
    expected = [['storage', False, True, False]]
    if reduced['signature'] != expected:
        raise HarnessError('expected A to disagree with both mutated model routes on storage')
    write_json(output / 'receipt.json', {'mutation': 'model-write-zero', 'detected': True,
        'command': argv, 'witness': witness, 'signature': reduced['signature'],
        'attempts': reduced['attempts'], 'deletionMinimal': True})
    print(f'Executable write-zero mutation detected and reduced to one transaction: {output}')


if __name__ == '__main__':
    main()
