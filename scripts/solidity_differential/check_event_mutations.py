"""Require real EVM/model disagreement for event omission, indexing and ordering."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from .engine import HarnessError, write_json


def main():
    output = Path(tempfile.mkdtemp(prefix='stateful-event-mutants-', dir='.lake')).resolve()
    original = Path('Contracts/SolidityImportSmoke/EventSequenceModel.lean').read_text()
    mutations = {
        'wrong-indexing': ('{ name := "previous", ty := .uint256, kind := .indexed }',
                           '{ name := "previous", ty := .uint256, kind := .unindexed }'),
        'reversed-arguments': ('.emit "Changed" [.localVar "old", .param "value"]',
                               '.emit "Changed" [.param "value", .localVar "old"]'),
        'missing-event': ('.emit "Changed" [.localVar "old", .param "value"],', ''),
    }
    receipts = []
    for name, (before, after) in mutations.items():
        if original.count(before) != 1:
            raise HarnessError(f'event mutation anchor is not unique: {name}')
        driver = output / (name + '.lean')
        driver.write_text(original.replace(before, after))
        campaign = output / name
        argv = [sys.executable, '-m', 'solidity_differential.check_stateful',
                '--model-driver', str(driver), '--output', str(campaign),
                '--source-fixture', 'scripts/solidity_differential/fixtures/EventSequence.sol',
                '--transactions', '3', '--seed', '2450', '--shrink-attempts', '15']
        result = subprocess.run(argv, text=True, capture_output=True, timeout=600)
        (output / (name + '.log')).write_text(result.stdout + result.stderr)
        if result.returncode == 0:
            raise HarnessError(f'event mutation survived: {name}')
        full = json.loads((campaign / 'campaign.json').read_text())
        reduced = json.loads((campaign / 'reduced.json').read_text())
        if not full['divergences'] or not reduced['deletion_minimal']:
            raise HarnessError(f'no minimal semantic witness for {name}')
        if reduced['signature'] != [['events', False, True, False]]:
            raise HarnessError(f'wrong divergence signature for {name}')
        if len(reduced['transactions']) != 1 or reduced['transactions'][0]['function'] != 'change':
            raise HarnessError(f'wrong minimal witness for {name}')
        receipts.append({'mutation': name, 'command': argv, **reduced})
        write_json(output / 'receipts.json', receipts)
    print(f'Three executable event mutations detected and reduced: {output}')


if __name__ == '__main__':
    main()
