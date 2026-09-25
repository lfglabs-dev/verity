"""Execute near-miss inputs against the actual scalar Denote JSON adapter."""
import copy
from pathlib import Path
import tempfile

from .denote import SequenceAdapter
from .engine import HarnessError, write_json


def main():
    output = Path(tempfile.mkdtemp(prefix='denote-rejections-', dir='.lake')).resolve()
    account = '0x' + '11' * 20
    foreign = '0x' + '22' * 20
    slot = '0x' + '00' * 32
    adapter = SequenceAdapter(output / 'runs',
        Path('Contracts/SolidityImportSmoke/SequenceModel.lean'), account)
    valid = {'id': '0', 'function': 'change', 'args': [7], 'sender': foreign,
        'target': account, 'value': '0x0', 'timestamp': 1000000100, 'blockNumber': 2}
    rows = adapter([valid], [[]])
    if rows[0]['status'] != 'ok' or rows[0]['storage'][0][2] != '0x' + format(7, '064x'):
        raise HarnessError('positive Denote rejection-test control failed')
    cases = [
        ('value-transfer', {'value': '0x1'}, [], 'does not yet account for value transfers'),
        ('foreign-target', {'target': foreign}, [], 'foreign model target'),
        ('foreign-observation', {}, [[foreign, slot]], 'foreign storage observation'),
        ('unknown-function', {'function': 'missing'}, [], 'must resolve uniquely'),
        ('missing-argument', {'args': []}, [], 'argument count differs'),
        ('word-overflow', {'args': [1 << 256]}, [], 'uint256 integer'),
        ('duplicate-identity', {}, [], 'unique model transaction ids'),
    ]
    receipts = []
    for name, changes, slots, diagnostic in cases:
        tx = {**copy.deepcopy(valid), **changes}
        transactions = [tx, copy.deepcopy(tx)] if name == 'duplicate-identity' else [tx]
        try:
            adapter(transactions, [slots for _ in transactions])
        except HarnessError as exc:
            if diagnostic not in str(exc):
                raise HarnessError(f'{name}: unexpected failure: {exc}') from exc
            receipts.append({'case': name, 'diagnostic': str(exc)})
        else:
            raise HarnessError(f'{name}: unsupported input was accepted')
    write_json(output / 'rejections.json', receipts)
    print(f'Positive Denote control and {len(cases)} precise rejections passed: {output}')


if __name__ == '__main__':
    main()
