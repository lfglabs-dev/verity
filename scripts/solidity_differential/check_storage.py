"""Run actual imported packed storage variants through all three stateful routes."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

from .engine import command, write_json
from .programs import stateful_storage_source, stateful_storage_word_source, stateful_mapping_source
from .stateful import validate_observation


def canonical_observations(observations):
    """Slot order is not observable; retain every key/value and ordered event."""
    result = {}
    for route, rows in observations.items():
        result[route] = []
        for row in rows:
            touched, storage = validate_observation(row)
            result[route].append({**row,
                'touched': [list(key) for key in sorted(touched)],
                'storage': [[*key, storage[key]] for key in sorted(storage)]})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', choices=('packed', 'void', 'bytes', 'mapping'), default='packed')
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--seed', type=int, default=2453)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='storage-', dir='.lake')).resolve()
    output.mkdir(parents=True, exist_ok=args.output is None)
    name = {'packed': 'StorageSequence', 'void': 'StorageVoidSequence', 'bytes': 'StorageBytesSequence', 'mapping': 'MappingSequence'}[args.fixture]
    fixture = Path(f'Contracts/SolidityImportSmoke/{name}.sol').read_text()
    template = Path(f'Contracts/SolidityImportSmoke/{name}Model.lean').read_text()
    anchor = f'from "Contracts/SolidityImportSmoke" entry "{name}.sol"'
    if template.count(anchor) != 1:
        raise RuntimeError('nonunique imported storage source anchor')
    completed = []
    baseline = None
    variants = ('baseline', 'bindings', 'reordered' if args.fixture in ('packed', 'mapping') else 'expression')
    for variant in variants:
        directory = output / variant
        directory.mkdir()
        source = directory / 'Sequence.sol'
        source.write_text(stateful_mapping_source(fixture, variant) if args.fixture == "mapping"
                          else stateful_storage_source(fixture, variant) if args.fixture == "packed"
                          else stateful_storage_word_source(fixture, variant, args.fixture))
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_stateful',
                 '--model-driver', driver, '--source-fixture', source,
                 '--senders', '3', '--transactions', str(args.transactions), '--seed', str(args.seed),
                 '--output', directory / 'campaign'], timeout=1800, log=directory / 'check.log')
        result = json.loads((directory / 'campaign' / 'campaign.json').read_text())
        observable = {'transactions': result['transactions'],
                      'observations': canonical_observations(result['observations'])}
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json',
                       {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise RuntimeError(f'storage variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    print(f'Imported storage variants agree: {output}')


if __name__ == '__main__':
    main()
