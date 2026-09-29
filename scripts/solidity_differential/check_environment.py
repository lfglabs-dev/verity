"""Run actual imported context variants through all three stateful routes."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

from .engine import command, write_json
from .programs import stateful_environment_source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--seed', type=int, default=2452)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='environment-', dir='.lake')).resolve()
    output.mkdir(parents=True, exist_ok=args.output is None)
    fixture = Path('Contracts/SolidityImportSmoke/EnvironmentSequence.sol').read_text()
    template = Path('Contracts/SolidityImportSmoke/EnvironmentSequenceModel.lean').read_text()
    anchor = 'from "Contracts/SolidityImportSmoke" entry "EnvironmentSequence.sol"'
    if template.count(anchor) != 1:
        raise RuntimeError('nonunique imported environment source anchor')
    completed = []
    baseline = None
    for variant in ('baseline', 'bindings', 'helpers'):
        directory = output / variant
        directory.mkdir()
        source = directory / 'Sequence.sol'
        source.write_text(stateful_environment_source(fixture, variant))
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_stateful',
                 '--model-driver', driver, '--source-fixture', source,
                 '--senders', '3', '--transactions', str(args.transactions), '--seed', str(args.seed),
                 '--output', directory / 'campaign'], timeout=1800, log=directory / 'check.log')
        result = json.loads((directory / 'campaign' / 'campaign.json').read_text())
        observable = {key: result[key] for key in ('transactions', 'observations')}
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json',
                       {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise RuntimeError(f'environment variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    print(f'Imported environment variants agree: {output}')


if __name__ == '__main__':
    main()
