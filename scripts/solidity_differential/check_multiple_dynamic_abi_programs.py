"""Compare generated multiple-root ABI variants using public Denote and real EVMs."""
import argparse
import json
from pathlib import Path
import sys
from .engine import command, write_json, HarnessError
from .programs import multiple_dynamic_abi_source
from .check_storage import canonical_observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path('Contracts/SolidityImportSmoke/MultipleDynamicAbi.sol').read_text()
    template = Path('Contracts/SolidityImportSmoke/MultipleDynamicAbiModel.lean').read_text()
    anchor = 'from "Contracts/SolidityImportSmoke" entry "MultipleDynamicAbi.sol"'
    if template.count(anchor) != 1:
        raise HarnessError('nonunique ABI source anchor')
    baseline = None
    for variant in ('baseline', 'members', 'bindings', 'condition'):
        directory = output / variant
        directory.mkdir()
        fixture = directory / 'MultipleDynamicAbi.sol'
        fixture.write_text(multiple_dynamic_abi_source(source, variant))
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "MultipleDynamicAbi.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_multiple_dynamic_abi',
            '--source-fixture', fixture, '--model-driver', driver,
            '--output', directory / 'campaign'], timeout=1800, log=directory / 'check.log')
        report = json.loads((directory / 'campaign/campaign.json').read_text())
        observable = {'transactions': report['transactions'],
            'observations': canonical_observations(report['observations'])}
        if baseline is None:
            baseline = observable
        elif baseline != observable:
            write_json(output / 'metamorphic-divergence.json',
                {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise HarnessError('ABI variant changed observable behavior')
    write_json(output / 'complete.json', {'exit': 0, 'variants': 4, 'cases': 528})
    print(f'All multiple-root ABI variants agree: {output}')


if __name__ == '__main__':
    main()
