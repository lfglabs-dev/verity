"""Compare generated scalar-array ABI variants using public Denote and real EVMs."""
import argparse
import json
from pathlib import Path
import sys
from .engine import command, write_json, HarnessError
from .programs import scalar_array_abi_source
from .check_storage import canonical_observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path('Contracts/SolidityImportSmoke/ScalarArrayAbi.sol').read_text()
    template = Path('Contracts/SolidityImportSmoke/ScalarArrayAbiModel.lean').read_text()
    anchor = 'from "Contracts/SolidityImportSmoke" entry "ScalarArrayAbi.sol"'
    if template.count(anchor) != 1:
        raise HarnessError('nonunique ABI source anchor')
    baseline = None
    for variant in ('baseline', 'renamed', 'bindings'):
        directory = output / variant
        directory.mkdir()
        fixture = directory / 'ScalarArrayAbi.sol'
        fixture.write_text(scalar_array_abi_source(source, variant))
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "ScalarArrayAbi.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_scalar_array_abi',
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
    write_json(output / 'complete.json', {'exit': 0, 'variants': 3, 'cases': 288})
    print(f'All scalar-array ABI variants agree: {output}')


if __name__ == '__main__':
    main()
