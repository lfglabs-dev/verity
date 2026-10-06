"""Compare generated scalar-array ABI variants using public Denote and real EVMs."""
import argparse
import json
from pathlib import Path
import sys
from .engine import command, write_json, HarnessError
from .programs import abi_length_for_source
from .check_storage import canonical_observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path('Contracts/SolidityImportSmoke/ArrayForAbi.sol').read_text()
    template = Path('Contracts/SolidityImportSmoke/ArrayForAbiModel.lean').read_text()
    anchor = 'from "Contracts/SolidityImportSmoke" entry "ArrayForAbi.sol"'
    if template.count(anchor) != 1:
        raise HarnessError('nonunique ABI source anchor')
    baseline = None
    for variant in ('baseline', 'renamed', 'assignment-step'):
        directory = output / variant
        directory.mkdir()
        fixture = directory / 'ArrayForAbi.sol'
        fixture.write_text(abi_length_for_source(source, variant))
        driver = directory / 'Driver.lean'
        variant_template = template
        if variant == 'renamed':
            # Keep the exact ABI name/type assertion aligned with this source.
            parameter = 'name := "box", ty := .tuple [.array (.uintN 128)]'
            if variant_template.count(parameter) != 1:
                raise HarnessError('nonunique ABI parameter manifest anchor')
            variant_template = variant_template.replace(parameter,
                'name := "box_renamed", ty := .tuple [.array (.uintN 128)]')
        driver.write_text(variant_template.replace(anchor,
            f'from "{directory}" entry "ArrayForAbi.sol"'))
        command([sys.executable, '-m', 'solidity_differential.check_scalar_array_abi',
            '--source-fixture', fixture, '--model-driver', driver,
            '--output', directory / 'campaign'], timeout=1800, log=directory / 'check.log')
        report = json.loads((directory / 'campaign/campaign.json').read_text())
        if len(report['transactions']) != 128:
            raise HarnessError('incomplete ABI variant control matrix')
        observable = {'transactions': report['transactions'],
            'observations': canonical_observations(report['observations'])}
        if baseline is None:
            baseline = observable
        elif baseline != observable:
            write_json(output / 'metamorphic-divergence.json',
                {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise HarnessError('ABI variant changed observable behavior')
    write_json(output / 'complete.json', {'exit': 0, 'variants': 3, 'cases': 384})
    print(f'All scalar-array ABI variants agree: {output}')


if __name__ == '__main__':
    main()
