"""Validate ABI/storage/event composition against source EVM and all three routes."""
import argparse
from pathlib import Path
import subprocess
import sys
from .programs import abi_event_variants


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--variant', choices=['baseline', 'renamed', 'scoped', 'lexical'])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = repo / 'Contracts/SolidityImportSmoke'
    original = (fixture / 'AbiEventComposition.sol').read_text()
    for variant, source in abi_event_variants(original):
        if args.variant and variant != args.variant:
            continue
        variant_dir = output / variant
        inputs = variant_dir / 'fixture'
        inputs.mkdir(parents=True)
        (inputs / 'AbiEventComposition.sol').write_text(source)
        (inputs / 'AbiEventCompositionModel.lean').write_bytes(
            (fixture / 'AbiEventCompositionModel.lean').read_bytes())
        for module, target, extra in [
            ('check_abi_event_source', 'source', []),
            ('check_abi_event_abc', 'abc', ['--source-results', str(variant_dir / 'source')]),
        ]:
            subprocess.run([sys.executable, '-m', 'solidity_differential.' + module,
                            '--repo', str(repo), '--fixture-dir', str(inputs),
                            '--output', str(variant_dir / target), *extra], cwd=repo, check=True)



if __name__ == '__main__':
    main()
