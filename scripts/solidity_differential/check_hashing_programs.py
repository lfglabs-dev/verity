"""Generated hashing sources must match A/B/C and each other's exact observations."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
from .engine import HarnessError, write_json
from .programs import abi_hashing_variants


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--variant', action='append', choices=['baseline', 'renamed', 'receiver', 'bound'])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixture = repo / 'Contracts/SolidityImportSmoke'
    variants = abi_hashing_variants((fixture / 'AbiHashing.sol').read_text())
    expected = None
    results = []
    for name, source in variants:
        if args.variant and name not in args.variant:
            continue
        project = output / name / 'fixture'
        project.mkdir(parents=True)
        (project / 'AbiHashing.sol').write_text(source)
        (project / 'AbiHashingModel.lean').write_bytes((fixture / 'AbiHashingModel.lean').read_bytes())
        shutil.copytree(fixture / 'pinned-midnight', project / 'pinned-midnight')
        campaign = output / name / 'abc'
        subprocess.run([sys.executable, '-m', 'solidity_differential.check_abi_hashing',
            '--repo', str(repo), '--fixture-dir', str(project), '--output', str(campaign)],
            cwd=repo, check=True, timeout=1200)
        complete = json.loads((campaign / 'complete.json').read_text())
        if complete['exit'] != 0:
            raise HarnessError('variant did not finish successfully')
        observations = json.loads((campaign / 'campaign.json').read_text())['observations']
        if expected is None:
            expected = observations
        elif observations != expected:
            raise HarnessError(f'{name}: equivalent sources have different observations')
        results.append({'variant': name, 'cases': complete['cases'], 'exit': 0})
        write_json(output / 'results.json', results)
    write_json(output / 'complete.json', {'exit': 0, 'results': results})


if __name__ == '__main__':
    main()
