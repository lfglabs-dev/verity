"""Full reference argument campaign consuming a successful source-EVM receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

from .reference_argument_cases import SIGNATURES


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--fixture-dir', type=Path)
    parser.add_argument('--source-results', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, prior, output = args.repo.resolve(), args.source_results.resolve(), args.output.resolve()
    fixture_dir = args.fixture_dir.resolve() if args.fixture_dir else repo / 'Contracts/SolidityImportSmoke'
    script_dir = Path(__file__).resolve().parent
    fixture = fixture_dir / 'ReferenceArguments.sol'
    os.chdir(repo)
    sys.path.insert(0, str(repo / 'scripts'))
    from solidity_differential.anvil import SequenceAdapter as EVMAdapter
    from solidity_differential.denote import SequenceAdapter as DenoteAdapter
    from solidity_differential.engine import HarnessError, SOLC, command, solc_compile, write_json
    from solidity_differential.identity import ImplementationIdentity
    from solidity_differential.stateful import replay_three_routes, shrink_sequence

    receipt = json.loads((prior / 'complete.json').read_text())
    provenance = json.loads((prior / 'provenance.json').read_text())
    cases = json.loads((prior / 'cases.json').read_text())
    checks = json.loads((prior / 'expectations.json').read_text())
    artifacts = {name: digest(prior / name)
                 for name in ('source.input.json', 'source.output.json', 'cases.json',
                              'expectations.json', 'provenance.json')}
    if receipt != {'scope': 'source EVM only', 'cases': len(cases), 'replays': 2,
                   'exit': 0, 'artifacts': artifacts}:
        raise HarnessError('complete source-EVM receipt required')
    if checks['failures'] or checks['observations'] != [case['expected'] for case in cases]:
        raise HarnessError('source receipt does not establish expected observations')
    for key, path in [('sourceSha256', fixture), ('corpusSha256', script_dir / 'reference_argument_cases.py'),
                      ('solcSha256', SOLC), ('runnerSha256', script_dir / 'check_reference_argument_source.py')]:
        if provenance[key] != digest(path):
            raise HarnessError(f'source receipt identity changed: {key}')
    if provenance['anvilVersion'] != command(['anvil', '--version']).strip():
        raise HarnessError('Anvil version differs from source receipt')
    output.mkdir(parents=True, exist_ok=False)
    source = json.loads((prior / 'source.output.json').read_text())['contracts'][fixture.name]['ReferenceArguments']['evm']
    template = (fixture_dir / 'ReferenceArgumentsModel.lean').read_text()
    anchor = '"Contracts/SolidityImportSmoke"'
    if template.count(anchor) != 1:
        raise HarnessError('unique imported source path required')
    driver = output / 'Driver.lean'
    driver.write_text(template.replace(anchor, json.dumps(str(fixture_dir))))
    identity = ImplementationIdentity(driver, extra_inputs=[fixture, script_dir / 'reference_argument_cases.py'])
    write_json(output / 'implementation.json', identity.manifest)
    write_json(output / 'selectors.json', [int(source['methodIdentifiers'][sig], 16) for sig in SIGNATURES])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            timeout=600, log=output / 'compile.log')
    identity.verify()
    compiled = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture_dir, output / 'compiled')
    objects = list(compiled['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('one compiled model required')
    transactions = [case['transaction'] for case in cases]
    account = transactions[0]['target']
    adapters = {'source': EVMAdapter(output / 'A', ['0x' + source['bytecode']['object']]),
        'model': DenoteAdapter(output / 'B', driver, account, identity=identity),
        'compiled': EVMAdapter(output / 'C', ['0x' + objects[0]['evm']['bytecode']['object']])}
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        reduced = shrink_sequence(transactions,
            lambda txs: replay_three_routes(txs, adapters)['divergences'], max_attempts=1000)
        identity.verify()
        write_json(output / 'reduced.json', reduced)
        raise HarnessError('reference argument A/B/C divergence; witness retained')
    if any(digest(prior / name) != expected for name, expected in artifacts.items()):
        raise HarnessError('source receipt artifacts changed during A/B/C execution')
    if result['observations']['source'] != checks['observations']:
        raise HarnessError('source observations changed from prerequisite receipt')
    write_json(output / 'complete.json', {'scope': 'reference argument A/B/C', 'cases': len(cases),
        'sourceReceipt': str(prior), 'sourceReceiptSha256': digest(prior / 'complete.json'), 'exit': 0})
    print(f'{len(cases)} reference argument cases agree across A/B/C: {output}')


if __name__ == '__main__':
    main()
