"""Verify the composition corpus against real solc EVM before trusting A/B/C.

Run only when the single native campaign slot is available. This is a draft
source-only prerequisite, not a complete importer or A/B/C validation.
"""
import argparse
import hashlib
import os
from pathlib import Path
import sys

from .abi_event_cases import sequence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--fixture-dir', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    fixture = (args.fixture_dir.resolve() if args.fixture_dir else
               args.repo.resolve() / 'Contracts/SolidityImportSmoke') / 'AbiEventComposition.sol'
    corpus = Path(__file__).resolve().with_name('abi_event_cases.py')
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    os.chdir(repo)
    sys.path.insert(0, str(repo / 'scripts'))
    from solidity_differential.anvil import Anvil, SequenceAdapter
    from solidity_differential.engine import HarnessError, SOLC, command, solc_compile, write_json
    from solidity_differential.stateful import validate_observation

    source_text = fixture.read_text()
    source_digest = hashlib.sha256(fixture.read_bytes()).hexdigest()
    corpus_digest = hashlib.sha256(corpus.read_bytes()).hexdigest()
    request = {'language': 'Solidity', 'sources': {fixture.name: {'content': source_text}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    compiled = solc_compile(request, fixture.parent, output / 'source')
    evm = compiled['contracts'][fixture.name]['AbiEventComposition']['evm']
    bytecode = '0x' + evm['bytecode']['object']
    with Anvil(output / 'discovery') as node:
        senders = node.rpc('eth_accounts')[:2]
        deployed = node.transact({'from': senders[0], 'data': bytecode, 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('composition source deployment failed')
        account = deployed['receipt']['contractAddress']
        topic = node.rpc('web3_sha3', '0x' + b'Decoded(address,uint256,uint256)'.hex())
    cases = sequence(evm['methodIdentifiers'], senders, account, topic)
    transactions = [case['transaction'] for case in cases]
    plan = [[[account, '0x' + '00' * 32]] for _ in cases]
    write_json(output / 'cases.json', cases)
    write_json(output / 'provenance.json', {
        'repoHead': command(['git', 'rev-parse', 'HEAD']).strip(),
        'sourceSha256': source_digest, 'corpusSha256': corpus_digest,
        'runnerSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'solcSha256': hashlib.sha256(SOLC.read_bytes()).hexdigest(),
        'anvilVersion': command(['anvil', '--version']).strip(),
        'scope': 'source EVM expectations only; no Denote or compiled model'})
    adapter = SequenceAdapter(output / 'A', [bytecode])
    observations = adapter(transactions, plan)
    replay = adapter(transactions, plan)
    if observations != replay:
        raise HarnessError('composition source replay is nondeterministic')
    failures = []
    if len(observations) != len(cases):
        raise HarnessError('composition source omitted observations')
    for case, actual in zip(cases, observations):
        validate_observation(actual)
        if actual != case['expected']:
            failures.append({'case': case['case'], 'expected': case['expected'], 'actual': actual})
    write_json(output / 'expectations.json', {'failures': failures, 'observations': observations})
    if hashlib.sha256(fixture.read_bytes()).hexdigest() != source_digest or \
            hashlib.sha256(corpus.read_bytes()).hexdigest() != corpus_digest:
        raise HarnessError('composition source/corpus changed during execution')
    if failures:
        raise HarnessError(f'composition source expectations differ: {output}')
    artifacts = {name: hashlib.sha256((output / name).read_bytes()).hexdigest()
                 for name in ('source.input.json', 'source.output.json', 'cases.json',
                              'expectations.json', 'provenance.json')}
    write_json(output / 'complete.json', {'scope': 'source EVM only', 'cases': len(cases),
                                         'replays': 2, 'exit': 0, 'artifacts': artifacts})
    print(f'{len(cases)} source EVM expectations pass twice; A/B/C still required: {output}')


if __name__ == '__main__':
    main()
