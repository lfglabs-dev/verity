"""Real A/B/C sequence regression for the handwritten scalar instrument fixture."""
import argparse
import hashlib
import random
from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence
from .identity import ImplementationIdentity
from .programs import stateful_scalar_source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant', choices=['baseline', 'scoped', 'early-return'], default='baseline')
    parser.add_argument('--seed', type=int, default=2448)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--shrink-attempts', type=int, default=1000)
    parser.add_argument('--model-driver', type=Path,
        default=Path('Contracts/SolidityImportSmoke/SequenceModel.lean'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < 3 or args.shrink_attempts < 2:
        parser.error('at least three transactions and two shrink attempts required')
    if args.output is None:
        output = Path(tempfile.mkdtemp(prefix='stateful-abc-', dir='.lake')).resolve()
    else:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    fixture = Path(__file__).parent / 'fixtures/Sequence.sol'
    source_text = stateful_scalar_source(fixture.read_text(), args.variant)
    request = {'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source_text}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    source = solc_compile(request, fixture.parent, output / 'source')['contracts']['Sequence.sol']['SequenceFixture']['evm']
    names = ['change(uint256)', 'fail()', 'read()']
    write_json(output / 'selectors.json', [int(source['methodIdentifiers'][name], 16) for name in names])
    driver = args.model_driver.resolve()
    identity = ImplementationIdentity(driver)
    write_json(output / 'implementation.json', identity.manifest)
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            log=output / 'compile-model.log')
    identity.verify()
    compiled = solc_compile({'language': 'Yul', 'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture.parent, output / 'compiled')
    objects = list(compiled['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled object')
    source_code = '0x' + source['bytecode']['object']
    compiled_code = '0x' + objects[0]['evm']['bytecode']['object']
    with Anvil(output / 'deployment-discovery') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': source_code, 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('source fixture deployment failed')
        account = deployed['receipt']['contractAddress']
    rng = random.Random(args.seed)
    calls = [('change(uint256)', [7]), ('fail()', []), ('read()', [])]
    for _ in range(args.transactions - 3):
        name = rng.choice(names)
        call_args = [rng.choice([0, 1, (1 << 256) - 1, rng.getrandbits(256)])] if name == names[0] else []
        calls.append((name, call_args))
    transactions = [{'id': str(index), 'function': name.split('(')[0], 'args': args,
        'sender': sender, 'target': account, 'value': '0x0',
        'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
        'data': '0x' + source['methodIdentifiers'][name] + ''.join(format(arg, '064x') for arg in args)}
        for index, (name, args) in enumerate(calls)]
    adapters = {'source': EVMAdapter(output / 'A', [source_code]),
        'model': DenoteAdapter(output / 'B', driver, account, identity=identity),
        'compiled': EVMAdapter(output / 'C', [compiled_code])}
    write_json(output / 'provenance.json', {
        'solcSha256': hashlib.sha256(SOLC.read_bytes()).hexdigest(),
        'anvilVersion': command(['anvil', '--version']).strip(),
        'leanVersion': command(['lake', 'env', 'lean', '--version']).strip(),
        'sourceSha256': hashlib.sha256(source_text.encode()).hexdigest(),
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
        'variant': args.variant, 'seed': args.seed, 'transactionCount': args.transactions,
        'evmVersion': 'osaka', 'optimizerRuns': 466})
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'seed': args.seed, 'transactions': transactions, **result})
    if result['divergences']:
        reduced = shrink_sequence(transactions,
            lambda candidate: replay_three_routes(candidate, adapters)['divergences'],
            max_attempts=args.shrink_attempts)
        write_json(output / 'reduced.json', reduced)
        raise HarnessError(f"stateful A/B/C divergence: {output / 'campaign.json'}")
    print(f'{args.transactions} real A/B/C transactions agree; discovery and replay: {output}')


if __name__ == '__main__':
    main()
