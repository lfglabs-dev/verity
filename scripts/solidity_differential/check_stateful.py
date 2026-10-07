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
    parser.add_argument('--dirty-mappings', action='store_true',
        help='seed the MappingDirtySequence layout with noncanonical low bytes and nonzero upper bits')
    parser.add_argument('--argument-bits', type=int, default=256,
        help='unsigned width of the change argument; generates canonical ABI words')
    parser.add_argument('--change-prefix', type=int, nargs='+', default=[],
        help='deterministic initial change arguments before random calls')
    parser.add_argument('--seed', type=int, default=2448)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--senders', type=int, default=1, help='number of funded transaction senders (1 to 10)')
    parser.add_argument('--shrink-attempts', type=int, default=1000)
    parser.add_argument('--model-driver', type=Path,
        default=Path('Contracts/SolidityImportSmoke/SequenceModel.lean'))
    parser.add_argument('--solc-version', choices=('0.8.34', '0.8.10'), default='0.8.34')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--source-fixture', type=Path,
        default=Path(__file__).parent / 'fixtures/Sequence.sol')
    args = parser.parse_args()
    if args.argument_bits not in range(8, 257, 8):
        parser.error('argument width must be a byte-aligned unsigned width from 8 to 256')
    if args.dirty_mappings and args.argument_bits != 256:
        parser.error('dirty mapping fixture requires uint256 arguments')
    if not 1 <= args.senders <= 10:
        parser.error('sender count must be between one and ten')
    if args.transactions < 3 or args.shrink_attempts < 2:
        parser.error('at least three transactions and two shrink attempts required')
    if args.dirty_mappings and args.transactions < 5:
        parser.error('dirty mapping coverage requires at least five transactions')
    if any(value < 0 or value >= (1 << args.argument_bits) for value in args.change_prefix):
        parser.error('change prefix values must fit the argument width')
    if len(args.change_prefix) > args.transactions - 3:
        parser.error('change prefix exceeds the transaction budget')
    if args.dirty_mappings and args.change_prefix:
        parser.error('change prefix cannot replace the dirty mapping witness prefix')
    if args.output is None:
        output = Path(tempfile.mkdtemp(prefix='stateful-abc-', dir='.lake')).resolve()
    else:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    fixture = args.source_fixture.resolve()
    source_text = stateful_scalar_source(fixture.read_text(), args.variant)
    solc_bin = SOLC if args.solc_version == '0.8.34' else SOLC.with_name('solc-0.8.10')
    evm_version = 'osaka' if args.solc_version == '0.8.34' else 'london'
    optimizer_runs = 466 if args.solc_version == '0.8.34' else 1
    source_settings = {'evmVersion': evm_version,
        'optimizer': {'enabled': True, 'runs': optimizer_runs},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}
    if args.solc_version == '0.8.34':
        source_settings['viaIR'] = True
    request = {'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source_text}},
        'settings': source_settings}
    source = solc_compile(request, fixture.parent, output / 'source', solc=solc_bin)['contracts']['Sequence.sol']['SequenceFixture']['evm']
    names = [f'change(uint{args.argument_bits})', 'fail()', 'read()']
    for extra_name in ('inspectBytes(bytes,uint256)', 'redeemRewards(bytes)', 'getRewardTokens()'):
        if extra_name in source['methodIdentifiers']:
            names.append(extra_name)
    write_json(output / 'selectors.json', [int(source['methodIdentifiers'][name], 16) for name in names])
    driver = args.model_driver.resolve()
    extra_inputs = [fixture]
    imported_dep = fixture.parent / 'Solc0810Imported.sol'
    if imported_dep.exists():
        extra_inputs.append(imported_dep)
    identity = ImplementationIdentity(driver, extra_inputs=extra_inputs)
    write_json(output / 'implementation.json', identity.manifest)
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            log=output / 'compile-model.log')
    identity.verify()
    compiled = solc_compile({'language': 'Yul', 'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': evm_version, 'optimizer': {'enabled': True, 'runs': optimizer_runs},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture.parent, output / 'compiled', solc=solc_bin)
    objects = list(compiled['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled object')
    source_code = '0x' + source['bytecode']['object']
    compiled_code = '0x' + objects[0]['evm']['bytecode']['object']
    with Anvil(output / 'deployment-discovery') as node:
        senders = node.rpc('eth_accounts')[:args.senders]
        if len(senders) != args.senders:
            raise HarnessError('Anvil did not provide the requested funded senders')
        sender = senders[0]
        deployed = node.transact({'from': sender, 'data': source_code, 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('source fixture deployment failed')
        account = deployed['receipt']['contractAddress']
        initial_storage = []
        if args.dirty_mappings:
            def mapping_slot(base, key):
                return int(node.rpc('web3_sha3', '0x' + format(key, '064x') + format(base, '064x')), 16)
            dirty = (0xabcdef << 232) | (0x123456 << 128) | 0x102
            slots = {mapping_slot(3, 7)}
            for owner in senders:
                key = int(owner, 16)
                slots.update((mapping_slot(0, key),
                    mapping_slot(mapping_slot(1, key), int(account, 16)),
                    mapping_slot(mapping_slot(2, key), 7)))
            initial_storage = [[account, '0x' + format(slot, '064x'),
                                '0x' + format(dirty, '064x')] for slot in sorted(slots)]
    write_json(output / 'initial-storage.json', initial_storage)
    rng = random.Random(args.seed)
    calls = [(names[0], [7]), ('fail()', []), ('read()', [])]
    calls.extend((names[0], [value]) for value in args.change_prefix)
    if 'inspectBytes(bytes,uint256)' in source['methodIdentifiers']:
        bytes_prefix = [
            ('getRewardTokens()', []),
            ('redeemRewards(bytes)', [32, 0]),
            ('redeemRewards(bytes)', [32, 5, 0x1122334455 << 216]),
            ('redeemRewards(bytes)', [32, 33, 1]),
            ('redeemRewards(bytes)', [64, 0]),
            ('inspectBytes(bytes,uint256)', [64, 7, 0]),
            ('inspectBytes(bytes,uint256)', [64, 9, 5, 0xdeadbeef01 << 216]),
            ('inspectBytes(bytes,uint256)', [64, 11, 32, (1 << 256) - 1]),
            ('inspectBytes(bytes,uint256)', [64, 13, 33, 1]),
            ('inspectBytes(bytes,uint256)', [64, 15, 1 << 64, 0]),
            ('inspectBytes(bytes,uint256)', [1 << 64, 17, 0]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(bytes_prefix[:remaining_budget])
    while len(calls) < args.transactions:
        name = rng.choice(names)
        if name == names[0]:
            call_args = [rng.choice([0, 1, (1 << args.argument_bits) - 1, rng.getrandbits(args.argument_bits)])]
        elif name == 'redeemRewards(bytes)':
            call_args = rng.choice([[32, 0], [32, 5, 0x1122334455 << 216], [32, 32, (1 << 256) - 1], [32, 33, 1], [64, 0]])
        elif name == 'inspectBytes(bytes,uint256)':
            tag = rng.choice([0, 1, 2, 3, 7, 19])
            call_args = rng.choice([[64, tag, 0], [64, tag, 5, 0xdeadbeef01 << 216], [64, tag, 32, (1 << 256) - 1], [64, tag, 33, 1], [64, tag, 1 << 64, 0], [1 << 64, tag, 0]])
        else:
            call_args = []
        calls.append((name, call_args))
    if args.dirty_mappings:
        calls = [('read()', []), ('read()', []), ('change(uint256)', [7]),
                 ('fail()', []), ('read()', [])] + calls[5:]
    sender_rng = random.Random(args.seed)
    transaction_senders = [senders[index] if index < len(senders) else sender_rng.choice(senders)
                           for index in range(len(calls))]
    if args.dirty_mappings:
        transaction_senders[:5] = [senders[0], senders[0], senders[-1], senders[-1], senders[-1]]
    transactions = [{'id': str(index), 'function': name.split('(')[0], 'args': args,
        'sender': transaction_senders[index], 'target': account, 'value': '0x0',
        'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
        'data': '0x' + source['methodIdentifiers'][name] + ''.join(format(arg, '064x') for arg in args)}
        for index, (name, args) in enumerate(calls)]
    adapters = {'source': EVMAdapter(output / 'A', [source_code], initial_storage=initial_storage),
        'model': DenoteAdapter(output / 'B', driver, account, initial_storage=initial_storage, identity=identity),
        'compiled': EVMAdapter(output / 'C', [compiled_code], initial_storage=initial_storage)}
    write_json(output / 'provenance.json', {
        'solcSha256': hashlib.sha256(solc_bin.read_bytes()).hexdigest(),
        'anvilVersion': command(['anvil', '--version']).strip(),
        'leanVersion': command(['lake', 'env', 'lean', '--version']).strip(),
        'sourceSha256': hashlib.sha256(source_text.encode()).hexdigest(),
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
        'variant': args.variant, 'seed': args.seed, 'transactionCount': args.transactions,
        'changePrefix': args.change_prefix, 'argumentBits': args.argument_bits, 'senderCount': args.senders, 'dirtyMappings': args.dirty_mappings,
        'evmVersion': evm_version, 'optimizerRuns': optimizer_runs})
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'seed': args.seed, 'transactions': transactions, **result})
    if args.dirty_mappings and not result['divergences']:
        # Guarantee both bool normalization cases actually executed before accepting coverage.
        rows = result['observations']['source']
        for index, expected in ((0, 1), (1, 0)):
            row = rows[index]
            if row['status'] != 'ok' or len(row['data']) != 258 or int(row['data'][66:130], 16) != expected:
                raise HarnessError('dirty mapping prefix did not observe the required bool values')
    if result['divergences']:
        reduced = shrink_sequence(transactions,
            lambda candidate: replay_three_routes(candidate, adapters)['divergences'],
            max_attempts=args.shrink_attempts)
        write_json(output / 'reduced.json', reduced)
        raise HarnessError(f"stateful A/B/C divergence: {output / 'campaign.json'}")
    print(f'{args.transactions} real A/B/C transactions agree; discovery and replay: {output}')


if __name__ == '__main__':
    main()
