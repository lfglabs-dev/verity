"""Transient state with structured low-level call helpers and hashed-base transient words.

Runs `TransientStructuredAssemblySequence.sol` through source EVM (A), the Denote model (B)
and the compiled model (C). Each closure accesses transient state variables and also runs
inline assembly the importer admits only in its structured shapes: a `staticcall` or a
value-free `call` over a `bytes memory` local, `returndatasize`, the free-pointer revert
bubble, and single transient word accesses at bases `>= 2^128` (direct, plus a literal, or
plus a masked full-word index). The call targets are recording responders
(`ExternalCodeAndLowLevelCallResponder.sol` on the EVM side, `recording-call-responder-v1`
in Denote), one account without code and the sender EOA. A staticcall into a responder
fails because its fallback writes storage, so both failure branches are exercised. Every RPC
transaction is its own EVM transaction, so transient storage starts cleared each time.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/TransientStructuredAssemblySequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/TransientStructuredAssemblySequenceModel.lean')
RESPONDER = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol')
CONTRACT = 'TransientStructuredAssemblySequence'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
# (response word, failed, response length)
RESPONDERS = [
    (1, False, 32),
    (0, False, 0),
    (7, False, 64),
    (1, True, 4),
    (0, True, 0),
    (5, True, 100),
]
EMPTY = '0x' + '00' * 19 + '77'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "TransientStructuredAssemblySequence.sol"'
ROOTS = ['lockedProbe(address,bytes)', 'renamedProbe(address,bytes)', 'guardedCall(address,bytes)',
         'guardedCallReturn(address,uint256,bytes)', 'queueSum(uint256,uint256)',
         'queueAt(uint256)', 'queueRevert(uint256)', 'state()',
         'unmaskedWriteAndRead(uint256,uint256)']
QUEUE_BASE = int.from_bytes(keccak(text='verity.fixture.transient.queue'), 'big')


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def transactions_for(count, seed, caller, responders):
    targets = [*responders, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []

    def add(function, types, values):
        index = len(calls)
        payload = encode(types, values)
        words = [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)]
        calls.append({'id': str(index), 'function': function[:function.index('(')], 'args': words,
                      'sender': SENDER, 'target': caller,
                      'data': '0x' + keccak(text=function)[:4].hex() + payload.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(responders) + 2 + index})

    def payload():
        return rng.choice([b'', b'\x12\x34\x56\x78', rng.getrandbits(8 * 36).to_bytes(36, 'big'),
                           rng.getrandbits(8 * 64).to_bytes(64, 'big')])

    # Deterministic prefix: every target through every call shape, then the queue.
    for target in targets:
        for function in ROOTS[:3]:
            add(function, ['address', 'bytes'], [target, b'\xaa\xbb\xcc\xdd' + bytes(32)])
        add(ROOTS[3], ['address', 'uint256', 'bytes'],
            [target, 0, b'\xaa\xbb\xcc\xdd' + bytes(32)])
    for a, b in [(3, 4), (2 ** 256 - 1, 1), (0, 0)]:
        add('queueSum(uint256,uint256)', ['uint256', 'uint256'], [a, b])
    for index in [0, 1, 255, 256, 2 ** 256 - 1]:
        add('queueAt(uint256)', ['uint256'], [index])
    add('queueRevert(uint256)', ['uint256'], [9])
    add('unmaskedWriteAndRead(uint256,uint256)', ['uint256', 'uint256'], [5, 77])
    add('unmaskedWriteAndRead(uint256,uint256)', ['uint256', 'uint256'], [2 ** 256 - QUEUE_BASE, 2])
    add('state()', [], [])
    while len(calls) < count:
        choice = rng.randrange(8)
        if choice < 3:
            add(ROOTS[choice], ['address', 'bytes'], [rng.choice(targets), payload()])
        elif choice == 3:
            add(ROOTS[3], ['address', 'uint256', 'bytes'], [rng.choice(targets), 0, payload()])
        elif choice == 4:
            add('queueSum(uint256,uint256)', ['uint256', 'uint256'],
                [rng.getrandbits(rng.choice([8, 255])), rng.getrandbits(8)])
        elif choice == 5:
            add('queueAt(uint256)', ['uint256'], [rng.choice([0, 1, 256, rng.getrandbits(256)])])
        elif choice == 6:
            add('queueRevert(uint256)', ['uint256'], [rng.getrandbits(64)])
        else:
            add('state()', [], [])
    return calls


def campaign(directory, transactions, seed, shrink_attempts, solc=SOLC):
    """Run the fixture; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    source = (root / FIXTURE).read_text()
    template = (root / DRIVER).read_text()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported transient structured assembly source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source},
                    RESPONDER.name: {'content': (root / RESPONDER).read_text()}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][CONTRACT]
    identifiers = caller_contract['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in ROOTS])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    caller_a = '0x' + caller_contract['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    mock = compiled[RESPONDER.name]['RecordingCallResponder']['evm']
    runtime = '0x' + mock['deployedBytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(RESPONDERS))]
    responders = ['0x' + mock['bytecode']['object'] + encode(['uint256', 'bool', 'uint256'], list(p)).hex()
                  for p in RESPONDERS]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
               for account, parameters in zip(accounts, RESPONDERS, strict=True)
               for slot, value in enumerate(parameters)]
    calls = transactions_for(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'recording-call-responder-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))], 'gas': '1000000'}
    adapters = {
        'source': EVM(directory / 'A', [caller_a, *responders], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment,
                        account_code=[(account, runtime) for account in accounts]),
        'compiled': EVM(directory / 'C', [caller_c, *responders], initial)}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed,
              'responders': [[str(v) for v in p] for p in RESPONDERS], 'empty': EMPTY,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    rows = result['observations']['source']
    if {row['status'] for row in rows} != {'ok', 'revert'}:
        raise HarnessError('campaign must exercise both successful and reverting calls')
    # The bubbled child revert of a failing responder (100 bytes) reaches the caller.
    if not any(row['status'] == 'revert' and len(row['data']) == 2 + 200 for row in rows):
        raise HarnessError('campaign must bubble a multi-word child revert payload')
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=96)
    parser.add_argument('--seed', type=int, default=2953)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 4 * (len(RESPONDERS) + 2) + 10
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='transient-structured-assembly-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=True)
    code, report = campaign(output, args.transactions, args.seed, args.shrink_attempts)
    if code:
        raise SystemExit(f'transient structured assembly divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'transient state with structured low-level call helpers and '
                                    'hashed-base transient words: source EVM / Denote / compiled model'})
    print(f'transient structured assembly A/B/C agree on {args.transactions} transactions: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
