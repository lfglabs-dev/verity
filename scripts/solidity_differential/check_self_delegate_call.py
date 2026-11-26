"""Imported self-dispatch `address(this).delegatecall(...)` through source EVM, Denote and compiled model.

The fixture runs `multicall(bytes[])` and `selfDispatchSingle(bytes)` against its own
external entry points (`addAmount(uint256)` and `failEmpty()`). Route B configures
`imported-model-self-delegate-v1` so Denote replays the imported model's own functions in
the caller's storage with preserved outer `msg.sender` and `msg.value`. Compares storage,
return bytes, outer `msg.sender` preservation, custom-error revert bubbling, empty revert
bubbling, and batch rollback across all three routes.
"""
import argparse
import hashlib
from pathlib import Path
import random
import re
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/SelfDelegateCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/SelfDelegateCallSequenceModel.lean')
CONTRACT = 'SelfDelegateCallFixture'
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "SelfDelegateCallSequence.sol"'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    # Strip Lean guillemets («bytes[]» -> bytes[]).
    return [sig.replace('«', '').replace('»', '') for sig in found]


def call_payload(function, types, values):
    return keccak(text=function)[:4] + encode(types, values)


def transactions_for(count, seed, caller):
    rng = random.Random(seed)
    calls = []

    def add(function, types, values):
        index = len(calls)
        selector = keccak(text=function)[:4].hex()
        name = function[:function.index('(')]
        encoded = encode(types, values)
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                      'target': caller, 'data': '0x' + selector + encoded.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': 2 + index})

    add_ok_1 = call_payload('addAmount(uint256)', ['uint256'], [5])
    add_ok_2 = call_payload('addAmount(uint256)', ['uint256'], [7])
    add_revert = call_payload('addAmount(uint256)', ['uint256'], [0])
    empty_revert = call_payload('failEmpty()', [], [])

    # Deterministic coverage of every self-delegatecall path:
    # 1. Empty batch, single batch, multi-call batch, custom-error revert + rollback,
    #    empty revert + rollback.
    add('multicall(bytes[])', ['bytes[]'], [[]])
    add('multicall(bytes[])', ['bytes[]'], [[add_ok_1]])
    add('read()', [], [])
    add('multicall(bytes[])', ['bytes[]'], [[add_ok_1, add_ok_2]])
    add('read()', [], [])
    add('multicall(bytes[])', ['bytes[]'], [[add_ok_1, add_revert]])
    add('read()', [], [])
    add('multicall(bytes[])', ['bytes[]'], [[add_ok_2, empty_revert]])
    add('read()', [], [])
    # 2. Single self-dispatch: success (returns ABI-encoded uint256), custom error, empty revert.
    add('selfDispatchSingle(bytes)', ['bytes'], [add_ok_2])
    add('selfDispatchSingle(bytes)', ['bytes'], [add_revert])
    add('selfDispatchSingle(bytes)', ['bytes'], [empty_revert])
    add('read()', [], [])

    while len(calls) < count:
        choice = rng.randrange(5)
        amt = rng.choice([0, 1, 3, 11, rng.getrandbits(16)])
        payload = call_payload('addAmount(uint256)', ['uint256'], [amt])
        if choice == 0:
            batch_len = rng.randrange(0, 4)
            items = []
            for _ in range(batch_len):
                kind = rng.randrange(5)
                if kind == 0:
                    items.append(empty_revert)
                elif kind == 1:
                    items.append(add_revert)
                else:
                    items.append(call_payload('addAmount(uint256)', ['uint256'],
                                              [rng.choice([1, 2, 9, rng.getrandbits(16)])]))
            add('multicall(bytes[])', ['bytes[]'], [items])
        elif choice == 1:
            add('selfDispatchSingle(bytes)', ['bytes'],
                [rng.choice([payload, add_revert, empty_revert])])
        elif choice == 2:
            add('addAmount(uint256)', ['uint256'], [amt])
        else:
            add('read()', [], [])
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][CONTRACT]
    identifiers = caller_contract['evm']['methodIdentifiers']
    signatures = roots(template)
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in signatures])
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
    caller = address(0)
    calls = transactions_for(transactions, seed, caller)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'imported-model-self-delegate-v1', 'gas': '1000000'}
    adapters = {
        'source': EVM(directory / 'A', [caller_a], ()),
        'model': Denote(directory / 'B', driver, caller, (), byte_call_environment=environment),
        'compiled': EVM(directory / 'C', [caller_c], ())}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed,
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
    if not any(row['status'] == 'revert' and len(row['data']) > 2 + 8 * 2 for row in rows):
        raise HarnessError('campaign must forward a multi-word child revert payload')
    if not any(row['status'] == 'revert' and row['data'] == '0x' for row in rows):
        raise HarnessError('campaign must forward an empty child revert')
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=48)
    parser.add_argument('--seed', type=int, default=2942)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < 16:
        parser.error('at least 16 transactions cover every self-delegatecall shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='self-delegate-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions,
                       args.seed, args.shrink_attempts)
    if code:
        raise SystemExit(f'Self-delegatecall divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported self-dispatch address(this).delegatecall: '
                                    'source EVM / Denote / compiled model'})
    print(f'Self-delegatecall A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
