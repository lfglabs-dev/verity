"""Imported dynamic `T[] calldata` event payloads through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently. Calldata is built word
by word, so arrays carry dirty narrow elements (addresses with high bits, bools
above one, `uint8` above 255) that solc rejects at the emit, alongside clean,
empty, length-mismatched and malformed payloads. Exact logs (topics and data
bytes), return data, storage and status are compared. A divergence is shrunk to
a deletion-minimal sequence. Equivalent variants must produce identical
observations.
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
from .dynamic_address_event_programs import stateful_dynamic_address_event_source
from .stateful import replay_three_routes, shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/DynamicAddressEventSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/DynamicAddressEventSequenceModel.lean')
CONTRACT = 'DynamicAddressEventSequence'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SIGNATURES = ['batch(address[],uint256[],address)', 'batchThenCheck(address[],uint256[],address)',
              'flags(uint256,bool[],uint64,bytes32[])', 'narrow(uint8[],int256[])', 'count()']
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "DynamicAddressEventSequence.sol"'
WORD = (1 << 256) - 1


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def words(rng, bound, length, dirty):
    """`length` elements below `bound`; with `dirty`, one element is out of range."""
    values = [rng.choice([0, 1, bound - 1, rng.randrange(bound)]) for _ in range(length)]
    if dirty and length:
        values[rng.randrange(length)] = rng.choice([bound, WORD, bound + rng.randrange(bound)])
    return values


def transactions_for(count, seed, caller):
    rng = random.Random(seed)
    calls = []

    def add(signature, payload):
        index = len(calls)
        calls.append({'id': str(index), 'function': signature[:signature.index('(')],
                      'args': [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)],
                      'sender': SENDER, 'target': caller,
                      'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})

    batch, batch_then_check, flags, narrow, total = SIGNATURES
    # Addresses are encoded as raw words so dirty high bits reach the emit.
    def pair(signature, accounts, amounts, target):
        add(signature, encode(['uint256[]', 'uint256[]', 'uint256'], [accounts, amounts, target]))

    def flag(tag, values, note, keys):
        add(flags, encode(['uint256', 'uint256[]', 'uint256', 'bytes32[]'], [tag, values, note, keys]))

    def small(values, signed=()):
        add(narrow, encode(['uint256[]', 'uint256[]'], [values, list(signed)]))

    sender = int(SENDER, 16)
    # Deterministic prefix: empty, clean, dirty first/last, mismatched lengths,
    # rollback after the emit, every validated kind clean and dirty, and
    # truncated/out-of-range array payloads rejected by entry decoding.
    add(total, b'')
    pair(batch, [], [], 0)
    pair(batch, [sender, 1 << 159], [0, WORD], sender)
    pair(batch, [1 << 160, 1], [5, 6], sender)
    pair(batch, [1, (1 << 160) | 7], [5, 6], sender)
    pair(batch, [1, 2], [5], sender)
    pair(batch_then_check, [sender], [WORD], 0)
    pair(batch_then_check, [sender, 3], [1, 2], sender)
    pair(batch_then_check, [WORD], [1], sender)
    flag(0, [], 0, [])
    flag(WORD, [0, 1, 1], (1 << 64) - 1, [b'\xff' * 32, bytes(32)])
    flag(1, [1, 2], 3, [bytes(32)])
    small([0, 255, 17], [WORD, 1 << 255, 0])
    small([255, 256])
    add(narrow, encode(['uint256[]', 'uint256[]'], [[1, 2, 3], [4]])[:-32])
    add(narrow, (64).to_bytes(32, 'big') + (96).to_bytes(32, 'big') + (1 << 64).to_bytes(32, 'big'))
    add(total, b'')
    while len(calls) < count:
        choice = rng.randrange(6)
        dirty = rng.randrange(4) == 0
        length = rng.randrange(4)
        if choice in (0, 1):
            amounts = words(rng, 1 << 256, length if rng.randrange(6) else length + 1, False)
            pair(batch if choice == 0 else batch_then_check, words(rng, 1 << 160, length, dirty),
                 amounts, rng.choice([0, sender, rng.getrandbits(160)]))
        elif choice == 2:
            flag(rng.getrandbits(256), words(rng, 2, length, dirty), rng.getrandbits(64),
                 [rng.getrandbits(256).to_bytes(32, 'big') for _ in range(rng.randrange(3))])
        elif choice == 3:
            small(words(rng, 256, length, dirty), words(rng, 1 << 256, rng.randrange(3), False))
        else:
            add(total, b'')
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported dynamic-event sequence source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol'][CONTRACT]
    identifiers = compiled['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in SIGNATURES])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    caller = address(0)
    calls = transactions_for(transactions, seed, caller)
    write_json(directory / 'transactions.json', calls)
    adapters = {
        'source': EVM(directory / 'A', ['0x' + compiled['evm']['bytecode']['object']]),
        'model': Denote(directory / 'B', driver, caller, timeout=600),
        'compiled': EVM(directory / 'C', ['0x' + next(iter(generated.values()))['evm']['bytecode']['object']])}
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
    if not any(row['events'] for row in rows):
        raise HarnessError('campaign emitted no event')
    write_json(directory / 'campaign.json', report)
    return 0, report


def canonical(observations):
    result = {}
    for route, rows in observations.items():
        result[route] = []
        for row in rows:
            touched, storage = validate_observation(row)
            result[route].append({**row, 'touched': [list(k) for k in sorted(touched)],
                                  'storage': [[*k, storage[k]] for k in sorted(storage)]})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=48)
    parser.add_argument('--seed', type=int, default=2549)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < 17:
        parser.error('at least 17 transactions cover the deterministic prefix')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='dynamic-address-event-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_dynamic_address_event_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'dynamic-event divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'dynamic-event variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported dynamic T[] calldata event payloads: source EVM / Denote / compiled model'})
    print(f'dynamic-event variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
