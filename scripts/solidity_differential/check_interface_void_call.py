"""Imported typed external calls without return values through source EVM, Denote and compiled model.

The fixture calls `nonpayable` and `payable` interface functions that return nothing,
as whole expression statements, with scalar, `msg.data`, calldata-bytes and empty
argument lists. solc reverts with no data when the target has no code, forwards a
failed call's complete return data and ignores a successful call's return data,
whatever its length or contents. The A/B/C sequence reuses the Yul memory call
campaign: the recording responders (every response shape, success and failure,
calldata size and first four words recorded in storage), one account without code
and the sender EOA. A divergence is shrunk to a deletion-minimal sequence.
"""
import argparse
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak

from .check_yul_memory_call import EMPTY, RESPONDERS, SENDER, campaign
from .engine import write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/InterfaceVoidCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/InterfaceVoidCallSequenceModel.lean')
CONTRACT = 'InterfaceVoidCallFixture'
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "InterfaceVoidCallSequence.sol"'


def transactions_for(count, seed, caller, responders):
    targets = [*responders, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []

    def add(function, types, values):
        index = len(calls)
        selector = keccak(text=function)[:4].hex()
        name = function[:function.index('(')]
        encoded = encode(types, values)
        # The model's argument words are the calldata words after the selector, tails included.
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                      'target': caller, 'data': '0x' + selector + encoded.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(responders) + 2 + index})

    def payload():
        return rng.choice([b'', b'\x01', bytes(31), bytes(range(32)), bytes(range(33)),
                           rng.randbytes(rng.randrange(1, 100))])

    # Every target through every call shape, then random calls.
    for index, target in enumerate(targets):
        add('ping(address,uint256)', ['address', 'uint256'], [target, 7 + index])
        add('relay(address)', ['address'], [target])
        add('relayData(address,bytes)', ['address', 'bytes'], [target, bytes(range(index + 30))])
        add('poke(address)', ['address'], [target])
        add('fund(address,uint128)', ['address', 'uint128'], [target, 2 ** 128 - 1 - index])
    add('read()', [], [])
    while len(calls) < count:
        choice = rng.randrange(6)
        target = rng.choice(targets)
        amount = rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(256)])
        if choice == 0:
            add('ping(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 1:
            add('relay(address)', ['address'], [target])
        elif choice == 2:
            add('relayData(address,bytes)', ['address', 'bytes'], [target, payload()])
        elif choice == 3:
            add('poke(address)', ['address'], [target])
        elif choice == 4:
            add('fund(address,uint128)', ['address', 'uint128'], [target, amount % 2 ** 128])
        else:
            add('read()', [], [])
    return calls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=96)
    parser.add_argument('--seed', type=int, default=4219)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 5 * (len(RESPONDERS) + 2) + 1
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='interface-void-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts, contract=CONTRACT, anchor=ANCHOR, plan=transactions_for)
    if code:
        raise SystemExit(f'interface void call divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported typed external calls without return values: '
                                    'source EVM / Denote / compiled model'})
    print(f'interface void call A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
