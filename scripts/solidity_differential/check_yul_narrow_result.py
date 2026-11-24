"""Imported Yul writes and reads of narrow named results through source EVM, Denote and compiled model.

Two A/B/C campaigns over library helpers whose named `bool` (and `uint32`) results are written
in inline assembly and read back in Yul. The importer keeps the raw word a Yul write leaves on
the stack, as solc does (legacy and via-IR): Yul reads see it, Solidity consumers clean it.

- `YulNarrowResultCallSequence.sol`: the result of a value-free `call` with a
  transfer/transferFrom/approve shape, against the recording call responders (return words `1`,
  `0`, `2`, empty, short and long answers, reverts with and without data), one account without
  code and the sender EOA, plus a `tryMul` / saturating product over the same transactions.
- `YulNarrowResultStaticSequence.sol`: a `bool` and a `uint32` result written from the two
  scratch words a `staticcall` answers into, against raw static oracles whose first word is
  `0`, `1`, `2`, `0x100` or all ones, whose answer is complete, short (one byte, 31 and 32
  bytes) or empty, or which revert; one account without code and the sender EOA.

A divergence is shrunk to a deletion-minimal sequence.
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

CALL_FIXTURE = Path('Contracts/SolidityImportSmoke/YulNarrowResultCallSequence.sol')
CALL_DRIVER = Path('Contracts/SolidityImportSmoke/YulNarrowResultCallSequenceModel.lean')
CALL_CONTRACT = 'YulNarrowResultCallFixture'
CALL_ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "YulNarrowResultCallSequence.sol"'
STATIC_FIXTURE = Path('Contracts/SolidityImportSmoke/YulNarrowResultStaticSequence.sol')
STATIC_DRIVER = Path('Contracts/SolidityImportSmoke/YulNarrowResultStaticSequenceModel.lean')
STATIC_CONTRACT = 'YulNarrowResultStaticFixture'
STATIC_ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "YulNarrowResultStaticSequence.sol"'
ORACLE = Path('test/ByteExternalCall/RawStaticOracle.sol')
# (first return word, failed, response length) of `raw-static-oracle-v1`. A successful answer
# shorter than 64 bytes leaves the rest of the zeroed scratch words in place.
ORACLES = [
    (0, False, 64),
    (1, False, 64),
    (2, False, 64),
    (0x100, False, 64),
    (2**256 - 1, False, 64),
    (1, False, 32),
    (2, False, 31),
    (1, False, 1),
    # One byte of a word whose top byte is 0x80: a dirty, nonzero first scratch word.
    (2**255 + 2, False, 1),
    (1, False, 0),
    (1, True, 64),
    (0, True, 0),
]
RECEIVER = '0x' + '00' * 19 + '99'
WORDS = [0, 1, 2, 3, 2**128, 2**255, 2**256 - 1]


class Plan:
    """Transactions in the shape `check_yul_memory_call.campaign` replays."""

    def __init__(self, seed, caller):
        self.rng = random.Random(seed)
        self.caller = caller
        self.calls = []

    def add(self, function, types, values):
        index = len(self.calls)
        selector = keccak(text=function)[:4].hex()
        encoded = encode(types, values)
        # The model's argument words are the calldata words after the selector.
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        self.calls.append({'id': str(index), 'function': function[:function.index('(')],
                           'args': words, 'sender': SENDER, 'target': self.caller,
                           'data': '0x' + selector + encoded.hex(), 'value': '0x0',
                           'timestamp': 1000000100 + index, 'blockNumber': 64 + index})

    def amount(self):
        return self.rng.choice([0, 1, 7, self.rng.getrandbits(8), self.rng.getrandbits(256)])


def call_transactions(count, seed, caller, responders):
    tokens = [*responders, EMPTY, SENDER]
    plan = Plan(seed, caller)
    token3 = ['address', 'address', 'uint256']
    # Every token through every call shape, then random calls.
    for index, token in enumerate(tokens):
        plan.add('push(address,address,uint256)', token3, [token, RECEIVER, 100 + index])
        plan.add('tryPush(address,address,uint256)', token3, [token, RECEIVER, 200 + index])
        plan.add('pull(address,address,address,uint256)', ['address', 'address', 'address', 'uint256'],
                 [token, SENDER, RECEIVER, 1 + index])
        plan.add('allow(address,address,uint256)', token3, [token, RECEIVER, 300 + index])
    for a in WORDS:
        for b in WORDS:
            plan.add('scaled(uint256,uint256)', ['uint256', 'uint256'], [a, b])
    plan.add('read()', [], [])
    while len(plan.calls) < count:
        choice = plan.rng.randrange(6)
        token = plan.rng.choice(tokens)
        if choice == 0:
            plan.add('push(address,address,uint256)', token3, [token, RECEIVER, plan.amount()])
        elif choice == 1:
            plan.add('tryPush(address,address,uint256)', token3, [token, SENDER, plan.amount()])
        elif choice == 2:
            plan.add('pull(address,address,address,uint256)', ['address', 'address', 'address', 'uint256'],
                     [token, plan.rng.choice([RECEIVER, SENDER]), RECEIVER, plan.amount()])
        elif choice == 3:
            plan.add('allow(address,address,uint256)', token3, [token, RECEIVER, plan.amount()])
        elif choice == 4:
            plan.add('scaled(uint256,uint256)', ['uint256', 'uint256'],
                     [plan.rng.choice(WORDS + [plan.amount()]), plan.rng.choice(WORDS + [plan.amount()])])
        else:
            plan.add('read()', [], [])
    return plan.calls


def static_transactions(count, seed, caller, oracles):
    accounts = [*oracles, EMPTY, SENDER]
    plan = Plan(seed, caller)
    selector = bytes.fromhex('0badf00d')
    for index, account in enumerate(accounts):
        plan.add('peek(address,bytes4)', ['address', 'bytes4'], [account, selector])
        plan.add('peekRaw(address,bytes4)', ['address', 'bytes4'], [account, selector])
        plan.add('guarded(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
                 [account, selector, 1000 + index])
        plan.add('read()', [], [])
    while len(plan.calls) < count:
        choice = plan.rng.randrange(4)
        account = plan.rng.choice(accounts)
        word = plan.rng.getrandbits(32).to_bytes(4, 'big')
        if choice == 0:
            plan.add('peek(address,bytes4)', ['address', 'bytes4'], [account, word])
        elif choice == 1:
            plan.add('peekRaw(address,bytes4)', ['address', 'bytes4'], [account, word])
        elif choice == 2:
            plan.add('guarded(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
                     [account, word, plan.amount()])
        else:
            plan.add('read()', [], [])
    return plan.calls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=120)
    parser.add_argument('--seed', type=int, default=2912)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = max(4 * (len(RESPONDERS) + 2) + len(WORDS) ** 2 + 1, 4 * (len(ORACLES) + 2))
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every account and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='yul-narrow-result-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output / 'call', CALL_FIXTURE.read_text(), CALL_DRIVER.read_text(),
                       args.transactions, args.seed, args.shrink_attempts, contract=CALL_CONTRACT,
                       anchor=CALL_ANCHOR, plan=call_transactions)
    if code:
        raise SystemExit(f'Yul narrow result call divergence: {output / "call"}')
    code, _ = campaign(output / 'static', STATIC_FIXTURE.read_text(), STATIC_DRIVER.read_text(),
                       args.transactions, args.seed, args.shrink_attempts, contract=STATIC_CONTRACT,
                       anchor=STATIC_ANCHOR, plan=static_transactions, responder=ORACLE,
                       responder_contract='RawStaticOracle', parameters=ORACLES,
                       program='raw-static-oracle-v1')
    if code:
        raise SystemExit(f'Yul narrow result staticcall divergence: {output / "static"}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported Yul writes and reads of narrow named results: '
                                    'source EVM / Denote / compiled model'})
    print(f'Yul narrow result A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
