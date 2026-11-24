"""Imported storage reads, storage writes and logs after a closed CALL through source EVM, Denote and compiled model.

`PostCallStateAccess.sol` holds three synthetic contracts whose effects follow an
interaction: `SyntheticPostCallWrite` reads and writes storage after a typed void
interface call, `SyntheticCallbackTransfer` subtracts from and adds to storage after an
optional-bool low-level `CALL`, and `SyntheticPostCallEvent` logs after a typed void call
and writes storage in both clauses of a `try`. Each contract runs its own A/B/C sequence
against the recording call responders (every response shape, success and failure; each
writes its own storage on every answered call), one account without code and the sender
EOA. Storage touched on any route, return and revert bytes and logs are compared after
every transaction. A divergence is shrunk to a deletion-minimal sequence.

Re-entrant callees are covered by `PostCallStateAccessChecks.lean`, which runs the same
models in Denote against a callee that calls back into the contract.
"""
import argparse
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak

from .check_yul_memory_call import EMPTY, RECEIVER, RESPONDERS, SENDER, campaign
from .engine import write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/PostCallStateAccess.sol')
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"'
DRIVERS = {
    'SyntheticPostCallWrite': Path('Contracts/SolidityImportSmoke/PostCallWriteSequenceModel.lean'),
    'SyntheticCallbackTransfer':
        Path('Contracts/SolidityImportSmoke/CallbackTransferSequenceModel.lean'),
    'SyntheticPostCallEvent': Path('Contracts/SolidityImportSmoke/PostCallEventSequenceModel.lean'),
}


class Plan:
    """Transactions of one contract, encoded as the shared campaign expects."""

    def __init__(self, caller, responders):
        self.caller = caller
        self.calls = []
        self.targets = [*responders, EMPTY, SENDER]
        # The caller and every responder are deployed in their own blocks first.
        self.first_block = len(responders) + 2

    def add(self, function, types, values):
        index = len(self.calls)
        selector = keccak(text=function)[:4].hex()
        name = function[:function.index('(')]
        encoded = encode(types, values)
        # The model's argument words are the calldata words after the selector.
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        self.calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                           'target': self.caller, 'data': '0x' + selector + encoded.hex(),
                           'value': '0x0', 'timestamp': 1000000100 + index,
                           'blockNumber': self.first_block + index})


def amounts(rng):
    return rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(255), 2 ** 256 - 1])


def post_call_write(count, seed, caller, responders):
    plan, rng = Plan(caller, responders), random.Random(seed)
    for index, target in enumerate(plan.targets):
        plan.add('pingThenCount(address,uint256)', ['address', 'uint256'], [target, 5 + index])
        plan.add('pingThenRead(address)', ['address'], [target])
        plan.add('read()', [], [])
    # `total += amount` overflows after the call: the post-call checked addition panics.
    plan.add('pingThenCount(address,uint256)', ['address', 'uint256'], [plan.targets[0], 2 ** 256 - 1])
    while len(plan.calls) < count:
        target, choice = rng.choice(plan.targets), rng.randrange(3)
        if choice == 0:
            plan.add('pingThenCount(address,uint256)', ['address', 'uint256'], [target, amounts(rng)])
        elif choice == 1:
            plan.add('pingThenRead(address)', ['address'], [target])
        else:
            plan.add('read()', [], [])
    return plan.calls


def callback_transfer(count, seed, caller, responders):
    plan, rng = Plan(caller, responders), random.Random(seed)
    holders = [RECEIVER, SENDER]
    plan.add('deposit(address,uint256)', ['address', 'uint256'], [RECEIVER, 1000])
    for index, token in enumerate(plan.targets):
        plan.add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
                 [token, RECEIVER, 1 + index])
        plan.add('read(address)', ['address'], [RECEIVER])
    # More than the credit: the pre-call check fails before any interaction.
    plan.add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
             [plan.targets[0], SENDER, 1])
    while len(plan.calls) < count:
        choice = rng.randrange(4)
        holder = rng.choice(holders)
        if choice == 0:
            plan.add('deposit(address,uint256)', ['address', 'uint256'], [holder, amounts(rng)])
        elif choice in (1, 2):
            plan.add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
                     [rng.choice(plan.targets), holder, rng.choice([0, 1, 3, 50, rng.getrandbits(12)])])
        else:
            plan.add('read(address)', ['address'], [holder])
    return plan.calls


def post_call_event(count, seed, caller, responders):
    plan, rng = Plan(caller, responders), random.Random(seed)
    for index, target in enumerate(plan.targets):
        plan.add('notify(address,uint256)', ['address', 'uint256'], [target, 3 + index])
        plan.add('tryNotify(address,uint256)', ['address', 'uint256'], [target, 9 + index])
        plan.add('read()', [], [])
    while len(plan.calls) < count:
        target, choice = rng.choice(plan.targets), rng.randrange(3)
        if choice == 0:
            plan.add('notify(address,uint256)', ['address', 'uint256'], [target, amounts(rng)])
        elif choice == 1:
            plan.add('tryNotify(address,uint256)', ['address', 'uint256'], [target, amounts(rng)])
        else:
            plan.add('read()', [], [])
    return plan.calls


PLANS = {
    'SyntheticPostCallWrite': post_call_write,
    'SyntheticCallbackTransfer': callback_transfer,
    'SyntheticPostCallEvent': post_call_event,
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=96)
    parser.add_argument('--seed', type=int, default=6517)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--only', choices=sorted(PLANS))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 3 * (len(RESPONDERS) + 2) + 2
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='post-call-state-access-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    source = FIXTURE.read_text()
    passed = []
    for contract, plan in PLANS.items():
        if args.only and args.only != contract:
            continue
        code, _ = campaign(output / contract, source, DRIVERS[contract].read_text(),
                           args.transactions, args.seed, args.shrink_attempts,
                           contract=contract, anchor=ANCHOR, plan=plan)
        if code:
            raise SystemExit(f'post-call state access divergence ({contract}): {output / contract}')
        passed.append(contract)
    write_json(output / 'summary.json', {'passed': True, 'contracts': passed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported storage reads, writes and logs after a closed CALL: '
                 'source EVM / Denote / compiled model'})
    print(f'post-call state access A/B/C agree ({", ".join(passed)}): {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
