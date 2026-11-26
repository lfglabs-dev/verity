"""Re-entrant callbacks through source EVM, Denote and compiled model.

Covers both the trailing-call fixture (`ReentrantCallbackSequence.sol`: `ReentrantCallbackFixture`)
and the post-CALL state-access fixtures (`PostCallStateAccess.sol`: `SyntheticPostCallWrite`,
`SyntheticCallbackTransfer`, `SyntheticPostCallEvent`).

Each hook (`ReentrantCallbackHook.sol` on the EVM side, `reentrant-callback-v1` in Denote)
answers a value-free `CALL` either inertly (`NO_CALLBACK`), as a read-only view oracle
(`PURE_WORD`), or by calling its caller back once with a 0..3-word payload. Re-entrant
callbacks in the post-CALL contracts execute real post-call storage reads, storage writes,
checked arithmetic panics, and logs on all three routes (source EVM A, Denote B, compiled C):
- `SyntheticPostCallWrite`: `pingThenCount(hook, 5)` calling back `pingThenCount(inert, 7)`
  leaves `(counter=2, total=12)` on A, B and C; `pingThenView` exercises a post-call `STATICCALL`
  to a `PURE_WORD` view responder after a re-entrant `CALL`.
- `SyntheticCallbackTransfer`: same-credit re-spend panics with `Panic(0x11)` on A, B and C;
  double-spend with 20 credit leaves `(credit=0, transfers=2)` on A, B and C.
- `SyntheticPostCallEvent`: `notify(hook, 3)` calling back `notify(inert, 4)` leaves
  `(count=2, failures=0)` with the callback's log preceding the caller's on A, B and C.

Negative control: each contract replays its witness prefix with every callback hook configured as
an account that answers without calling back on the model route only, and asserts that the model
diverges from source EVM and compiled code. That shows the agreeing campaign really re-enters
the model on all three routes.
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

FIXTURE = Path('Contracts/SolidityImportSmoke/ReentrantCallbackSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/ReentrantCallbackSequenceModel.lean')
POST_CALL_FIXTURE = Path('Contracts/SolidityImportSmoke/PostCallStateAccess.sol')
HOOK = Path('Contracts/SolidityImportSmoke/ReentrantCallbackHook.sol')
CONTRACT = 'ReentrantCallbackFixture'
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ReentrantCallbackSequence.sol"'
POST_CALL_ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "PostCallStateAccess.sol"'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
RECEIVER = '0x' + '00' * 19 + '99'
EMPTY = '0x' + '00' * 19 + '77'
REVERT_AFTER = 1
NO_CALLBACK = 2
PURE_WORD = 4
# `Panic(0x11)`: checked arithmetic overflow or underflow.
PANIC_OVERFLOW = '0x4e487b71' + (0x11).to_bytes(32, 'big').hex()
# The trailing fixture's `callbacks` slot: the re-entry witness the negative control must lose.
CALLBACKS_SLOT = 1
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}


def selector(signature):
    return int.from_bytes(keccak(text=signature)[:4], 'big')


ENTER, ENTER_SMALL, ENTER_FAIL = selector('enter()'), selector('enterSmall(uint8)'), selector('enterThenFail()')
PING_THEN_COUNT = selector('pingThenCount(address,uint256)')
PING_THEN_READ = selector('pingThenRead(address)')
TRANSFER_OUT = selector('transferOut(address,address,uint256)')
NOTIFY = selector('notify(address,uint256)')
TRY_NOTIFY = selector('tryNotify(address,uint256)')
UNKNOWN = 0x12345678

# One configuration per hook: (callback selector, argument count, arg0, arg1, arg2, flags).
HOOKS = [
    (ENTER, 0, 0, 0, 0, 0),                # commits: own sender and selector, sees the pre-call write
    (ENTER_SMALL, 1, 7, 0, 0, 0),          # commits a decoded argument
    (ENTER_SMALL, 1, 256, 0, 0, 0),        # the callback's decoder reverts with no data
    (ENTER_FAIL, 0, 0, 0, 0, 0),           # the callback writes, then reverts with data
    (UNKNOWN, 0, 0, 0, 0, 0),              # no function: the dispatcher reverts with no data
    (ENTER, 0, 0, 0, 0, REVERT_AFTER),     # the callback commits, then the hook reverts
]


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def make_call(calls, caller, first_block, function, types, values):
    index = len(calls)
    encoded = encode(types, values)
    words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
    calls.append({'id': str(index), 'function': function[:function.index('(')], 'args': words,
                  'sender': SENDER, 'target': caller,
                  'data': '0x' + keccak(text=function)[:4].hex() + encoded.hex(),
                  'value': '0x0', 'timestamp': 1000000100 + index,
                  'blockNumber': first_block + index})


def transactions_for(count, seed, caller, hooks):
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []
    first_block = len(hooks) + 2

    def add(function, types, values):
        make_call(calls, caller, first_block, function, types, values)

    # Every target through every call shape, the callbacks called directly, then random calls.
    # The first call is `poke` of the first hook, which commits its callback.
    for index, target in enumerate(targets):
        add('poke(address,uint256)', ['address', 'uint256'], [target, 100 + index])
        add('tryPoke(address,uint256)', ['address', 'uint256'], [target, 200 + index])
        add('emitPoke(address,uint256)', ['address', 'uint256'], [target, 300 + index])
    add('enter()', [], [])
    add('enterSmall(uint8)', ['uint8'], [9])
    add('enterThenFail()', [], [])
    while len(calls) < count:
        choice = rng.randrange(7)
        target = rng.choice(targets)
        value = rng.choice([0, 1, rng.getrandbits(8), rng.getrandbits(128)])
        if choice < 2:
            add('poke(address,uint256)', ['address', 'uint256'], [target, value])
        elif choice < 4:
            add('tryPoke(address,uint256)', ['address', 'uint256'], [target, value])
        elif choice == 4:
            add('emitPoke(address,uint256)', ['address', 'uint256'], [target, value])
        elif choice == 5:
            add('enter()', [], [])
        else:
            add('enterSmall(uint8)', ['uint8'], [value % 256])
    return calls


def hook_storage(account, hook):
    """The hook constructor's writes: selector, argument count, arg0..arg2 and flags."""
    return [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
            for slot, value in enumerate(hook) if value]


def slot_word(row, account, slot):
    """Storage word at `(account, slot)` after one transaction, as a route observed it."""
    for owner, key, value in row['storage']:
        if owner.lower() == account.lower() and int(key, 16) == slot:
            return int(value, 16)
    return None


def callback_witness(row, caller):
    """The trailing fixture's callback count after one transaction, as a route observed it."""
    return slot_word(row, caller, CALLBACKS_SLOT)


def post_call_write_hooks(accounts):
    inert = int(accounts[0], 16)
    # 0: inert callee; 1: failing inert; 2: read-only view oracle returning 42;
    # 3: re-entrant pingThenCount(inert, 7); 4: re-entrant pingThenCount(inert, 7) + revert;
    # 5: re-entrant pingThenRead(inert).
    return [
        (0, 0, 0, 0, 0, NO_CALLBACK),
        (0, 0, 0, 0, 0, NO_CALLBACK | REVERT_AFTER),
        (0, 0, 42, 0, 0, PURE_WORD),
        (PING_THEN_COUNT, 2, inert, 7, 0, 0),
        (PING_THEN_COUNT, 2, inert, 7, 0, REVERT_AFTER),
        (PING_THEN_READ, 1, inert, 0, 0, 0),
    ]


def post_call_write_txs(count, seed, caller, hooks):
    inert, failing, view_oracle, reenter_count, reenter_revert, reenter_read = hooks
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []
    first_block = len(hooks) + 2

    def add(function, types, values):
        make_call(calls, caller, first_block, function, types, values)

    # Tx 0: pinned witness: `pingThenCount(reenter_count, 5)` -> callback adds (1, 7), outer adds
    # (1, 5), leaving `(counter=2, total=12)` on all three routes A, B and C.
    add('pingThenCount(address,uint256)', ['address', 'uint256'], [reenter_count, 5])
    add('pingThenRead(address)', ['address'], [reenter_count])
    add('pingThenView(address,address)', ['address', 'address'], [reenter_count, view_oracle])
    add('twoPingsThenCount(address,address,uint256)', ['address', 'address', 'uint256'],
        [reenter_count, inert, 3])
    add('pingThenRequire(address,uint256)', ['address', 'uint256'], [reenter_count, 7])
    add('pingThenRequire(address,uint256)', ['address', 'uint256'], [reenter_count, 0])
    add('pingLoop(address,uint256)', ['address', 'uint256'], [reenter_count, 4])
    add('pingThenBalance(address)', ['address'], [reenter_count])
    for index, target in enumerate(targets):
        add('pingThenCount(address,uint256)', ['address', 'uint256'], [target, 1 + index])
        add('pingThenRead(address)', ['address'], [target])
        add('pingThenView(address,address)', ['address', 'address'], [target, view_oracle])
    add('pingThenCount(address,uint256)', ['address', 'uint256'], [failing, 1])
    add('pingThenCount(address,uint256)', ['address', 'uint256'], [reenter_revert, 1])
    add('pingThenCount(address,uint256)', ['address', 'uint256'], [reenter_read, 1])
    add('read()', [], [])
    while len(calls) < count:
        choice = rng.randrange(7)
        target = rng.choice(targets)
        amount = rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(64)])
        if choice == 0:
            add('pingThenCount(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 1:
            add('pingThenRead(address)', ['address'], [target])
        elif choice == 2:
            add('twoPingsThenCount(address,address,uint256)', ['address', 'address', 'uint256'],
                [target, rng.choice(targets), amount])
        elif choice == 3:
            add('pingLoop(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 4:
            add('pingThenBalance(address)', ['address'], [target])
        elif choice == 5:
            add('pingThenView(address,address)', ['address', 'address'], [target, view_oracle])
        else:
            add('read()', [], [])
    return calls


def post_call_write_check(caller, hooks, observations, negative_observations):
    del hooks
    for route, rows in observations.items():
        if rows[0]['status'] != 'ok' or slot_word(rows[0], caller, 0) != 2 or slot_word(rows[0], caller, 1) != 12:
            raise HarnessError(f'{route}: pingThenCount re-entry witness did not leave (2, 12)')
    if (slot_word(negative_observations['source'][0], caller, 0) != 2
            or slot_word(negative_observations['model'][0], caller, 0) != 1):
        raise HarnessError('negative control: pingThenCount without callback went undetected')


def callback_transfer_hooks(accounts):
    inert = int(accounts[0], 16)
    receiver = int(RECEIVER, 16)
    # 0: inert token; 1: failing inert token;
    # 2: re-entrant token calling back `transferOut(inert, RECEIVER, 10)`;
    # 3: re-entrant token calling back `transferOut(inert, RECEIVER, 10)` then reverting.
    return [
        (0, 0, 0, 0, 0, NO_CALLBACK),
        (0, 0, 0, 0, 0, NO_CALLBACK | REVERT_AFTER),
        (TRANSFER_OUT, 3, inert, receiver, 10, 0),
        (TRANSFER_OUT, 3, inert, receiver, 10, REVERT_AFTER),
    ]


def callback_transfer_txs(count, seed, caller, hooks):
    inert, failing, reenter_spend, reenter_revert = hooks
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []
    first_block = len(hooks) + 2

    def add(function, types, values):
        make_call(calls, caller, first_block, function, types, values)

    # Tx 0..1: pinned witness 1: deposit 10, then re-entrant spend of the same 10 panics (0x11)
    # on A, B and C (rolls back to credit=10, transfers=0).
    add('deposit(address,uint256)', ['address', 'uint256'], [RECEIVER, 10])
    add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
        [reenter_spend, RECEIVER, 10])
    # Tx 2..3: pinned witness 2: deposit 10 more (total 20), then re-entrant double spend
    # succeeds leaving `(credit=0, transfers=2)` on A, B and C.
    add('deposit(address,uint256)', ['address', 'uint256'], [RECEIVER, 10])
    add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
        [reenter_spend, RECEIVER, 10])
    add('read(address)', ['address'], [RECEIVER])
    # Exercise every target (including failing and revert-after hooks).
    add('deposit(address,uint256)', ['address', 'uint256'], [RECEIVER, 100])
    for index, target in enumerate(targets):
        add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
            [target, RECEIVER, 1 + index])
    add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
        [failing, RECEIVER, 1])
    add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
        [reenter_revert, RECEIVER, 10])
    add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
        [inert, RECEIVER, 1])
    while len(calls) < count:
        choice = rng.randrange(4)
        holder = rng.choice([RECEIVER, SENDER])
        if choice == 0:
            add('deposit(address,uint256)', ['address', 'uint256'], [holder, rng.choice([0, 5, 10, 25])])
        elif choice in (1, 2):
            add('transferOut(address,address,uint256)', ['address', 'address', 'uint256'],
                [rng.choice(targets), holder, rng.choice([0, 1, 10, 15])])
        else:
            add('read(address)', ['address'], [holder])
    return calls


def callback_transfer_check(caller, hooks, observations, negative_observations):
    del hooks
    for route, rows in observations.items():
        if rows[1]['status'] != 'revert' or rows[1]['data'] != PANIC_OVERFLOW:
            raise HarnessError(f'{route}: same-credit re-spend did not panic with Panic(0x11)')
        if rows[3]['status'] != 'ok' or slot_word(rows[3], caller, 1) != 2:
            raise HarnessError(f'{route}: double-spend with 20 credit did not leave transfers=2')
        if rows[4]['status'] != 'ok' or rows[4]['data'] != '0x' + encode(['uint256', 'uint256'], [0, 2]).hex():
            raise HarnessError(f'{route}: read(RECEIVER) after double-spend did not return (0, 2)')
    if (negative_observations['source'][1]['status'] != 'revert'
            or negative_observations['model'][1]['status'] != 'ok'):
        raise HarnessError('negative control: same-credit re-spend without callback went undetected')


def post_call_event_hooks(accounts):
    inert = int(accounts[0], 16)
    # 0: inert callee; 1: failing inert callee;
    # 2: re-entrant notify(inert, 4); 3: re-entrant notify(inert, 4) then revert;
    # 4: re-entrant tryNotify(inert, 4).
    return [
        (0, 0, 0, 0, 0, NO_CALLBACK),
        (0, 0, 0, 0, 0, NO_CALLBACK | REVERT_AFTER),
        (NOTIFY, 2, inert, 4, 0, 0),
        (NOTIFY, 2, inert, 4, 0, REVERT_AFTER),
        (TRY_NOTIFY, 2, inert, 4, 0, 0),
    ]


def post_call_event_txs(count, seed, caller, hooks):
    inert, failing, reenter_notify, reenter_revert, reenter_try = hooks
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []
    first_block = len(hooks) + 2

    def add(function, types, values):
        make_call(calls, caller, first_block, function, types, values)

    # Tx 0: pinned witness: `notify(reenter_notify, 3)` -> callback emits `(inert, 4, 1)` BEFORE
    # caller emits `(reenter_notify, 3, 2)`, leaving `(count=2, failures=0)` on A, B and C.
    add('notify(address,uint256)', ['address', 'uint256'], [reenter_notify, 3])
    for index, target in enumerate(targets):
        add('notify(address,uint256)', ['address', 'uint256'], [target, 5 + index])
        add('tryNotify(address,uint256)', ['address', 'uint256'], [target, 9 + index])
        add('tryNotifyRead(address,uint256)', ['address', 'uint256'], [target, 11 + index])
    add('notify(address,uint256)', ['address', 'uint256'], [failing, 1])
    add('notify(address,uint256)', ['address', 'uint256'], [reenter_revert, 1])
    add('tryNotify(address,uint256)', ['address', 'uint256'], [reenter_try, 1])
    add('read()', [], [])
    while len(calls) < count:
        choice = rng.randrange(4)
        target = rng.choice(targets)
        amount = rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(64)])
        if choice == 0:
            add('notify(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 1:
            add('tryNotify(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 2:
            add('tryNotifyRead(address,uint256)', ['address', 'uint256'], [target, amount])
        else:
            add('read()', [], [])
    return calls


def post_call_event_check(caller, hooks, observations, negative_observations):
    inert, _, reenter_notify, _, _ = hooks
    expected_first = '0x' + encode(['uint256', 'uint256'], [4, 1]).hex()
    expected_second = '0x' + encode(['uint256', 'uint256'], [3, 2]).hex()
    topic_inert = '0x' + int(inert, 16).to_bytes(32, 'big').hex()
    topic_hook = '0x' + int(reenter_notify, 16).to_bytes(32, 'big').hex()
    for route, rows in observations.items():
        events = rows[0]['events']
        if (rows[0]['status'] != 'ok' or slot_word(rows[0], caller, 0) != 2 or len(events) != 2
                or events[0]['topics'][1] != topic_inert or events[0]['data'] != expected_first
                or events[1]['topics'][1] != topic_hook or events[1]['data'] != expected_second):
            raise HarnessError(f'{route}: notify re-entry did not order callback log before caller log')
    if (len(negative_observations['source'][0]['events']) != 2
            or len(negative_observations['model'][0]['events']) != 1):
        raise HarnessError('negative control: notify without callback went undetected')


def trailing_check(caller, hooks, observations, negative_observations):
    del hooks
    for route, observed in observations.items():
        if callback_witness(observed[0], caller) != 1:
            raise HarnessError(f'{route}: the first committing callback was not observed')
    if (callback_witness(negative_observations['source'][0], caller) != 1
            or callback_witness(negative_observations['model'][0], caller) != 0):
        raise HarnessError('negative control: a model route without callbacks went undetected')


SPECS = {
    'ReentrantCallbackFixture': {
        'fixture': FIXTURE,
        'driver': DRIVER,
        'anchor': ANCHOR,
        'hooks': lambda accounts: HOOKS,
        'hook_count': len(HOOKS),
        'plan': transactions_for,
        'negative_prefix': 1,
        'check': trailing_check,
    },
    'SyntheticPostCallWrite': {
        'fixture': POST_CALL_FIXTURE,
        'driver': Path('Contracts/SolidityImportSmoke/PostCallWriteSequenceModel.lean'),
        'anchor': POST_CALL_ANCHOR,
        'hooks': post_call_write_hooks,
        'hook_count': 6,
        'plan': post_call_write_txs,
        'negative_prefix': 1,
        'check': post_call_write_check,
    },
    'SyntheticCallbackTransfer': {
        'fixture': POST_CALL_FIXTURE,
        'driver': Path('Contracts/SolidityImportSmoke/CallbackTransferSequenceModel.lean'),
        'anchor': POST_CALL_ANCHOR,
        'hooks': callback_transfer_hooks,
        'hook_count': 4,
        'plan': callback_transfer_txs,
        'negative_prefix': 2,
        'check': callback_transfer_check,
    },
    'SyntheticPostCallEvent': {
        'fixture': POST_CALL_FIXTURE,
        'driver': Path('Contracts/SolidityImportSmoke/PostCallEventSequenceModel.lean'),
        'anchor': POST_CALL_ANCHOR,
        'hooks': post_call_event_hooks,
        'hook_count': 5,
        'plan': post_call_event_txs,
        'negative_prefix': 1,
        'check': post_call_event_check,
    },
}


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC, *,
             contract=CONTRACT, anchor=ANCHOR, hook_configs=None, plan=transactions_for,
             negative_prefix=1, check=trailing_check):
    """Run one imported variant and its negative control; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(anchor) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source},
                    HOOK.name: {'content': (root / HOOK).read_text()}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][contract]
    identifiers = caller_contract['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in roots(template)])
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
    mock = compiled[HOOK.name]['ReentrantCallbackHook']['evm']
    runtime = '0x' + mock['deployedBytecode']['object']
    caller = address(0)
    if hook_configs is None:
        hook_configs = HOOKS
    if callable(hook_configs):
        count_hooks = SPECS[contract]['hook_count']
        accounts = [address(i + 1) for i in range(count_hooks)]
        configs = hook_configs(accounts)
    else:
        configs = hook_configs
        accounts = [address(i + 1) for i in range(len(configs))]
    hooks = ['0x' + mock['bytecode']['object'] + encode(['uint256'] * 6, list(hook)).hex()
             for hook in configs]
    initial = [row for account, hook in zip(accounts, configs, strict=True)
               for row in hook_storage(account, hook)]
    calls = plan(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    empty = [str(int(EMPTY, 16)), str(int(SENDER, 16))]

    def adapters(name, environment):
        return {
            'source': EVM(directory / name / 'A', [caller_a, *hooks], initial),
            'model': Denote(directory / name / 'B', driver, caller, initial,
                            byte_call_environment=environment,
                            account_code=[(account, runtime) for account in accounts]),
            'compiled': EVM(directory / name / 'C', [caller_c, *hooks], initial)}

    environment = {'program': 'reentrant-callback-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': empty, 'gas': '1000000'}
    routes = adapters('campaign', environment)
    result = replay_three_routes(calls, routes)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed, 'contract': contract,
              'hooks': [[str(v) for v in hook] for hook in configs], 'empty': EMPTY,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, routes)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    rows = result['observations']['source']
    if {row['status'] for row in rows} != {'ok', 'revert'}:
        raise HarnessError(f'{contract}: campaign must exercise both successful and reverting calls')
    # Negative control: the hooks answer without calling back on the model route only.
    skipped = {'program': 'reentrant-callback-v1', 'accounts': [],
               'emptyAccounts': [str(int(a, 16)) for a in accounts] + empty, 'gas': '1000000'}
    control = replay_three_routes(calls[:negative_prefix], adapters('negative-control', skipped))
    if not control['divergences']:
        raise HarnessError(f'{contract}: negative control without callbacks went undetected')
    check(caller, accounts, result['observations'], control['observations'])
    report['negativeControl'] = {'transactions': negative_prefix,
                                 'divergences': len(control['divergences'])}
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2911)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--only', choices=sorted(SPECS))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 3 * (len(HOOKS) + 2) + 3
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='reentrant-callback-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    passed = []
    for name, spec in SPECS.items():
        if args.only and args.only != name:
            continue
        target_dir = output if args.only else output / name
        code, _ = campaign(target_dir, spec['fixture'].read_text(), spec['driver'].read_text(),
                           args.transactions, args.seed, args.shrink_attempts,
                           contract=name, anchor=spec['anchor'], hook_configs=spec['hooks'],
                           plan=spec['plan'], negative_prefix=spec['negative_prefix'],
                           check=spec['check'])
        if code:
            raise SystemExit(f'reentrant callback divergence ({name}): {target_dir}')
        passed.append(name)
    write_json(output / 'summary.json', {'passed': True, 'contracts': passed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'value-free CALLs whose callee re-enters the caller once (trailing and '
                 'post-CALL state access): source EVM / Denote / compiled model, plus '
                 'no-callback negative controls'})
    print(f'reentrant callback A/B/C agree ({", ".join(passed)}): {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
