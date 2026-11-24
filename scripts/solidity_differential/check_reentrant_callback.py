"""Re-entrant callbacks through source EVM, Denote and compiled model.

The fixture writes state, then calls a target that may call it back (`poke` bubbles a failed
call, `tryPoke` catches it). Each hook (`ReentrantCallbackHook.sol` on the EVM side,
`reentrant-callback-v1` in Denote) calls the caller back once with its own payload: a callback
that records its own sender and selector and reads the caller's pre-call write, one with a
clean and one with a dirty `uint8` argument, one that writes and then reverts with data, one
whose selector names no function, and a hook that reverts after a successful callback. One
account has no code and the sender is an EOA. A divergence is shrunk to a deletion-minimal
sequence.

Negative control: the same transactions replayed with every hook configured as an account that
answers without calling back must diverge, with the model route missing the callback count.
That shows the agreeing campaign really re-enters the model.
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
HOOK = Path('Contracts/SolidityImportSmoke/ReentrantCallbackHook.sol')
CONTRACT = 'ReentrantCallbackFixture'
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ReentrantCallbackSequence.sol"'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
EMPTY = '0x' + '00' * 19 + '77'
REVERT_AFTER = 1
# The fixture's `callbacks` slot: the re-entry witness the negative control must lose.
CALLBACKS_SLOT = 1
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}


def selector(signature):
    return int.from_bytes(keccak(text=signature)[:4], 'big')


ENTER, ENTER_SMALL, ENTER_FAIL = selector('enter()'), selector('enterSmall(uint8)'), selector('enterThenFail()')
UNKNOWN = 0x12345678

# One configuration per hook: (callback selector, argument count, argument, flags).
HOOKS = [
    (ENTER, 0, 0, 0),                # commits: own sender and selector, sees the pre-call write
    (ENTER_SMALL, 1, 7, 0),          # commits a decoded argument
    (ENTER_SMALL, 1, 256, 0),        # the callback's decoder reverts with no data
    (ENTER_FAIL, 0, 0, 0),           # the callback writes, then reverts with data
    (UNKNOWN, 0, 0, 0),              # no function: the dispatcher reverts with no data
    (ENTER, 0, 0, REVERT_AFTER),     # the callback commits, then the hook reverts
]


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def transactions_for(count, seed, caller, hooks):
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls = []

    def add(function, types, values):
        index = len(calls)
        encoded = encode(types, values)
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        calls.append({'id': str(index), 'function': function[:function.index('(')], 'args': words,
                      'sender': SENDER, 'target': caller,
                      'data': '0x' + keccak(text=function)[:4].hex() + encoded.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(hooks) + 2 + index})

    # Every target through both call shapes, the callbacks called directly, then random calls.
    for index, target in enumerate(targets):
        add('poke(address,uint256)', ['address', 'uint256'], [target, 100 + index])
        add('tryPoke(address,uint256)', ['address', 'uint256'], [target, 200 + index])
    add('enter()', [], [])
    add('enterSmall(uint8)', ['uint8'], [9])
    add('enterThenFail()', [], [])
    while len(calls) < count:
        choice = rng.randrange(6)
        target = rng.choice(targets)
        value = rng.choice([0, 1, rng.getrandbits(8), rng.getrandbits(128)])
        if choice < 2:
            add('poke(address,uint256)', ['address', 'uint256'], [target, value])
        elif choice < 4:
            add('tryPoke(address,uint256)', ['address', 'uint256'], [target, value])
        elif choice == 4:
            add('enter()', [], [])
        else:
            add('enterSmall(uint8)', ['uint8'], [value % 256])
    return calls


def hook_storage(account, hook):
    """The hook constructor's writes: selector, argument count, argument and flags."""
    return [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
            for slot, value in enumerate(hook) if value]


def callback_witness(row, caller):
    """The fixture's callback count after one transaction, as a route observed it."""
    for owner, slot, value in row['storage']:
        if owner.lower() == caller.lower() and int(slot, 16) == CALLBACKS_SLOT:
            return int(value, 16)
    return None


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant and its negative control; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source},
                    HOOK.name: {'content': (root / HOOK).read_text()}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][CONTRACT]
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
    accounts = [address(i + 1) for i in range(len(HOOKS))]
    hooks = ['0x' + mock['bytecode']['object'] + encode(['uint256'] * 4, list(hook)).hex()
             for hook in HOOKS]
    initial = [row for account, hook in zip(accounts, HOOKS, strict=True)
               for row in hook_storage(account, hook)]
    calls = transactions_for(transactions, seed, caller, accounts)
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
              'divergences': result['divergences'], 'seed': seed,
              'hooks': [[str(v) for v in hook] for hook in HOOKS], 'empty': EMPTY,
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
        raise HarnessError('campaign must exercise both successful and reverting calls')
    # The committing hook's first `poke` must have re-entered on every route.
    first = calls.index(next(tx for tx in calls if tx['function'] == 'poke'))
    for route, observed in result['observations'].items():
        if callback_witness(observed[first], caller) != 1:
            raise HarnessError(f'{route}: the first committing callback was not observed')
    # Negative control: the hooks answer without calling back on the model route only.
    skipped = {'program': 'reentrant-callback-v1', 'accounts': [],
               'emptyAccounts': [str(int(a, 16)) for a in accounts] + empty, 'gas': '1000000'}
    control = replay_three_routes(calls[:first + 1], adapters('negative-control', skipped))
    observed = control['observations']
    if (not control['divergences'] or callback_witness(observed['source'][first], caller) != 1
            or callback_witness(observed['model'][first], caller) != 0):
        raise HarnessError('negative control: a model route without callbacks went undetected')
    report['negativeControl'] = {'transactions': first + 1,
                                 'divergences': len(control['divergences'])}
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2911)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 2 * (len(HOOKS) + 2) + 3
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='reentrant-callback-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts)
    if code:
        raise SystemExit(f'reentrant callback divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'value-free CALLs whose callee re-enters the caller once: '
                                    'source EVM / Denote / compiled model, plus a no-callback '
                                    'negative control'})
    print(f'reentrant callback A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
