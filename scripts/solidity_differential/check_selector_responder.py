"""Typed external calls answered by selector-dispatched responders through source EVM, Denote and compiled model.

The fixture calls a `view` function (a `staticcall`), a `bool`-returning function and a
function returning nothing on one account. Each responder (`SelectorCallResponder.sol` on
the EVM side, `selector-call-responder-v1` in Denote) answers by selector from a table in its
storage: entries succeed or fail, answer with short, exact or long data, and are view entries
(answered without writing, also under `staticcall`) or not (recorded; a `staticcall` to them
halts). One account has no code and the sender is an EOA. A divergence is shrunk to a
deletion-minimal sequence.
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

FIXTURE = Path('Contracts/SolidityImportSmoke/SelectorResponderSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/SelectorResponderSequenceModel.lean')
RESPONDER = Path('Contracts/SolidityImportSmoke/SelectorCallResponder.sol')
CONTRACT = 'SelectorResponderFixture'
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "SelectorResponderSequence.sol"'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
RECEIVER = '0x' + '00' * 19 + '99'
EMPTY = '0x' + '00' * 19 + '77'
FAIL, VIEW = 1, 2
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}


def selector(signature):
    return int.from_bytes(keccak(text=signature)[:4], 'big')


QUOTE, PAY, PING = selector('quote(uint256)'), selector('pay(address,uint256)'), selector('ping(uint256)')


def entry(sel, flags, length, *words):
    return [sel, flags, length, *(list(words) + [0, 0, 0, 0])[:4]]


# One table per responder: (selector, flags, answer length, answer words).
TABLES = [
    entry(QUOTE, VIEW, 32, 42) + entry(PAY, 0, 32, 1) + entry(PING, 0, 0),
    entry(QUOTE, VIEW | FAIL, 4, 0xdeadbeef << 224) + entry(PAY, FAIL, 100, 7, 8, 9, 10)
    + entry(PING, FAIL, 0),
    entry(QUOTE, VIEW, 31, 5) + entry(PAY, 0, 32, 2) + entry(PING, 0, 64, 3, 4),
    entry(QUOTE, 0, 32, 6) + entry(PAY, 0, 32, 0) + entry(PING, VIEW, 0),
    [],
]


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def transactions_for(count, seed, caller, responders):
    targets = [*responders, EMPTY, SENDER]
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
                      'blockNumber': len(responders) + 2 + index})

    # Every target through every call shape, then random calls.
    for index, target in enumerate(targets):
        add('ask(address,uint256)', ['address', 'uint256'], [target, index])
        add('settle(address,address,uint256)', ['address', 'address', 'uint256'],
            [target, RECEIVER, 10 + index])
        add('poke(address,uint256)', ['address', 'uint256'], [target, 20 + index])
    add('read()', [], [])
    while len(calls) < count:
        choice = rng.randrange(4)
        target = rng.choice(targets)
        amount = rng.choice([0, 1, rng.getrandbits(8), rng.getrandbits(128)])
        if choice == 0:
            add('ask(address,uint256)', ['address', 'uint256'], [target, amount])
        elif choice == 1:
            add('settle(address,address,uint256)', ['address', 'address', 'uint256'],
                [target, rng.choice([RECEIVER, SENDER]), amount])
        elif choice == 2:
            add('poke(address,uint256)', ['address', 'uint256'], [target, amount])
        else:
            add('read()', [], [])
    return calls


def table_storage(account, table):
    """The responder constructor's writes: the entry count, then each entry's seven words."""
    count = len(table) // 7
    slots = [(0, count)] + [(16 + 8 * (k // 7) + k % 7, word) for k, word in enumerate(table)]
    return [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
            for slot, value in slots]


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
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
                    RESPONDER.name: {'content': (root / RESPONDER).read_text()}},
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
    mock = compiled[RESPONDER.name]['SelectorCallResponder']['evm']
    runtime = '0x' + mock['deployedBytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(TABLES))]
    responders = ['0x' + mock['bytecode']['object'] + encode(['uint256[]'], [table]).hex() for table in TABLES]
    initial = [row for account, table in zip(accounts, TABLES, strict=True)
               for row in table_storage(account, table)]
    calls = transactions_for(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'selector-call-responder-v1',
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
              'tables': [[str(v) for v in t] for t in TABLES], 'empty': EMPTY,
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
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=3307)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 3 * (len(TABLES) + 2) + 1
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='selector-responder-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts)
    if code:
        raise SystemExit(f'selector responder divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'typed external calls against selector-dispatched responders: '
                                    'source EVM / Denote / compiled model'})
    print(f'selector responder A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
