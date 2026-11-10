"""Imported inline-assembly `call` / `staticcall` over memory through source EVM, Denote and compiled model.

The fixture writes calldata into the scratch space (overwriting and restoring the
free-memory pointer and the zero slot), calls with `gas()`, bubbles a failed call's
complete return data, checks empty return data against `extcodesize`, and reads two
`staticcall` return words. Its A/B/C sequence uses the recording call responders
(`ExternalCodeAndLowLevelCallResponder.sol` on the EVM side, `recording-call-responder-v1`
in Denote, which also receives their deployed runtime code), one account without code
and the sender EOA. The responders answer every `call` and fail every `staticcall`,
which writes their storage; both outcomes are compared. A divergence is shrunk to a
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

FIXTURE = Path('Contracts/SolidityImportSmoke/YulMemoryCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/YulMemoryCallSequenceModel.lean')
RESPONDER = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
RECEIVER = '0x' + '00' * 19 + '99'
# (response word, failed, response length): true/false/empty/short/long success, reverts.
RESPONDERS = [
    (1, False, 32),
    (0, False, 32),
    (0, False, 0),
    (2, False, 32),
    (1, False, 31),
    (1, False, 64),
    (1, True, 4),
    (0, True, 0),
    (1, True, 100),
    (1, False, 1),
]
EMPTY = '0x' + '00' * 19 + '77'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "YulMemoryCallSequence.sol"'


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def transactions_for(count, seed, caller, responders):
    tokens = [*responders, EMPTY]
    accounts = [*tokens, SENDER]
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

    selector = keccak(text='transfer(address,uint256)')[:4]
    # Every account through every call shape, then random calls.
    for account in accounts:
        add('codeSize(address)', ['address'], [account])
    for index, token in enumerate(tokens):
        add('push(address,address,uint256)', ['address', 'address', 'uint256'],
            [token, RECEIVER, 100 + index])
        add('pull(address,address,address,uint256)', ['address', 'address', 'address', 'uint256'],
            [token, SENDER, RECEIVER, 1 + index])
        add('query(address,address,address,bytes4)', ['address', 'address', 'address', 'bytes4'],
            [token, SENDER, RECEIVER, selector])
    add('read()', [], [])
    while len(calls) < count:
        choice = rng.randrange(5)
        token = rng.choice(tokens)
        amount = rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(256)])
        if choice == 0:
            add('codeSize(address)', ['address'], [rng.choice(accounts)])
        elif choice == 1:
            add('push(address,address,uint256)', ['address', 'address', 'uint256'],
                [token, rng.choice([RECEIVER, SENDER]), amount])
        elif choice == 2:
            add('pull(address,address,address,uint256)', ['address', 'address', 'address', 'uint256'],
                [token, rng.choice([RECEIVER, SENDER]), RECEIVER, amount])
        elif choice == 3:
            add('query(address,address,address,bytes4)', ['address', 'address', 'address', 'bytes4'],
                [token, SENDER, rng.choice([RECEIVER, SENDER]), rng.getrandbits(32).to_bytes(4, 'big')])
        else:
            add('read()', [], [])
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC, *,
             contract='YulMemoryCallFixture', anchor=ANCHOR, plan=transactions_for):
    """Run one imported variant of `contract` against the recording responders, one
    account without code and the sender; `plan(count, seed, caller, responders)` lists
    the transactions. Returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(anchor) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"'))
    responder_source = (root / RESPONDER).read_text()
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}, RESPONDER.name: {'content': responder_source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][contract]
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
    mock = compiled[RESPONDER.name]['RecordingCallResponder']['evm']
    runtime = '0x' + mock['deployedBytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(RESPONDERS))]
    responders = ['0x' + mock['bytecode']['object'] + encode(['uint256', 'bool', 'uint256'], list(p)).hex()
                  for p in RESPONDERS]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
               for account, parameters in zip(accounts, RESPONDERS, strict=True)
               for slot, value in enumerate(parameters)]
    calls = plan(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'recording-call-responder-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   # The sender is an EOA: a call that reaches it succeeds with no effect.
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
    if not any(row['status'] == 'revert' and len(row['data']) > 2 + 8 * 2 for row in rows):
        raise HarnessError('campaign must forward a multi-word child revert payload')
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2531)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = (len(RESPONDERS) + 2) + 3 * (len(RESPONDERS) + 1) + 1
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every account and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='yul-memory-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts)
    if code:
        raise SystemExit(f'Yul memory call divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported inline-assembly call/staticcall over memory: '
                                    'source EVM / Denote / compiled model'})
    print(f'Yul memory call A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
