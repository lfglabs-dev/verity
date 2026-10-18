"""Imported code-length reads and optional-bool low-level calls through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently; its A/B/C sequence uses
recording call responders (`ExternalCodeAndLowLevelCallResponder.sol` on the EVM
side, `recording-call-responder-v1` in Denote, which also receives their deployed
runtime code), one account without code and the sender EOA. A divergence is
shrunk to a deletion-minimal sequence. Equivalent variants must produce
identical observations.
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
from .programs import stateful_external_code_and_low_level_call_source
from .stateful import replay_three_routes, shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallSequenceModel.lean')
RESPONDER = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
RECEIVER = '0x' + '00' * 19 + '99'
# (response word, failed, response length)
RESPONDERS = [
    (1, False, 32),
    (0, False, 32),
    (0, False, 0),
    (2, False, 32),
    (1, False, 31),
    (1, False, 64),
    (1, True, 4),
    (0, True, 0),
    ((1 << 256) - 1, False, 32),
    (1, True, 100),
    (1, False, 1),
]
EMPTY = '0x' + '00' * 19 + '77'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ExternalCodeAndLowLevelCallSequence.sol"'


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    """Imported roots, in model order, as Solidity signatures."""
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
        words = [int(v, 16) if isinstance(v, str) else int(v) for v in values]
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                      'target': caller, 'data': '0x' + selector + encode(types, values).hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(responders) + 2 + index})

    # Deterministic prefix: every account through both code-length reads, then
    # every token through each call shape, withdrawing what was deposited.
    for account in accounts:
        add('codeSize(address)', ['address'], [account])
        add('hasCode(address)', ['address'], [account])
    for index, token in enumerate(tokens):
        add('deposit(address,uint256)', ['address', 'uint256'], [token, 100 + index])
        add('withdraw(address,address,uint256)', ['address', 'address', 'uint256'],
            [token, RECEIVER, 1 + index % 3])
        add('pay(address,address,uint256)', ['address', 'address', 'uint256'],
            [token, RECEIVER, index])
    add('stored(address)', ['address'], [SENDER])
    while len(calls) < count:
        choice = rng.randrange(6)
        token = rng.choice(tokens)
        amount = rng.choice([0, 1, 7, rng.getrandbits(8), rng.getrandbits(256)])
        if choice == 0:
            add('codeSize(address)', ['address'], [rng.choice(accounts)])
        elif choice == 1:
            add('hasCode(address)', ['address'], [rng.choice(accounts)])
        elif choice == 2:
            add('deposit(address,uint256)', ['address', 'uint256'], [token, amount])
        elif choice == 3:
            add('withdraw(address,address,uint256)', ['address', 'address', 'uint256'],
                [token, rng.choice([RECEIVER, SENDER]), amount % 200])
        elif choice == 4:
            add('pay(address,address,uint256)', ['address', 'address', 'uint256'],
                [token, rng.choice([RECEIVER, SENDER]), amount])
        else:
            add('stored(address)', ['address'], [SENDER])
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported low-level call source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    responder_source = (root / RESPONDER).read_text()
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}, RESPONDER.name: {'content': responder_source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol']['ExternalCodeAndLowLevelCallFixture']
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
    calls = transactions_for(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'recording-call-responder-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': [str(int(EMPTY, 16))], 'gas': '1000000'}
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
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2527)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 2 * (len(RESPONDERS) + 2) + 3 * (len(RESPONDERS) + 1) + 1
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every account and call shape')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='external-code-low-level-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_external_code_and_low_level_call_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'code-length/low-level call divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'code-length/low-level call variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported <address>.code.length and optional-bool low-level call: '
                 'source EVM / Denote / compiled model'})
    print(f'code-length/low-level call variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
