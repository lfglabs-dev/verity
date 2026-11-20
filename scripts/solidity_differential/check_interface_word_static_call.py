"""Imported typed-interface word staticcalls through source EVM, Denote and compiled model.

Covers static word arguments (`address`, `uint256`, `bytes32`, `bool`, `enum`), `bool`,
`bytes32`, `bytes4` and `int256` returns, and calls placed in short-circuit operands and `require`
conditions. Every variant of the fixture is imported independently; its A/B/C
sequence uses calldata-folding oracle mocks (`InterfaceWordStaticCallOracle.sol`
on the EVM side, `word-static-oracle-v1` in Denote) plus one account without
code. A divergence is shrunk to a deletion-minimal sequence. Equivalent variants
must produce identical observations.
"""
import argparse
import hashlib
import json
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
from .programs import stateful_interface_word_static_call_source
from .stateful import replay_three_routes, shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/InterfaceWordStaticCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/InterfaceWordStaticCallSequenceModel.lean')
ORACLE = Path('Contracts/SolidityImportSmoke/InterfaceWordStaticCallOracle.sol')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
WORD = (1 << 256) - 1
# (value, failed, response length, mask): constant/argument-dependent valid bools,
# invalid bools, full calldata folds, short/long successes and both revert kinds.
ORACLES = [
    (1, False, 32, 0),
    (0, False, 32, 0),
    (0, False, 32, 1),
    (1, False, 32, 1),
    (2, False, 32, 0),
    (0, False, 32, WORD),
    (1, False, 31, 0),
    (0, False, 65, 1),
    (11, True, 65, 0),
    (13, True, 0, 0),
    (WORD - 1, False, 96, 1),
    (0x87654321 << 224, False, 33, 0),  # left-aligned bytes4, negative int256
    ((0x87654321 << 224) | (1 << 223), False, 32, 0),  # highest dirty padding bit
    (0, False, 0, 0),  # empty success from code, distinct from EMPTY
]
EMPTY = '0x' + '00' * 19 + '77'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "InterfaceWordStaticCallSequence.sol"'


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    """Imported roots, in model order, as Solidity signatures."""
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def transactions_for(count, seed, caller, oracles):
    targets = [*oracles, EMPTY]
    rng = random.Random(seed)
    calls = []

    def add(function, types, values):
        index = len(calls)
        selector = keccak(text=function)[:4].hex()
        name = function[:function.index('(')]
        words = [int(v, 16) if isinstance(v, str) else int.from_bytes(v, 'big')
                 if isinstance(v, bytes) else int(v) for v in values]
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                      'target': caller, 'data': '0x' + selector + encode(types, values).hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(oracles) + 2 + index})

    def account():
        return rng.choice([*targets, SENDER, '0x' + rng.getrandbits(160).to_bytes(20, 'big').hex()])

    # Deterministic prefix: every target through every call shape, the gate
    # short-circuit on the zero address, and the helper pair in both orders.
    for target in targets:
        add('readPrefix(address)', ['address'], [target])
        add('readSigned(address)', ['address'], [target])
        add('check(address,address)', ['address', 'address'], [target, SENDER])
        add('gated(address,uint256)', ['address', 'uint256'], [target, len(calls) + 1])
        add('both(address,address,uint256)', ['address', 'address', 'uint256'],
            [target, target, len(calls)])
        add('both(address,address,uint256)', ['address', 'address', 'uint256'],
            [target, SENDER, len(calls) + 1])
        add('price(address,uint256,bytes32)', ['address', 'uint256', 'bytes32'],
            [target, len(calls), bytes([len(calls)]) * 32])
        add('stamp(address,address,bool)', ['address', 'address', 'bool'],
            [target, SENDER, len(calls) % 2 == 0])
        add('route(address,uint256,uint8)', ['address', 'uint256', 'uint8'],
            [target, len(calls), len(calls) % 3])
    # An out-of-range ordinal panics (0x21) before the call.
    add('route(address,uint256,uint8)', ['address', 'uint256', 'uint8'], [targets[2], 9, 3])
    add('gated(address,uint256)', ['address', 'uint256'], ['0x' + '00' * 20, 5])
    for first, second in [(0, 1), (1, 0), (1, 2), (2, 1), (4, 8), (8, 4), (1, -1), (-1, 1), (6, 9)]:
        add('either(address,address)', ['address', 'address'], [targets[first], targets[second]])
    add('stored()', [], [])
    while len(calls) < count:
        choice = rng.randrange(8)
        target = rng.choice(targets)
        if choice == 0:
            add('check(address,address)', ['address', 'address'], [target, account()])
        elif choice == 1:
            gate = '0x' + '00' * 20 if rng.randrange(4) == 0 else target
            add('gated(address,uint256)', ['address', 'uint256'], [gate, rng.getrandbits(256)])
        elif choice == 2:
            add('both(address,address,uint256)', ['address', 'address', 'uint256'],
                [target, account(), rng.getrandbits(256)])
        elif choice == 3:
            add('price(address,uint256,bytes32)', ['address', 'uint256', 'bytes32'],
                [target, rng.getrandbits(256), rng.getrandbits(256).to_bytes(32, 'big')])
        elif choice == 4:
            add('stamp(address,address,bool)', ['address', 'address', 'bool'],
                [target, account(), rng.randrange(2) == 1])
        elif choice == 6:
            add('route(address,uint256,uint8)', ['address', 'uint256', 'uint8'],
                [target, rng.getrandbits(256), rng.choice([0, 1, 2, 2, 3, 255])])
        elif choice == 5:
            add('either(address,address)', ['address', 'address'], [target, rng.choice(targets)])
        else:
            add('stored()', [], [])
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported interface word staticcall source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    oracle_source = (root / ORACLE).read_text()
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}, ORACLE.name: {'content': oracle_source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol']['InterfaceWordStaticCallFixture']
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
    mock = compiled[ORACLE.name]['WordStaticOracle']['evm']['bytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(ORACLES))]
    oracles = ['0x' + mock + encode(['uint256', 'bool', 'uint256', 'uint256'], list(p)).hex()
               for p in ORACLES]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
               for account, parameters in zip(accounts, ORACLES, strict=True)
               for slot, value in enumerate(parameters)]
    calls = transactions_for(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'word-static-oracle-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   # The zero address is the short-circuited gate target; it is
                   # code-less on the EVM routes, so an eagerly evaluated call
                   # (a lowering bug) is a Solidity-level observation, not an
                   # out-of-domain instrumentation error.
                   'emptyAccounts': [str(int(EMPTY, 16)), '0'], 'gas': '1000000'}
    adapters = {
        'source': EVM(directory / 'A', [caller_a, *oracles], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment),
        'compiled': EVM(directory / 'C', [caller_c, *oracles], initial)}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed,
              'oracles': [[str(v) for v in p] for p in ORACLES], 'empty': EMPTY,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    statuses = {row['status'] for row in result['observations']['source']}
    if statuses != {'ok', 'revert'}:
        raise HarnessError('campaign must exercise both successful and reverting calls')
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
    parser.add_argument('--transactions', type=int, default=160)
    parser.add_argument('--seed', type=int, default=2549)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 9 * (len(ORACLES) + 1) + 12
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and helper order')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='interface-word-static-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_interface_word_static_call_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'interface word staticcall divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'interface word staticcall variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported typed-interface word staticcall: source EVM / Denote / compiled model'})
    print(f'interface word staticcall variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
