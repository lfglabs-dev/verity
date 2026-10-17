"""Imported typed-interface staticcalls through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently; its A/B/C sequence uses
selector-checked oracle mocks (`InterfaceStaticCallOracle.sol` on the EVM side,
`checked-static-oracle-v1` in Denote) plus one account without code. A
divergence is shrunk to a deletion-minimal sequence. Equivalent variants must
produce identical observations.
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
from .programs import stateful_interface_static_call_source
from .stateful import replay_three_routes, shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/InterfaceStaticCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/InterfaceStaticCallSequenceModel.lean')
ORACLE = Path('Contracts/SolidityImportSmoke/InterfaceStaticCallOracle.sol')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
PRICE = 0xa035b1fe
EXPECTED = PRICE << 224
# (value, failed, response length, expected first calldata word, expected calldata length)
ORACLES = [
    (42, False, 32, EXPECTED, 4),
    ((1 << 256) - 1, False, 32, EXPECTED, 4),
    (7, False, 31, EXPECTED, 4),
    (9, False, 65, EXPECTED, 4),
    (11, True, 65, EXPECTED, 4),
    (13, True, 0, EXPECTED, 4),
    (17, True, 33, EXPECTED, 4),
    (5, False, 32, EXPECTED + 1, 4),
    (6, False, 32, EXPECTED, 36),
    (1 << 255, False, 96, EXPECTED, 4),
]
EMPTY = '0x' + '00' * 19 + '77'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "InterfaceStaticCallSequence.sol"'


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
        words = [int(v, 16) if isinstance(v, str) else int(v) for v in values]
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                      'target': caller, 'data': '0x' + selector + encode(types, values).hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index,
                      'blockNumber': len(oracles) + 2 + index})

    # Deterministic prefix: every target through every call shape, then the
    # helper pair in both orders over failing/overflowing oracles.
    for target in targets:
        add('read(address)', ['address'], [target])
        add('record(address,uint256)', ['address', 'uint256'], [target, len(calls) + 1])
        add('ping(address,uint256)', ['address', 'uint256'], [target, len(calls) % 2])
        add('probe(address,uint256)', ['address', 'uint256'], [target, len(calls) + 1])
    for first, second in [(0, 1), (1, 1), (4, 6), (6, 4), (0, 2), (2, 0), (5, 3), (9, 9), (0, 10), (7, 8)]:
        add('sum(address,address)', ['address', 'address'], [targets[first], targets[second]])
    add('stored()', [], [])
    while len(calls) < count:
        choice = rng.randrange(6)
        target = rng.choice(targets)
        if choice == 0:
            add('read(address)', ['address'], [target])
        elif choice == 1:
            add('record(address,uint256)', ['address', 'uint256'], [target, rng.getrandbits(256)])
        elif choice == 2:
            add('ping(address,uint256)', ['address', 'uint256'], [target, rng.getrandbits(256)])
        elif choice == 5:
            add('probe(address,uint256)', ['address', 'uint256'], [target, rng.getrandbits(256)])
        elif choice == 3:
            add('sum(address,address)', ['address', 'address'], [target, rng.choice(targets)])
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
        raise HarnessError('nonunique imported interface staticcall source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    oracle_source = (root / ORACLE).read_text()
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}, ORACLE.name: {'content': oracle_source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol']['InterfaceStaticCallFixture']
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
    mock = compiled[ORACLE.name]['CheckedStaticOracle']['evm']['bytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(ORACLES))]
    oracles = ['0x' + mock + encode(['uint256', 'bool', 'uint256', 'uint256', 'uint256'], list(p)).hex()
               for p in ORACLES]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(value).to_bytes(32, 'big').hex())
               for account, parameters in zip(accounts, ORACLES, strict=True)
               for slot, value in enumerate(parameters)]
    calls = transactions_for(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'checked-static-oracle-v1',
                   'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': [str(int(EMPTY, 16))], 'gas': '1000000'}
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
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2512)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    minimum = 4 * (len(ORACLES) + 1) + 11
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and helper order')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='interface-static-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_interface_static_call_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'interface staticcall divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'interface staticcall variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported typed-interface uint256 staticcall: source EVM / Denote / compiled model'})
    print(f'interface staticcall variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
