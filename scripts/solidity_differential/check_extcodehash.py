"""Imported `<address>.codehash` reads through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently; its A/B/C sequence
probes accounts with runtime code (deployed on the EVM routes from raw initcode,
installed verbatim in Denote's account world), two funded EOAs without code
(the deployer, with a nonzero nonce, and an unused prefunded account with nonce
zero), a never-touched address and a precompile address. On the EVM routes the
EOAs hold anvil's genesis balance; Denote is given the same nonzero balance and
no nonce, since only the existence of an account without code is observed
(EIP-1052: `0` for an empty account, `keccak256("")` for an existing one). The
executing contract's own address is never probed: its code differs between the
source and compiled routes and is not modeled. A divergence is shrunk to a
deletion-minimal sequence. Equivalent variants must produce identical
observations.
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
from .programs import stateful_extcodehash_source
from .stateful import replay_three_routes, shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/ExtCodeHashSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/ExtCodeHashSequenceModel.lean')
CONTRACT = 'ExtCodeHashFixture'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
# anvil's second prefunded account: a balance, nonce zero, never used.
FUNDED = '0x70997970c51812dc3a010c7d01b50e0d17dc79c8'
# anvil's genesis balance of its prefunded accounts (10000 ether).
GENESIS_BALANCE = 10000 * 10 ** 18
EMPTY = '0x' + '00' * 19 + '77'
NONCE_ONLY = '0x' + '00' * 19 + '88'
PRECOMPILE = '0x' + '00' * 19 + '01'
# Copies everything after this 11-byte prefix as the runtime code.
PREFIX = bytes.fromhex('600b380380600b5f395ff3')
# Runtime codes: the fixture's bound code (`BOUND_CODEHASH`), a one-byte code,
# and a multi-word code whose length is not a multiple of 32.
RUNTIMES = [bytes.fromhex('5f5ff3'), bytes.fromhex('00'),
            bytes([0x00]) + bytes((7 * i + 3) % 256 for i in range(76))]
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ExtCodeHashSequence.sol"'
SINGLE = ['codeHash(address)', 'isBound(address)', 'classify(address)', 'record(address)',
          'recordBound(address)', 'stored(address)']


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    """Imported roots, in model order, as Solidity signatures."""
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def transactions_for(count, seed, caller, coded):
    accounts = [*coded, SENDER, FUNDED, NONCE_ONLY, EMPTY, PRECOMPILE]
    rng = random.Random(seed)
    calls = []

    def add(function, values):
        index = len(calls)
        types = ['address'] * len(values)
        selector = keccak(text=function)[:4].hex()
        calls.append({'id': str(index), 'function': function[:function.index('(')],
                      'args': [int(v, 16) for v in values], 'sender': SENDER, 'target': caller,
                      'data': '0x' + selector + encode(types, values).hex(), 'value': '0x0',
                      'timestamp': 1000000100 + index, 'blockNumber': len(coded) + 2 + index})

    # Deterministic prefix: every account through every root, then every pair.
    for account in accounts:
        for function in SINGLE:
            add(function, [account])
    for left in accounts:
        for right in accounts:
            add('sameCode(address,address)', [left, right])
    while len(calls) < count:
        function = rng.choice([*SINGLE, 'sameCode(address,address)'])
        if function.startswith('sameCode'):
            add(function, [rng.choice(accounts), rng.choice(accounts)])
        else:
            add(function, [rng.choice(accounts)])
    return calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported code-hash source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol'][CONTRACT]
    identifiers = compiled['evm']['methodIdentifiers']
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
    caller_a = '0x' + compiled['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    caller = address(0)
    coded = [address(i + 1) for i in range(len(RUNTIMES))]
    initcodes = ['0x' + (PREFIX + runtime).hex() for runtime in RUNTIMES]
    calls = transactions_for(transactions, seed, caller, coded)
    write_json(directory / 'transactions.json', calls)
    adapters = {
        'source': EVM(directory / 'A', [caller_a, *initcodes], account_nonces=[(NONCE_ONLY, 1)]),
        'model': Denote(directory / 'B', driver, caller, byte_call_environment={},
                        account_code=[(a, '0x' + r.hex()) for a, r in zip(coded, RUNTIMES, strict=True)],
                        account_balance=[(SENDER, GENESIS_BALANCE), (FUNDED, GENESIS_BALANCE)],
                        external_account_nonce=[(NONCE_ONLY, 1)]),
        'compiled': EVM(directory / 'C', [caller_c, *initcodes], account_nonces=[(NONCE_ONLY, 1)])}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed,
              'runtimes': ['0x' + r.hex() for r in RUNTIMES], 'coded': coded,
              'eoas': [SENDER, FUNDED, NONCE_ONLY], 'empty': [EMPTY, PRECOMPILE],
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
    # The three EIP-1052 cases must all be observed: code, existing without code, empty.
    hashes = {row['data'] for call, row in zip(calls, rows, strict=True)
              if call['function'] == 'codeHash' and row['status'] == 'ok'}
    expected = {'0x' + keccak(r).hex() for r in RUNTIMES} | {'0x' + keccak(b'').hex(), '0x' + '00' * 32}
    if hashes != expected:
        raise HarnessError(f'campaign must observe every code-hash case: {sorted(hashes)}')
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
    parser.add_argument('--transactions', type=int, default=128)
    parser.add_argument('--seed', type=int, default=2627)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    accounts = len(RUNTIMES) + 4
    minimum = accounts * len(SINGLE) + accounts * accounts
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every account and root')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='extcodehash-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_extcodehash_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'code-hash divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'code-hash variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported <address>.codehash: source EVM / Denote / compiled model'})
    print(f'code-hash variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
