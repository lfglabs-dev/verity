"""Imported CREATE2 code storage and struct events through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently. CREATE2 runs in Denote
through the physical-memory `create2` transport with an instrument-supplied
parent gas allowance; no deployment result is supplied to the model. Created
accounts are discovered from both EVM routes' opcode traces and replayed on
one cumulative plan, so code, nonces and balances of every attempted account
are compared, alongside return data, storage and exact logs. A divergence is
shrunk to a deletion-minimal sequence. Equivalent variants must produce
identical observations.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .denote import SequenceAdapter as Denote
from .deployment import DeploymentSequenceAdapter, replay_deployment_routes
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .programs import stateful_create2_struct_emit_source
from .stateful import shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/Create2BytecodeAndStructEmitSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/Create2BytecodeAndStructEmitSequenceModel.lean')
CONTRACT = 'Create2BytecodeAndStructEmitSequence'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SPEC = '(uint256,address,(address,uint256)[],uint256)'
LEG = '(address,uint256)'
SIGNATURES = [f'create({SPEC})', f'storeAt({SPEC},bytes32)', f'storeLeg({LEG},uint256)', 'count()']
# Parent gas at the CREATE2 opcode. Payloads stay far below this allowance on
# every route, so no case depends on the gas consumed before the opcode.
GAS = 9_000_000
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "Create2BytecodeAndStructEmitSequence.sol"'


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def specs(rng):
    """A small pool, so repeated specs exercise skipped and colliding creations."""
    def leg():
        return ('0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(), rng.getrandbits(256))
    pool = [(0, '0x' + '00' * 20, [], 0),
            (1, SENDER, [leg()], (1 << 256) - 1),
            (2, '0x' + 'ff' * 20, [leg(), leg(), leg()], 7),
            (rng.getrandbits(256), '0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(),
             [leg() for _ in range(4)], rng.getrandbits(256))]
    # Denote's physical memory is a closure chain, so byte copies cost time
    # quadratic in the payload; small arrays keep the model route tractable.
    pool += [(rng.getrandbits(64), '0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(),
              [leg() for _ in range(rng.randrange(3))], rng.getrandbits(32)) for _ in range(3)]
    return pool


def transactions_for(count, seed, caller):
    rng = random.Random(seed)
    pool = specs(rng)
    legs = [('0x' + '11' * 20, 5), ('0x' + '00' * 20, 0), (SENDER, (1 << 256) - 1)]
    calls = []

    def add(signature, types, values):
        index = len(calls)
        payload = encode(types, values)
        calls.append({'id': str(index), 'function': signature[:signature.index('(')],
                      'args': [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)],
                      'sender': SENDER, 'target': caller,
                      'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})

    create, store_at, store_leg, total = SIGNATURES
    # Deterministic prefix: first creation, its skipped repeat, salt collisions
    # with and without a prior creation, a fresh salt, and leg pointers that
    # collide (CREATE2 then yields the zero address, which is still logged).
    add(total, [], [])
    add(create, [SPEC], [pool[1]])
    add(create, [SPEC], [pool[1]])
    add(store_at, [SPEC, 'bytes32'], [pool[1], bytes(32)])
    add(store_at, [SPEC, 'bytes32'], [pool[1], (1).to_bytes(32, 'big')])
    add(store_at, [SPEC, 'bytes32'], [pool[1], (1).to_bytes(32, 'big')])
    add(store_leg, [LEG, 'uint256'], [legs[0], 5])
    add(store_leg, [LEG, 'uint256'], [legs[0], 5])
    for spec in pool:
        add(create, [SPEC], [spec])
    add(store_at, [SPEC, 'bytes32'], [pool[0], bytes(32)])
    add(store_at, [SPEC, 'bytes32'], [pool[3], (2).to_bytes(32, 'big')])
    add(total, [], [])
    while len(calls) < count:
        choice = rng.randrange(5)
        if choice == 0:
            add(create, [SPEC], [rng.choice(pool)])
        elif choice == 1:
            salt = rng.choice([0, 1, 2, rng.getrandbits(256)])
            add(store_at, [SPEC, 'bytes32'], [rng.choice(pool), salt.to_bytes(32, 'big')])
        elif choice == 2:
            add(store_leg, [LEG, 'uint256'], [rng.choice(legs), rng.choice([0, 5, rng.getrandbits(256)])])
        else:
            add(total, [], [])
    return calls


class ModelDeployment:
    """Denote route observing exactly the EVM-discovered deployment plan."""
    def __init__(self, adapter):
        self.adapter = adapter

    def __call__(self, transactions, slot_plan, account_plan):
        if len(transactions) != len(account_plan):
            raise HarnessError('model deployment plan does not cover the sequence')
        for transaction, plan in zip(transactions, account_plan):
            transaction['observeAccounts'] = list(plan)
        return self.adapter(transactions, slot_plan)


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    """Run one imported variant; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported CREATE2 sequence source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol'][CONTRACT]
    identifiers = compiled['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in SIGNATURES])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    caller = address(0)
    calls = transactions_for(transactions, seed, caller)
    write_json(directory / 'transactions.json', calls)
    adapters = {
        'source': DeploymentSequenceAdapter(directory / 'A', ['0x' + compiled['evm']['bytecode']['object']], caller),
        # Byte-level memory copies are slow in the executable model; allow it
        # a longer replay budget than the scalar fixtures' default.
        'model': ModelDeployment(Denote(directory / 'B', driver, caller, account_nonce=1,
                                        byte_call_environment={'gas': str(GAS)}, timeout=1200)),
        'compiled': DeploymentSequenceAdapter(
            directory / 'C', ['0x' + next(iter(generated.values()))['evm']['bytecode']['object']], caller)}
    result = replay_deployment_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'], 'accounts': result['accounts'],
              'divergences': result['divergences'], 'seed': seed, 'gas': GAS,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_deployment_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    statuses = {row['status'] for row in result['observations']['source']}
    if statuses != {'ok', 'revert'}:
        raise HarnessError('campaign must exercise both successful and reverting calls')
    if not any(row['deployment']['accounts'] for row in result['observations']['source']):
        raise HarnessError('campaign created no account')
    write_json(directory / 'campaign.json', report)
    return 0, report


def canonical(observations):
    result = {}
    for route, rows in observations.items():
        result[route] = []
        for row in rows:
            base = {k: v for k, v in row.items() if k != 'deployment'}
            touched, storage = validate_observation(base)
            result[route].append({**row, 'touched': [list(k) for k in sorted(touched)],
                                  'storage': [[*k, storage[k]] for k in sorted(storage)]})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--seed', type=int, default=2520)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < 18:
        parser.error('at least 18 transactions cover the deterministic prefix')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='create2-struct-emit-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_create2_struct_emit_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'CREATE2/struct-event divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'CREATE2/struct-event variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported CREATE2 code storage and struct events: source EVM / Denote / compiled model'})
    print(f'CREATE2/struct-event variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
