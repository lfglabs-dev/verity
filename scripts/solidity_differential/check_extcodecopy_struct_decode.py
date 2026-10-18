"""Imported `<address>.code` reads and dynamic-struct `abi.decode` returns through source EVM, Denote and compiled model.

Every variant of the fixture is imported independently. Code is stored by the
closed CREATE2 transport (canonical struct encodings and raw, deliberately
malformed payloads), then read back by the closed code-copy transport, decoded
from memory and re-encoded by the closed memory-return transport. Denote reads
code only from its own account world; no code is supplied to the model.
Created accounts are discovered from both EVM routes' opcode traces, so code,
nonces and balances of every attempted account are compared alongside return
data, storage and logs. A divergence is shrunk to a deletion-minimal sequence.
Equivalent variants must produce identical observations.
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
from .programs import stateful_extcodecopy_struct_decode_source
from .stateful import shrink_sequence, validate_observation

FIXTURE = Path('Contracts/SolidityImportSmoke/ExtCodeCopyStructDecodeSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/ExtCodeCopyStructDecodeSequenceModel.lean')
CONTRACT = 'ExtCodeCopyStructDecodeSequence'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SPEC = '(uint256,address,(address,uint96,bool)[],uint64[],uint256)'
SIGNATURES = [f'store({SPEC})', 'storeRaw(bytes,bytes32)', 'load(bytes32)', 'summary(address)',
              f'echo({SPEC})']
PREFIX = bytes.fromhex('600b380380600b5f395ff3')
# Parent gas at the CREATE2 opcode. Payloads stay far below this allowance on
# every route, so no case depends on the gas consumed before the opcode.
GAS = 9_000_000
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ExtCodeCopyStructDecodeSequence.sol"'
# Length of the deterministic prefix of `transactions_for`.
PREFIX_TRANSACTIONS = 81


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def create2_address(deployer, salt, payload):
    digest = keccak(b'\xff' + bytes.fromhex(deployer[2:]) + salt + keccak(PREFIX + payload))
    return '0x' + digest[-20:].hex()


def word(value):
    return value.to_bytes(32, 'big')


def specs(rng):
    """A small pool, so repeated specs exercise skipped stores."""
    def leg():
        return ('0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(), rng.getrandbits(96),
                rng.random() < 0.5)
    pool = [(0, '0x' + '00' * 20, [], [], 0),
            (1, SENDER, [leg()], [7], (1 << 256) - 1),
            (2, '0x' + 'ff' * 20, [leg(), leg(), leg()], [], 7),
            (rng.getrandbits(256), '0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(),
             [leg() for _ in range(2)], [(1 << 64) - 1, 0, rng.getrandbits(64)], rng.getrandbits(256))]
    # Denote's physical memory is a closure chain, so byte copies cost time
    # quadratic in the payload; small arrays keep the model route tractable.
    pool += [(rng.getrandbits(64), '0x' + rng.getrandbits(160).to_bytes(20, 'big').hex(),
              [leg() for _ in range(rng.randrange(3))],
              [rng.getrandbits(64) for _ in range(rng.randrange(3))], rng.getrandbits(32))
             for _ in range(2)]
    return pool


def raw_payloads(pool):
    """Code payloads around every decoder check, valid and malformed."""
    canonical = encode([SPEC], [pool[3]])
    one_leg = encode([SPEC], [pool[1]])

    def head(tag=5, owner=0x1234, legs=0xa0, marks=None, deadline=9):
        return [tag, owner, legs, marks if marks is not None else legs + 32, deadline]

    def blob(struct_offset, words, tail=b''):
        return word(struct_offset) + b''.join(word(w) for w in words) + tail

    empty_arrays = blob(32, head(legs=0xa0, marks=0xa0), word(0))
    # Valid, but not canonical: arrays out of order, shared, with gaps and trailing bytes.
    reordered = blob(32, head(legs=0xe0, marks=0xa0),
                     word(1) + word(3) + word(1) + word(0xaa) + word(2**96 - 1) + word(1) + b'\x01\x02')
    shared = blob(32, head(legs=0xa0, marks=0xa0), word(0)) + b'\x00' * 7
    backwards = blob(32, head(tag=1, legs=0, marks=0xa0), word(0))
    gap = word(64) + word(2**255) + b''.join(word(w) for w in head(legs=0xc0, marks=0xa0)) + \
        word(0) + word(0)
    return {
        'canonical': canonical,
        'one-leg': one_leg,
        'empty-arrays': empty_arrays,
        'reordered': reordered,
        'shared': shared,
        'backwards': backwards,
        'gap': gap,
        'empty': b'',
        'short': word(32)[:31],
        'struct-offset-high': blob(2**64, head()),
        'struct-head-truncated': blob(32, head())[:5 * 32],
        'dirty-owner': blob(32, head(owner=2**160), word(0)),
        'dirty-mark': blob(32, head(legs=0xa0, marks=0xc0), word(0) + word(1) + word(2**64)),
        'dirty-weight': blob(32, head(legs=0xa0, marks=0xa0),
                             word(1) + word(1) + word(2**96) + word(1)),
        'dirty-active': blob(32, head(legs=0xc0, marks=0xa0),
                             word(0) + word(1) + word(1) + word(1) + word(2)),
        'array-offset-high': blob(32, head(legs=2**64, marks=0xa0), word(0)),
        'array-header-outside': blob(32, head(legs=0xa0, marks=0x2000), word(0)),
        'array-length-panic': blob(32, head(legs=0xa0, marks=0xc0), word(2**64) + word(0)),
        'array-allocation-panic': blob(32, head(legs=0xa0, marks=0xc0), word(2**59) + word(0)),
        'array-payload-truncated': blob(32, head(legs=0xa0, marks=0xc0), word(3) + word(0) +
                                        word(1) + word(1)),
        'leg-payload-truncated': blob(32, head(legs=0xa0, marks=0xa0), word(1) + word(1) + word(2)),
        'marks-payload-truncated': blob(32, head(legs=0xa0, marks=0xc0), word(0) + word(2) + word(5)),
    }


def transactions_for(count, seed, caller):
    rng = random.Random(seed)
    pool = specs(rng)
    payloads = raw_payloads(pool)
    calls = []
    pointers = []

    def add(signature, types, values):
        index = len(calls)
        payload = encode(types, values)
        calls.append({'id': str(index), 'function': signature[:signature.index('(')],
                      'args': [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)],
                      'sender': SENDER, 'target': caller,
                      'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})

    store, store_raw, load, summary, echo = SIGNATURES

    def store_spec(spec):
        key = keccak(encode([SPEC], [spec]))
        pointer = create2_address(caller, key, encode([SPEC], [spec]))
        add(store, [SPEC], [spec])
        pointers.append(pointer)

    def store_payload(name, salt):
        add(store_raw, ['bytes', 'bytes32'], [payloads[name], salt])
        pointers.append(create2_address(caller, salt, payloads[name]))

    def load_pointer(pointer):
        add(load, ['bytes32'], [word(int(pointer, 16))])

    # Deterministic prefix: a load before any store, every stored spec read
    # back, every raw payload stored and read through both decoding roots, a
    # missing account and the executing contract's caller, and echoes.
    load_pointer(SENDER)
    for spec in pool[:4]:
        store_spec(spec)
        load_pointer(pointers[-1])
    store_spec(pool[1])
    for index, name in enumerate(payloads):
        store_payload(name, word(index + 1))
        load_pointer(pointers[-1])
        add(summary, ['address'], [pointers[-1]])
    store_payload('canonical', word(1))
    load_pointer('0x' + '00' * 19 + '01')
    add(summary, ['address'], [SENDER])
    add(echo, [SPEC], [pool[2]])
    add(echo, [SPEC], [pool[3]])
    while len(calls) < count:
        choice = rng.randrange(6)
        if choice == 0:
            store_spec(rng.choice(pool))
        elif choice == 1:
            store_payload(rng.choice(list(payloads)), word(rng.choice([1, 2, rng.getrandbits(256)])))
        elif choice == 2:
            load_pointer(rng.choice(pointers + [SENDER]))
        elif choice == 3:
            add(summary, ['address'], [rng.choice(pointers)])
        else:
            add(echo, [SPEC], [rng.choice(pool)])
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
        raise HarnessError('nonunique imported code-decoding sequence source anchor')
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
                                        byte_call_environment={'gas': str(GAS)}, timeout=1800)),
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
    rows = result['observations']['source']
    if {row['status'] for row in rows} != {'ok', 'revert'}:
        raise HarnessError('campaign must exercise both successful and reverting calls')
    if not any(row['deployment']['accounts'] for row in rows):
        raise HarnessError('campaign created no account')
    returned = {(call['function'], row['status'], row['data'][:10]) for call, row in zip(calls, rows)}
    for expected in (('load', 'ok', '0x00000000'), ('summary', 'ok', None), ('load', 'revert', '0x'),
                     ('load', 'revert', '0x4e487b71'), ('echo', 'ok', '0x00000000')):
        if not any(r[0] == expected[0] and r[1] == expected[1] and
                   (expected[2] is None or r[2] == expected[2]) for r in returned):
            raise HarnessError(f'campaign did not exercise {expected}')
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
    parser.add_argument('--transactions', type=int, default=96)
    parser.add_argument('--seed', type=int, default=2545)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--variant', action='append', choices=('baseline', 'renamed', 'expanded'))
    parser.add_argument('--single', action='store_true',
                        help='one unmodified-source campaign into --output; exit 1 on divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < PREFIX_TRANSACTIONS:
        parser.error(f'at least {PREFIX_TRANSACTIONS} transactions cover the deterministic prefix')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='extcodecopy-struct-decode-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    original = FIXTURE.read_text()
    template = DRIVER.read_text()
    if args.single:
        code, _ = campaign(output, original, template, args.transactions, args.seed, args.shrink_attempts)
        return code
    baseline = None
    completed = []
    for variant in args.variant or ('baseline', 'renamed', 'expanded'):
        source = stateful_extcodecopy_struct_decode_source(original, variant)
        code, report = campaign(output / variant, source, template, args.transactions, args.seed,
                                args.shrink_attempts)
        if code:
            raise SystemExit(f'code-decoding divergence in {variant}: {output / variant}')
        observable = canonical(report['observations'])
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json', {'variant': variant})
            raise SystemExit(f'code-decoding variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'variants': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'imported <address>.code and dynamic-struct abi.decode returns: '
                 'source EVM / Denote / compiled model'})
    print(f'code-decoding variants agree: {output}')


if __name__ == '__main__':
    sys.exit(main())
