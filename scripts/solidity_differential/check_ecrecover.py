"""Imported Solidity `ecrecover` builtin through source EVM, Denote and compiled model.

`EcrecoverSequence.sol` calls the global `ecrecover(hash, v, r, s)` directly, in a pure
signer check, with an explicit `uint8` conversion of `v`, with a later argument that
overwrites the storage an earlier argument reads (left-to-right evaluation), and in an
EIP-2612-style permit whose digest hashes the consumed `nonces[owner]++`. Signatures are produced
here with deterministic nonces; the campaign covers valid signatures, their high-`s`
twins (which the precompile accepts), `v` outside {27, 28} (including words whose low byte
is 27), zero and out-of-range `r` / `s`, an `r` that is no curve x-coordinate, random
words, valid, forged, replayed and expired permits. On the EVM the call reaches the real
precompile at `address(1)`; Denote answers it with `ecrecover-precompile-v1`
(`PrecompileResponderMocks`). A divergence is shrunk to a deletion-minimal sequence.
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

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/EcrecoverSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/EcrecoverSequenceModel.lean')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SPENDER = '0x' + '00' * 19 + '55'
CHAIN_ID = 31337
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "EcrecoverSequence.sol"'

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
KEYS = [1, 2, 0xC0FFEE, N - 1]


def point_add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        slope = 3 * a[0] * a[0] * pow(2 * a[1], P - 2, P) % P
    else:
        slope = (b[1] - a[1]) * pow(b[0] - a[0], P - 2, P) % P
    x = (slope * slope - a[0] - b[0]) % P
    return x, (slope * (a[0] - x) - a[1]) % P


def point_mul(k, point):
    result = None
    for bit in reversed(range(256)):
        result = point_add(result, result)
        if k >> bit & 1:
            result = point_add(result, point)
    return result


def signer(key):
    x, y = point_mul(key, G)
    return '0x' + keccak(x.to_bytes(32, 'big') + y.to_bytes(32, 'big'))[-20:].hex()


def sign(key, digest):
    """Deterministic low-`s` ECDSA signature `(v, r, s)` of a 32-byte digest."""
    z = int.from_bytes(digest, 'big')
    counter = 0
    while True:
        k = int.from_bytes(keccak(key.to_bytes(32, 'big') + digest + bytes([counter])), 'big') % N
        counter += 1
        if k == 0:
            continue
        rx, ry = point_mul(k, G)
        r = rx % N
        if r == 0 or rx >= N:
            continue
        s = pow(k, N - 2, N) * (z + r * key) % N
        if s == 0:
            continue
        parity = ry & 1
        if s > N // 2:
            s, parity = N - s, parity ^ 1
        return 27 + parity, r, s


def word(value):
    return value.to_bytes(32, 'big')


def no_curve_x():
    """The smallest x in [1, N) with no point on the curve."""
    x = 1
    while pow((x ** 3 + 7) % P, (P - 1) // 2, P) == 1:
        x += 1
    return x


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def domain_separator(contract):
    typehash = keccak(text='EIP712Domain(uint256 chainId,address verifyingContract)')
    return keccak(encode(['bytes32', 'uint256', 'address'], [typehash, CHAIN_ID, contract]))


def permit_digest(contract, owner, spender, value, nonce, deadline):
    typehash = keccak(text='Permit(address owner,address spender,uint256 value,uint256 nonce,'
                           'uint256 deadline)')
    inner = keccak(encode(['bytes32', 'address', 'address', 'uint256', 'uint256', 'uint256'],
                          [typehash, owner, spender, value, nonce, deadline]))
    return keccak(b'\x19\x01' + domain_separator(contract) + inner)


def transactions_for(count, seed, contract):
    rng = random.Random(seed)
    calls = []
    expected = {}

    def add(function, types, values, recovers=None):
        index = len(calls)
        selector = keccak(text=function)[:4].hex()
        encoded = encode(types, values)
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        calls.append({'id': str(index), 'function': function[:function.index('(')], 'args': words,
                      'sender': SENDER, 'target': contract, 'data': '0x' + selector + encoded.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})
        if recovers is not None:
            expected[str(index)] = recovers

    def recover(digest, v, r, s, recovers=None):
        add('recover(bytes32,uint8,bytes32,bytes32)', ['bytes32', 'uint8', 'bytes32', 'bytes32'],
            [digest, v, word(r), word(s)], recovers)

    zero = '0x' + '00' * 20
    bad_x = no_curve_x()
    for key in KEYS:
        owner = signer(key)
        digest = keccak(text=f'ecrecover-fixture-{key}')
        v, r, s = sign(key, digest)
        recover(digest, v, r, s, owner)
        recover(digest, 55 - v, r, N - s, owner)      # high-s twin
        recover(digest, 55 - v, r, s)                   # other parity: another key
        for wrong in (0, 1, 26, 29, 255):
            recover(digest, wrong, r, s, zero)
        recover(digest, v, 0, s, zero)
        recover(digest, v, r, 0, zero)
        recover(digest, v, N, s, zero)
        recover(digest, v, r, N, zero)
        recover(digest, v, bad_x, s, zero)
        add('verify(bytes32,uint8,bytes32,bytes32,address)',
            ['bytes32', 'uint8', 'bytes32', 'bytes32', 'address'], [digest, v, word(r), word(s), owner])
        add('verify(bytes32,uint8,bytes32,bytes32,address)',
            ['bytes32', 'uint8', 'bytes32', 'bytes32', 'address'], [digest, v, word(r), word(s), SPENDER])
        add('verify(bytes32,uint8,bytes32,bytes32,address)',
            ['bytes32', 'uint8', 'bytes32', 'bytes32', 'address'], [digest, 0, word(r), word(s), zero])
        for v_word in (v, v + 256, v + 2**255, v - 27 + 2**8 * 3):
            add('recoverWide(bytes32,uint256,bytes32,bytes32)', ['bytes32', 'uint256', 'bytes32', 'bytes32'],
                [digest, v_word, word(r), word(s)])
        # Left to right: the digest is read before the last argument overwrites it.
        add('setDigest(bytes32)', ['bytes32'], [digest])
        add('recoverOrdered(uint8,bytes32,bytes32)', ['uint8', 'bytes32', 'bytes32'], [v, word(r), word(s)])
        add('storedDigest()', [], [])
    nonces = {}
    late = 2**64
    for key in KEYS:
        owner = signer(key)
        for value in (5, 2**256 - 1):
            nonce = nonces.get(owner, 0)
            pv, pr, ps = sign(key, permit_digest(contract, owner, SPENDER, value, nonce, late))
            args = [owner, SPENDER, value, late, pv, word(pr), word(ps)]
            types = ['address', 'address', 'uint256', 'uint256', 'uint8', 'bytes32', 'bytes32']
            add('permit(address,address,uint256,uint256,uint8,bytes32,bytes32)', types, args)
            nonces[owner] = nonce + 1
            # Replay: the nonce moved on.
            add('permit(address,address,uint256,uint256,uint8,bytes32,bytes32)', types, args)
            # High-s twin of a fresh signature is accepted by ecrecover.
            nonce = nonces[owner]
            pv, pr, ps = sign(key, permit_digest(contract, owner, SPENDER, 7, nonce, late))
            add('permit(address,address,uint256,uint256,uint8,bytes32,bytes32)', types,
                [owner, SPENDER, 7, late, 55 - pv, word(pr), word(N - ps)])
            nonces[owner] = nonce + 1
        # Forged: signed by another key.
        other = KEYS[(KEYS.index(key) + 1) % len(KEYS)]
        fv, fr, fs = sign(other, permit_digest(contract, owner, SPENDER, 9, nonces[owner], late))
        add('permit(address,address,uint256,uint256,uint8,bytes32,bytes32)',
            ['address', 'address', 'uint256', 'uint256', 'uint8', 'bytes32', 'bytes32'],
            [owner, SPENDER, 9, late, fv, word(fr), word(fs)])
        # Expired deadline.
        add('permit(address,address,uint256,uint256,uint8,bytes32,bytes32)',
            ['address', 'address', 'uint256', 'uint256', 'uint8', 'bytes32', 'bytes32'],
            [owner, SPENDER, 9, 1, fv, word(fr), word(fs)])
        add('nonces(address)', ['address'], [owner])
        add('allowance(address,address)', ['address', 'address'], [owner, SPENDER])
    for getter in ('lastRecovered()', 'recoveries()', 'domainSeparator()', 'PERMIT_TYPEHASH()'):
        add(getter, [], [])
    while len(calls) < count:
        digest = rng.getrandbits(256).to_bytes(32, 'big')
        choice = rng.randrange(3)
        if choice == 0:
            key = rng.choice(KEYS)
            v, r, s = sign(key, digest)
            recover(digest, v, r, s, signer(key))
        elif choice == 1:
            # Random words: about half of the r values are curve x-coordinates.
            recover(digest, rng.choice([27, 28]), rng.randrange(1, N), rng.randrange(1, N))
        else:
            recover(digest, rng.getrandbits(8), rng.getrandbits(256), rng.getrandbits(256))
    return calls, expected


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol']['EcrecoverFixture']
    identifiers = compiled['evm']['methodIdentifiers']
    signatures = [line[len('  function '):] for line in template.splitlines()
                  if line.startswith('  function ')]
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
    contract = address(0)
    calls, expected = transactions_for(transactions, seed, contract)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'ecrecover-precompile-v1', 'gas': '1000000'}
    adapters = {
        'source': EVM(directory / 'A', ['0x' + compiled['evm']['bytecode']['object']], []),
        'model': Denote(directory / 'B', driver, contract, [], byte_call_environment=environment),
        'compiled': EVM(directory / 'C', ['0x' + next(iter(generated.values()))['evm']['bytecode']['object']],
                        [])}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    rows = {row['id']: row for row in result['observations']['source']}
    # The harness's own signatures must recover on the real precompile, or the campaign is vacuous.
    for ident, recovered in expected.items():
        want = '0x' + encode(['address'], [recovered]).hex()
        if rows[ident]['status'] != 'ok' or rows[ident]['data'] != want:
            raise HarnessError(f'transaction {ident}: expected {recovered} from the EVM precompile')
    permits = [row for row in result['observations']['source']
               if calls[int(row['id'])]['function'] == 'permit']
    if {row['status'] for row in permits} != {'ok', 'revert'}:
        raise HarnessError('campaign must exercise accepted and rejected permits')
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=200)
    parser.add_argument('--seed', type=int, default=2698)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='ecrecover-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts)
    if code:
        raise SystemExit(f'ecrecover divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported Solidity ecrecover builtin: '
                                    'source EVM / Denote / compiled model'})
    print(f'ecrecover A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
