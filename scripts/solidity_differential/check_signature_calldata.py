"""Imported OpenZeppelin calldata signature split through source EVM, Denote and compiled model.

`SignatureCalldataSequence.sol` quotes OpenZeppelin 5.7's `ECDSA.tryRecoverCalldata` as is: the
65-byte `bytes calldata` signature is split with Yul `calldataload(signature.offset)`,
`calldataload(add(signature.offset, 0x20))` and `byte(0, calldataload(add(signature.offset, 0x40)))`,
then `tryRecover(hash, v, r, s)` rejects high `s` and calls the `ecrecover` precompile (#2920).
Calldata is built byte by byte here, so the campaign covers valid signatures of four keys, their
high-`s` twins, `v` outside {27, 28}, zero and off-curve `r` / `s` (zero-address recovery), the
lengths 0, 1, 64, 66 and 130, dirty bytes after the 65th, non-canonical head offsets, a signature
whose 65th byte is the last calldata byte (the last `calldataload` reads 31 zero-padded bytes),
truncated calldata and out-of-range offsets (ABI reverts), and a nonce-consuming signed approval
(valid, replayed, forged, high-`s`, wrong length). A divergence is shrunk to a deletion-minimal
sequence.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .check_ecrecover import KEYS, N, address, no_curve_x, sign, signer
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/SignatureCalldataSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/SignatureCalldataSequenceModel.lean')
CONTRACT = 'SignatureCalldataFixture'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SPENDER = '0x' + '00' * 19 + '55'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "SignatureCalldataSequence.sol"'

RECOVER = 'recover(bytes32,bytes)'
TRY_RECOVER = 'tryRecover(bytes32,bytes)'
APPROVE = 'approveBySig(address,address,uint256,bytes)'


def selector_of(text):
    return keccak(text=text)[:4]


ERR_SIGNATURE = '0x' + selector_of('ECDSAInvalidSignature()').hex()
ERR_LENGTH = '0x' + selector_of('ECDSAInvalidSignatureLength(uint256)').hex()
ERR_S = '0x' + selector_of('ECDSAInvalidSignatureS(bytes32)').hex()


def word(value):
    return value.to_bytes(32, 'big')


def signature_bytes(v, r, s):
    return word(r) + word(s) + bytes([v])


def calldata(function, head, payload, offset=None, length=None, tail_gap=b'', padding=None,
             truncate=None):
    """`selector ++ head ++ offset word`, then the bytes tail at `4 + offset`.

    `head` are the static words before the `bytes` argument (always its last parameter here).
    `offset` defaults to the canonical one (one above 1024 points past the tail, which stays
    canonical); `tail_gap` sits between the head and the tail;
    `padding` replaces the zero padding after the payload; `truncate` cuts calldata (after the
    selector) to that many bytes. The result is extended with zeros to whole words only when it
    is not truncated, as the Denote route needs word-aligned calldata.
    """
    head_bytes = b''.join(head)
    canonical = len(head_bytes) + 32 + len(tail_gap)
    offset = canonical if offset is None else offset
    length = len(payload) if length is None else length
    body = bytearray(head_bytes + word(offset))
    # An offset past any calldata this builds keeps the tail at the canonical place.
    start = offset if offset <= 1024 else canonical
    if len(body) < start:
        body += tail_gap[:start - len(body)]
        body += b'\x00' * (start - len(body))
    body = body[:start]
    body += word(length) + payload
    pad = (-len(body)) % 32
    body += (padding if padding is not None else b'\x00' * pad)[:pad]
    if truncate is not None:
        body = body[:truncate]
    body += b'\x00' * ((-len(body)) % 32)
    return selector_of(function) + bytes(body)


def transactions_for(count, seed, contract):
    rng = random.Random(seed)
    calls = []
    expected = {}

    def add(function, data, expect=None):
        index = len(calls)
        if (len(data) - 4) % 32:
            raise HarnessError('calldata after the selector must be word-aligned')
        words = [int.from_bytes(data[i:i + 32], 'big') for i in range(4, len(data), 32)]
        calls.append({'id': str(index), 'function': function[:function.index('(')], 'args': words,
                      'sender': SENDER, 'target': contract, 'data': '0x' + data.hex(),
                      'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})
        if expect is not None:
            expected[str(index)] = expect

    def recover(digest, payload, expect=None, **layout):
        add(RECOVER, calldata(RECOVER, [digest], payload, **layout), expect)

    def try_recover(digest, payload, **layout):
        add(TRY_RECOVER, calldata(TRY_RECOVER, [digest], payload, **layout))

    bad_x = no_curve_x()
    for key in KEYS:
        owner = signer(key)
        digest = keccak(text=f'signature-calldata-{key}')
        v, r, s = sign(key, digest)
        good = signature_bytes(v, r, s)
        recover(digest, good, ('ok', owner))
        try_recover(digest, good)
        # High-s twin: ecrecover accepts it, OpenZeppelin rejects it.
        recover(digest, signature_bytes(55 - v, r, N - s), ('revert', ERR_S))
        try_recover(digest, signature_bytes(55 - v, r, N - s))
        # The other parity recovers another address.
        recover(digest, signature_bytes(55 - v, r, s))
        for wrong in (0, 1, 26, 29, 255):
            recover(digest, signature_bytes(wrong, r, s), ('revert', ERR_SIGNATURE))
        for zr, zs in ((0, s), (r, 0), (bad_x, s), (N, s)):
            recover(digest, signature_bytes(v, zr, zs), ('revert', ERR_SIGNATURE))
        try_recover(digest, signature_bytes(v, bad_x, s))
        for size in (0, 1, 64, 66, 130):
            payload = (good * 3)[:size]
            recover(digest, payload, ('revert', ERR_LENGTH))
            try_recover(digest, payload)
        # Dirty bytes after the 65th: `byte(0, ...)` keeps only the first.
        recover(digest, good, ('ok', owner), padding=bytes([0xa5] * 31))
        # A non-canonical offset with junk between the head and the tail.
        recover(digest, good, ('ok', owner), tail_gap=bytes(range(1, 40)))
        # The 65th byte is the last calldata byte: head 2 words, offset 95, 4 + 95 + 32 + 65 = 196.
        recover(digest, good, ('ok', owner), offset=95)
        try_recover(digest, good, offset=95)
        recover(digest, signature_bytes(55 - v, r, N - s), ('revert', ERR_S), offset=95)
        # The length word claims one byte more than calldata holds: ABI revert.
        recover(digest, good, ('revert', '0x'), offset=95, length=66)
        recover(digest, good[:64], ('revert', '0x'), offset=96, length=65)
        recover(digest, good[:64], ('revert', '0x'), length=65)
        # Offset past calldata, offset at or above 2^64, truncated head.
        recover(digest, good, ('revert', '0x'), offset=2**16)
        recover(digest, good, ('revert', '0x'), offset=2**64)
        recover(digest, good, ('revert', '0x'), truncate=32)
    nonces = {}
    for key in KEYS:
        owner = signer(key)
        for value in (5, 2**256 - 1):
            nonce = nonces.get(owner, 0)
            digest = keccak(encode(['address', 'address', 'address', 'uint256', 'uint256'],
                                   [contract, owner, SPENDER, value, nonce]))
            pv, pr, ps = sign(key, digest)
            head = [encode(['address'], [owner]), encode(['address'], [SPENDER]), word(value)]
            sig = signature_bytes(pv, pr, ps)
            add(APPROVE, calldata(APPROVE, head, sig), ('ok', '0x'))
            nonces[owner] = nonce + 1
            # Replay: the nonce moved on, so another address is recovered.
            add(APPROVE, calldata(APPROVE, head, sig))
            # High-s twin of the fresh nonce's signature.
            nonce = nonces[owner]
            digest = keccak(encode(['address', 'address', 'address', 'uint256', 'uint256'],
                                   [contract, owner, SPENDER, value, nonce]))
            pv, pr, ps = sign(key, digest)
            add(APPROVE, calldata(APPROVE, head, signature_bytes(55 - pv, pr, N - ps)),
                ('revert', ERR_S))
            # Wrong length, then the signature ending at the end of calldata (offset 159:
            # 4 + 159 + 32 + 65 = 260 = 4 + 8 * 32).
            add(APPROVE, calldata(APPROVE, head, signature_bytes(pv, pr, ps)[:64]),
                ('revert', ERR_LENGTH))
            add(APPROVE, calldata(APPROVE, head, signature_bytes(pv, pr, ps), offset=159),
                ('ok', '0x'))
            nonces[owner] = nonce + 1
        # Forged: signed by another key.
        other = KEYS[(KEYS.index(key) + 1) % len(KEYS)]
        digest = keccak(encode(['address', 'address', 'address', 'uint256', 'uint256'],
                               [contract, owner, SPENDER, 9, nonces[owner]]))
        fv, fr, fs = sign(other, digest)
        head = [encode(['address'], [owner]), encode(['address'], [SPENDER]), word(9)]
        add(APPROVE, calldata(APPROVE, head, signature_bytes(fv, fr, fs)))
        add('nonces(address)', selector_of('nonces(address)') + encode(['address'], [owner]))
        add('allowance(address,address)', selector_of('allowance(address,address)') +
            encode(['address', 'address'], [owner, SPENDER]))
    while len(calls) < count:
        digest = rng.getrandbits(256).to_bytes(32, 'big')
        choice = rng.randrange(4)
        if choice == 0:
            key = rng.choice(KEYS)
            v, r, s = sign(key, digest)
            recover(digest, signature_bytes(v, r, s), ('ok', signer(key)))
        elif choice == 1:
            try_recover(digest, signature_bytes(rng.choice([27, 28]), rng.randrange(1, N),
                                                rng.randrange(1, N)))
        elif choice == 2:
            recover(digest, rng.getrandbits(8 * 65).to_bytes(65, 'big'))
        else:
            size = rng.choice([63, 65, 67, 96])
            recover(digest, rng.getrandbits(8 * size).to_bytes(size, 'big'),
                    offset=rng.choice([64, 65, 95, 127]))
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
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol'][CONTRACT]
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
    # The campaign is vacuous unless the source EVM shows the intended outcome of each case:
    # recovered signers, each OpenZeppelin error and the decoder's empty reverts.
    rows = {row['id']: row for row in result['observations']['source']}
    for ident, (status, want) in expected.items():
        row = rows[ident]
        if status == 'ok' and want != '0x':
            want = '0x' + encode(['address'], [want]).hex()
            ok = row['status'] == 'ok' and row['data'] == want
        elif status == 'ok':
            ok = row['status'] == 'ok'
        elif want == '0x':
            ok = row['status'] == 'revert' and row['data'] == '0x'
        else:
            ok = row['status'] == 'revert' and row['data'].startswith(want)
        if not ok:
            raise HarnessError(f'transaction {ident}: expected {status} {want} from the EVM, got {row}')
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=200)
    parser.add_argument('--seed', type=int, default=2920)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='signature-calldata-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts)
    if code:
        raise SystemExit(f'signature calldata divergence: {output}')
    write_json(output / 'summary.json', {'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'scope': 'imported OpenZeppelin ECDSA.tryRecoverCalldata: '
                                    'source EVM / Denote / compiled model'})
    print(f'signature calldata A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
