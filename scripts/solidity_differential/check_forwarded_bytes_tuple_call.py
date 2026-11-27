"""Three-route Anvil differential campaign for typed external interface `CALL`
returning `(Scalar, bytes memory)` assigned in a forwarded `(Scalar, bytes memory)`
tuple call tree (`ForwardedBytesTupleCall.sol`, Refs #2803, Refs #2842).

Compares across `viaIR` and `legacy` (and solc `0.8.34` + `0.8.38`):
  Route A: solc bytecode on Anvil
  Route B: Verity Lean Denote model (`ForwardedBytesTupleCallModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Covers:
- `(true, empty)`
- `(true, 5 bytes with dirty trailing padding bytes in returndata)`
- `(true, 65 bytes)` (multi-word non-32-aligned payload)
- `(true, 5 bytes)` with extra trailing bytes past the dynamic tail
- `(false, payload)` both reverting (`shouldRevert=true` -> `ModuleTransactionFailed()`)
  and returning (`shouldRevert=false` -> no `persistCount` increment)
- callee revert passthrough (`0xdeadbeef`)
- EOA / codeless target revert (empty `0x`)
- malformed returndata: short (`63` bytes), dirty `bool = 2`, dirty `enum = 2`,
  bad offset (`2^64`, `offset + 32 > returndatasize`, `2^256 - 1` wraparound),
  truncated tail (`offset + 32 + len > returndatasize`), huge length (`2^64` -> `Panic(0x41)`)
- re-entrant responder mutating caller storage (`pingCallback()`) during `exec` and `execUnlocked`
- re-entrant responder tripping `nonReentrant` (`guardedPing()`) during `exec`
- `--negative-control`: disables callback on the Denote route only and asserts divergence.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .anvil import SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes

SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
EMPTY = '0x' + '00' * 19 + '77'
TO_ADDR = '0x' + '00' * 19 + '42'

FUNCTIONS = [
    'setTarget(address)',
    'pingCallback()',
    'guardedPing()',
    'state()',
    'exec(address,uint256,bytes,uint8,bool)',
    'execUnlocked(address,uint256,bytes,uint8,bool)',
    'execEnum(uint256)',
]


def selector_int(sig: str) -> int:
    return int.from_bytes(keccak(text=sig)[:4], 'big')


def address(nonce: int) -> str:
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def bytes_to_6_words(raw: bytes) -> tuple[int, int, int, int, int, int]:
    assert len(raw) <= 192
    padded = raw.ljust(192, b'\x00')
    return tuple(int.from_bytes(padded[i:i + 32], 'big') for i in range(0, 192, 32))


def abi_tuple_raw(scalar: int, offset: int, length: int, payload: bytes, extra: bytes = b'') -> bytes:
    head = scalar.to_bytes(32, 'big') + offset.to_bytes(32, 'big')
    tail = length.to_bytes(32, 'big') + payload + extra
    return head + tail


def build_responders():
    ping_sel = selector_int('pingCallback()')
    guarded_sel = selector_int('guardedPing()')

    # (w0..w5, retLen, flags, cbSelector, cbArg0)
    # flags: bit 0 = revert, bit 1 = callback, bit 2 = pass cbArg0
    specs = []

    def add_spec(raw: bytes, *, ret_len: int | None = None, flags: int = 0,
                 cb_sel: int = 0, cb_arg0: int = 0):
        w0, w1, w2, w3, w4, w5 = bytes_to_6_words(raw)
        specs.append((w0, w1, w2, w3, w4, w5, len(raw) if ret_len is None else ret_len,
                      flags, cb_sel, cb_arg0))
        return len(specs) - 1

    # 0: (true, empty)
    idx_true_empty = add_spec(abi_tuple_raw(1, 64, 0, b''))
    # 1: (true, 5 bytes with dirty trailing bytes in returndata word)
    dirty_5 = b'\x11\x22\x33\x44\x55' + b'\xff' * 27
    idx_true_5_dirty = add_spec(abi_tuple_raw(1, 64, 5, dirty_5))
    # 2: (true, 65 bytes) — 3 words of data (bytes 65..95 dirty)
    payload_65 = bytes((i * 7 + 3) % 256 for i in range(65)) + b'\xaa' * 31
    idx_true_65 = add_spec(abi_tuple_raw(1, 64, 65, payload_65))
    # 3: (true, 5 bytes) with extra trailing bytes past dynamic tail
    idx_true_extra = add_spec(abi_tuple_raw(1, 64, 5, dirty_5, extra=b'\xde\xad\xbe\xef' * 8))
    # 4: (false, 4 bytes payload)
    idx_false_payload = add_spec(abi_tuple_raw(0, 64, 4, b'\xca\xfe\xba\xbe' + b'\x00' * 28))
    # 5: callee reverts with 0xdeadbeef
    idx_revert = add_spec(b'\xde\xad\xbe\xef', ret_len=4, flags=1)
    # 6: malformed — short returndata (63 bytes)
    idx_short_63 = add_spec(abi_tuple_raw(1, 64, 0, b''), ret_len=63)
    # 7: malformed — dirty bool = 2
    idx_dirty_bool = add_spec(abi_tuple_raw(2, 64, 0, b''))
    # 8: malformed — bad offset > 2^64 - 1
    idx_bad_off_hi = add_spec(abi_tuple_raw(1, 1 << 64, 0, b''))
    # 9: malformed — bad offset wraparound (2^256 - 1)
    idx_bad_off_wrap = add_spec(abi_tuple_raw(1, (1 << 256) - 1, 0, b''))
    # 10: malformed — offset + 32 > returndatasize (offset=65, rdSize=96 -> 97 > 96)
    idx_bad_off_oob = add_spec(abi_tuple_raw(1, 65, 0, b''), ret_len=96)
    # 11: malformed — truncated bytes tail (len=10, rdSize=100 -> 64+32+10=106 > 100)
    idx_trunc_tail = add_spec(abi_tuple_raw(1, 64, 10, b'\x01' * 4), ret_len=100)
    # 12: malformed — huge length 2^64 -> Panic(0x41)
    idx_huge_len = add_spec(abi_tuple_raw(1, 64, 1 << 64, b''))
    # 13: re-entrant responder calling pingCallback() (mutates caller storage), then returns (true, 5 bytes)
    idx_reent_mutate = add_spec(abi_tuple_raw(1, 64, 5, dirty_5), flags=2, cb_sel=ping_sel)
    # 14: re-entrant responder calling guardedPing() (trips nonReentrant during exec!)
    idx_reent_lock = add_spec(abi_tuple_raw(1, 64, 0, b''), flags=2, cb_sel=guarded_sel)
    # 15: enum (Operation.DelegateCall = 1, 3 bytes)
    idx_enum_ok = add_spec(abi_tuple_raw(1, 64, 3, b'\xaa\xbb\xcc' + b'\xee' * 29))
    # 16: malformed enum = 2 (out of range -> empty revert)
    idx_enum_bad = add_spec(abi_tuple_raw(2, 64, 0, b''))

    indices = {
        'true_empty': idx_true_empty,
        'true_5_dirty': idx_true_5_dirty,
        'true_65': idx_true_65,
        'true_extra': idx_true_extra,
        'false_payload': idx_false_payload,
        'revert': idx_revert,
        'short_63': idx_short_63,
        'dirty_bool': idx_dirty_bool,
        'bad_off_hi': idx_bad_off_hi,
        'bad_off_wrap': idx_bad_off_wrap,
        'bad_off_oob': idx_bad_off_oob,
        'trunc_tail': idx_trunc_tail,
        'huge_len': idx_huge_len,
        'reent_mutate': idx_reent_mutate,
        'reent_lock': idx_reent_lock,
        'enum_ok': idx_enum_ok,
        'enum_bad': idx_enum_bad,
    }
    return specs, indices


def run_mode(*, root: Path, output: Path, solc_path: Path, via_ir: bool, negative_control: bool):
    fixture = root / 'Contracts/SolidityImportSmoke/ForwardedBytesTupleCall.sol'
    responder = root / 'Contracts/SolidityImportSmoke/ForwardedBytesTupleResponder.sol'
    driver = root / (
        'Contracts/SolidityImportSmoke/ForwardedBytesTupleCallModel.lean'
        if via_ir
        else 'Contracts/SolidityImportSmoke/ForwardedBytesTupleCallLegacyModel.lean'
    )
    output.mkdir(parents=True, exist_ok=True)

    settings = {
        'evmVersion': 'osaka',
        'viaIR': via_ir,
        'optimizer': {'enabled': True, 'runs': 466},
        'metadata': {'bytecodeHash': 'none'},
    }
    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                fixture.name: {'content': fixture.read_text()},
                responder.name: {'content': responder.read_text()},
            },
            'settings': {
                **settings,
                'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
            },
        },
        fixture.parent,
        output / 'solc',
        solc=solc_path,
    )['contracts']
    caller_evm = compiled[fixture.name]['ForwardedBytesTupleCall']['evm']
    identifiers = caller_evm['methodIdentifiers']
    selectors = [int(identifiers[sig], 16) for sig in FUNCTIONS]
    write_json(output / 'selectors.json', selectors)

    identity = ImplementationIdentity(driver, extra_inputs=[fixture, responder])
    command(
        ['lake', 'env', 'lean', '--run', driver, 'compile',
         output / 'selectors.json', output / 'model.yul'],
        timeout=900,
        log=output / 'compile-model.log',
    )
    identity.verify()

    compiled_yul = solc_compile(
        {
            'language': 'Yul',
            'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
            'settings': {
                'evmVersion': 'osaka',
                'optimizer': {'enabled': True, 'runs': 466},
                'outputSelection': {'*': {'*': ['evm.bytecode.object']}},
            },
        },
        fixture.parent,
        output / 'compiled',
        solc=solc_path,
    )
    objects = list(compiled_yul['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled Yul object')

    caller_a = '0x' + caller_evm['bytecode']['object']
    caller_c = '0x' + objects[0]['evm']['bytecode']['object']
    mock_bin = compiled[responder.name]['ForwardedBytesTupleResponder']['evm']['bytecode']['object']

    specs, idx = build_responders()
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(specs))]

    responder_bytecodes = [
        '0x' + mock_bin + encode(['uint256'] * 10, list(spec)).hex()
        for spec in specs
    ]
    initial = [
        (acct, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for acct, spec in zip(accounts, specs, strict=True)
        for slot, val in enumerate(spec)
    ]

    if negative_control:
        # Disable callbacks (clear bit 1 of flags slot 7) ONLY on the Denote route.
        denote_initial = [
            (acct, slot_hex,
             '0x' + (int(val_hex, 16) & ~2).to_bytes(32, 'big').hex()
             if slot_hex == '0x' + (7).to_bytes(32, 'big').hex() else val_hex)
            for (acct, slot_hex, val_hex) in initial
        ]
    else:
        denote_initial = initial

    calls = []
    first_block = len(accounts) + 2

    def add(sig: str, types: list[str], values: list):
        n = len(calls)
        sel = keccak(text=sig)[:4].hex()
        name = sig[:sig.index('(')]
        enc = encode(types, values)
        words = [int.from_bytes(enc[i:i + 32], 'big') for i in range(0, len(enc), 32)]
        calls.append({
            'id': str(n),
            'function': name,
            'args': words,
            'sender': SENDER,
            'target': caller,
            'data': '0x' + sel + enc.hex(),
            'value': '0x0',
            'timestamp': 1000000100 + n,
            'blockNumber': first_block + n,
        })

    def exec_case(target_addr: str, *, payload: bytes = b'\xaa\xbb\xcc\xdd\xee',
                  op: int = 1, should_revert: bool = False, unlocked: bool = False):
        add('setTarget(address)', ['address'], [target_addr])
        fn = 'execUnlocked(address,uint256,bytes,uint8,bool)' if unlocked else 'exec(address,uint256,bytes,uint8,bool)'
        add(fn, ['address', 'uint256', 'bytes', 'uint8', 'bool'],
            [TO_ADDR, 123, payload, op, should_revert])
        add('state()', [], [])

    if negative_control:
        exec_case(accounts[idx['reent_mutate']], unlocked=True)
    else:
        # Valid return shapes
        exec_case(accounts[idx['true_empty']], payload=b'', op=0)
        exec_case(accounts[idx['true_5_dirty']], payload=b'\x01\x02\x03\x04\x05', op=1)
        exec_case(accounts[idx['true_65']], payload=bytes(range(40)), op=0)
        exec_case(accounts[idx['true_extra']], payload=b'\x99', op=1)
        # (false, payload): both returning and reverting
        exec_case(accounts[idx['false_payload']], should_revert=False)
        exec_case(accounts[idx['false_payload']], should_revert=True)
        # Callee revert passthrough & EOA / codeless target revert
        exec_case(accounts[idx['revert']])
        exec_case(EMPTY)
        exec_case(SENDER)
        # Malformed returndata cases
        exec_case(accounts[idx['short_63']])
        exec_case(accounts[idx['dirty_bool']])
        exec_case(accounts[idx['bad_off_hi']])
        exec_case(accounts[idx['bad_off_wrap']])
        exec_case(accounts[idx['bad_off_oob']])
        exec_case(accounts[idx['trunc_tail']])
        exec_case(accounts[idx['huge_len']])
        # Re-entrant responders: mutating caller storage & tripping nonReentrant
        exec_case(accounts[idx['reent_mutate']], unlocked=True)
        exec_case(accounts[idx['reent_mutate']], unlocked=False)
        exec_case(accounts[idx['reent_lock']], unlocked=False)
        add('guardedPing()', [], [])
        add('state()', [], [])
        # Enum scalar return: valid and out-of-range
        add('setTarget(address)', ['address'], [accounts[idx['enum_ok']]])
        add('execEnum(uint256)', ['uint256'], [7])
        add('state()', [], [])
        add('setTarget(address)', ['address'], [accounts[idx['enum_bad']]])
        add('execEnum(uint256)', ['uint256'], [8])
        add('state()', [], [])

    environment = {
        'program': 'forwarded-bytes-tuple-v1',
        'gas': '2000000',
        'accounts': [str(int(a, 16)) for a in accounts],
        'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))],
    }
    adapters = {
        'source': EVMAdapter(output / 'A', [caller_a, *responder_bytecodes], initial),
        'model': DenoteAdapter(output / 'B', driver, caller, denote_initial, identity=identity,
                               byte_call_environment=environment),
        'compiled': EVMAdapter(output / 'C', [caller_c, *responder_bytecodes], initial),
    }

    result = replay_three_routes(calls, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': calls, **result})

    if negative_control:
        if not result['divergences']:
            raise HarnessError('negative control failed: Denote with callback disabled still agreed with EVM!')
        print(f'negative control PASS (diverged as expected) [solc={solc_path.name} viaIR={via_ir}]')
        return
    if result['divergences']:
        raise HarnessError(f'A/B/C divergence [solc={solc_path.name} viaIR={via_ir}]: {output / "campaign.json"}')
    statuses = {row['status'] for row in result['observations']['source']}
    if statuses != {'ok', 'revert'}:
        raise HarnessError('forwarded bytes tuple campaign must exercise both ok and revert paths')
    print(f'Anvil 3-route A/B/C PASS: {len(calls)}/{len(calls)} transactions agree bit-for-bit '
          f'[solc={solc_path.name} viaIR={via_ir}]')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--solc', type=Path, default=None)
    parser.add_argument('--legacy', action='store_true')
    parser.add_argument('--all-matrix', action='store_true',
                        help='Run solc 0.8.34 + 0.8.38 across viaIR and legacy')
    parser.add_argument('--negative-control', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='forwarded-bytes-tuple-', dir=root / '.lake')).resolve()

    if args.all_matrix:
        solc_34 = root / '.lake/solidity-import/solc-0.8.34'
        solc_38 = root / '.lake/solidity-import/solc-0.8.38'
        for label, solc_bin, via_ir in [
            ('0.8.34-viaIR', solc_34, True),
            ('0.8.34-legacy', solc_34, False),
            ('0.8.38-viaIR', solc_38, True),
            ('0.8.38-legacy', solc_38, False),
        ]:
            run_mode(root=root, output=output / label, solc_path=solc_bin,
                     via_ir=via_ir, negative_control=False)
        if args.negative_control:
            run_mode(root=root, output=output / 'negative-control', solc_path=solc_34,
                     via_ir=True, negative_control=True)
    else:
        solc_bin = args.solc or SOLC
        run_mode(root=root, output=output, solc_path=solc_bin,
                 via_ir=not args.legacy, negative_control=args.negative_control)


if __name__ == '__main__':
    main()
