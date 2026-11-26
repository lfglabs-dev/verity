"""Stateful calls in binary comparisons and storage-struct mapping RHS writes (#2976):
3-route A/B/C differential validation (source EVM, Denote, compiled model) across via-IR
and legacy pipelines, including reverting callees, re-entrant callbacks, side-effecting
key helpers, and 4 runtime semantic mutants (swap order, drop hoist on each shape).
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

from .engine import SOLC, HarnessError, command, run_bounded, solc_compile, write_json
from .mutations import release, snapshot
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/StatefulComparisonStructMapRhs.sol')
DRIVER_IR = Path('Contracts/SolidityImportSmoke/StatefulComparisonStructMapRhsSequenceModel.lean')
DRIVER_LEGACY = Path(
    'Contracts/SolidityImportSmoke/StatefulComparisonStructMapRhsLegacySequenceModel.lean')
RESPONDER = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol')
HOOK = Path('Contracts/SolidityImportSmoke/ReentrantCallbackHook.sol')
CONTRACT = 'StatefulComparisonStructMapRhs'
LIBRARIES = ('LinkedConfigLib',)
ANCHOR = 'from "Contracts/SolidityImportSmoke"\n  entry "StatefulComparisonStructMapRhs.sol"'

SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
EMPTY = '0x' + '00' * 19 + '77'
MATCH_ADDR = '0x' + '11' * 20
OTHER_ADDR = '0x' + '22' * 20
T_INIT = '0x' + 'aa' * 20
T_NEW = '0x' + 'bb' * 20
T_ALT = '0x' + 'cc' * 20
B_INIT = b'\x01' * 32
B_NEW = b'\x02' * 32
B_ALT = b'\x03' * 32

REVERT_AFTER = 1
NO_CALLBACK = 2

PANIC_ASSERT = '0x4e487b71' + (0x01).to_bytes(32, 'big').hex()
PANIC_UNDERFLOW = '0x4e487b71' + (0x11).to_bytes(32, 'big').hex()
PANIC_DIV_ZERO = '0x4e487b71' + (0x12).to_bytes(32, 'big').hex()

RESPONDERS = [
    (int(MATCH_ADDR, 16), False, 32),   # 0: valid matching address
    (int(OTHER_ADDR, 16), False, 32),   # 1: valid mismatching address (assert -> Panic 0x01)
    (0, False, 32),                     # 2: zero address
    (1 << 160, False, 32),              # 3: dirty upper bit in address word -> empty revert
    (int(MATCH_ADDR, 16), False, 16),   # 4: short 16-byte return -> empty revert
    (0xdeadbeef, True, 68),             # 5: multi-word custom revert payload
    (0, True, 0),                       # 6: empty revert
]

IMPORT_FILE = 'Compiler/SolidityImport/Import.lean'
MUTANTS = {
    'import-stateful-comparison-swap-order': (
        IMPORT_FILE,
        '  if hasStatefulComparison then\n    if env.viaIR then\n',
        '  if hasStatefulComparison then\n    if !env.viaIR then\n',
    ),
    'import-stateful-comparison-drop-hoist': (
        IMPORT_FILE,
        '    if env.viaIR then\n      let a ← captureAssignedValue left\n',
        '    if env.viaIR then\n      let a := left\n',
    ),
    'import-struct-map-rhs-swap-order': (
        IMPORT_FILE,
        'return ← writeStructMappingElement (value.pre ++ pre) path mapInfo key value.expr deleting target',
        'return ← writeStructMappingElement (pre ++ value.pre) path mapInfo key value.expr deleting target',
    ),
    'import-struct-map-rhs-drop-hoist': (
        IMPORT_FILE,
        '      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do\n'
        '        let right ← mField expression "rightHandSide"\n'
        '        validateStoredEnumValue target right (← atom (← lowerConverted (← mType target) right))\n'
        '      if !pre.isEmpty && !deleting then\n'
        '        let right ← mField expression "rightHandSide"\n'
        '        if assignmentIn right || (assignmentIn target && statefulCallIn right (← get)) then\n'
        '          failAt target "struct mapping write key prelude with stateful RHS is unsupported"\n'
        '      let value ← if deleting then pure value else captureAssignedValue value',
        '      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do\n'
        '        let right ← mField expression "rightHandSide"\n'
        '        validateStoredEnumValue target right (← lowerConverted (← mType target) right)\n'
        '      if !pre.isEmpty && !deleting then\n'
        '        let right ← mField expression "rightHandSide"\n'
        '        if assignmentIn right || (assignmentIn target && statefulCallIn right (← get)) then\n'
        '          failAt target "struct mapping write key prelude with stateful RHS is unsupported"',
    ),
}


def _eth_deps():
    from eth_abi import encode
    from eth_utils import keccak
    import rlp
    from .anvil import SequenceAdapter as EVM
    from .denote import SequenceAdapter as Denote
    return encode, keccak, rlp, EVM, Denote


def address(nonce: int) -> str:
    _, keccak, rlp, _, _ = _eth_deps()
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def selector_int(signature: str) -> int:
    _, keccak, _, _, _ = _eth_deps()
    return int.from_bytes(keccak(text=signature)[:4], 'big')


def reenter_mutate_sel() -> int:
    return selector_int('reenterMutate(bytes32,address,uint256)')


def roots(template: str) -> list[str]:
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


def make_call(calls: list[dict], caller: str, first_block: int, function: str,
              types: list[str], values: list) -> None:
    encode, keccak, _, _, _ = _eth_deps()
    index = len(calls)
    encoded = encode(types, values)
    words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
    calls.append({
        'id': str(index),
        'function': function[:function.index('(')],
        'args': words,
        'sender': SENDER,
        'target': caller,
        'data': '0x' + keccak(text=function)[:4].hex() + encoded.hex(),
        'value': '0x0',
        'timestamp': 1000000100 + index,
        'blockNumber': first_block + index,
    })


def responder_plan(count: int, seed: int, caller: str, responders: list[str]) -> list[dict]:
    match_r, mismatch_r, zero_r, dirty_r, short_r, rev_custom_r, rev_empty_r = responders
    targets = [*responders, EMPTY, SENDER]
    rng = random.Random(seed)
    calls: list[dict] = []
    first_block = len(LIBRARIES) + len(responders) + 2
    sel = b'\x12\x34\x56\x78'

    def add(fn, tys, vals):
        make_call(calls, caller, first_block, fn, tys, vals)

    # Pinned deterministic prefix (tx 0..21) for exact semantic assertions & mutant witnesses.
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [match_r, b'\xde\xad', MATCH_ADDR])                              # tx 0: ok
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [mismatch_r, b'\xde\xad', MATCH_ADDR])                           # tx 1: Panic(0x01)
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [rev_custom_r, b'\xde\xad', MATCH_ADDR])                         # tx 2: custom revert
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [dirty_r, b'', MATCH_ADDR])                                      # tx 3: dirty addr revert
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [short_r, b'', MATCH_ADDR])                                      # tx 4: short return revert
    add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
        [EMPTY, b'', MATCH_ADDR])                                        # tx 5: no-code revert
    for mode in range(5):                                                # tx 6..10: modes 0..4
        add('compareCallAndState(address,uint256,uint256,address)',
            ['address', 'uint256', 'uint256', 'address'], [match_r, mode, 7, MATCH_ADDR])
    # tx 11..12: competing panics (100 / 0 vs reverting external call) in both operand orders.
    add('compareCallAndState(address,uint256,uint256,address)',
        ['address', 'uint256', 'uint256', 'address'], [rev_custom_r, 5, 0, MATCH_ADDR])
    add('compareCallAndState(address,uint256,uint256,address)',
        ['address', 'uint256', 'uint256', 'address'], [rev_custom_r, 6, 0, MATCH_ADDR])
    # tx 13: linked external library call in >= comparison.
    add('compareCallAndState(address,uint256,uint256,address)',
        ['address', 'uint256', 'uint256', 'address'], [match_r, 7, 11, MATCH_ADDR])
    # tx 14..15: Shape (b) direct key & computed key + linked library call.
    add('setDirectKeyInternal(address,bytes32,bytes32,bytes)',
        ['address', 'bytes32', 'bytes32', 'bytes'], [match_r, B_INIT, b'\xaa' * 32, b'\x01\x02'])
    add('setComputedKeyLinked(address,bytes32,address,bytes4,uint256)',
        ['address', 'bytes32', 'address', 'bytes4', 'uint256'],
        [match_r, B_INIT, T_INIT, sel, 42])
    # tx 16..21: Shape (b) side-effecting key helpers, competing panics, 2D map, and RHS capture.
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [match_r, 0, B_INIT, T_INIT, sel, 9])                            # tx 16: ok, order observable
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [rev_custom_r, 0, B_INIT, T_INIT, sel, 9])                       # tx 17: RHS reverts first
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [rev_custom_r, 1, B_INIT, T_INIT, sel, 0])                       # tx 18: RHS revert beats 0x12/0x11
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [match_r, 1, B_INIT, T_INIT, sel, 0])                            # tx 19: outer 0x12 beats inner 0x11
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [match_r, 2, B_INIT, T_INIT, sel, 3])                            # tx 20: 2D nested struct map
    add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
        ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
        [match_r, 3, B_NEW, T_NEW, sel, 5])                              # tx 21: RHS `stored` captured before outer adds 100

    while len(calls) < count:
        target = rng.choice(targets)
        choice = rng.randrange(5)
        bkey = rng.choice([B_INIT, B_NEW, B_ALT])
        taddr = rng.choice([MATCH_ADDR, OTHER_ADDR, T_INIT, T_NEW])
        rsel = rng.getrandbits(32).to_bytes(4, 'big')
        if choice == 0:
            add('assertDeployMatch(address,bytes,address)', ['address', 'bytes', 'address'],
                [target, rng.choice([b'', b'\x01', b'\x11' * 40]),
                 rng.choice([MATCH_ADDR, OTHER_ADDR, '0x' + '00' * 20])])
        elif choice == 1:
            mode = rng.randrange(8)
            arg = rng.choice([0, 1, 5, 25])
            add('compareCallAndState(address,uint256,uint256,address)',
                ['address', 'uint256', 'uint256', 'address'], [target, mode, arg, taddr])
        elif choice == 2:
            add('setDirectKeyInternal(address,bytes32,bytes32,bytes)',
                ['address', 'bytes32', 'bytes32', 'bytes'],
                [target, bkey, rng.getrandbits(256).to_bytes(32, 'big'), b'\xca\xfe'])
        elif choice == 3:
            add('setComputedKeyLinked(address,bytes32,address,bytes4,uint256)',
                ['address', 'bytes32', 'address', 'bytes4', 'uint256'],
                [target, bkey, taddr, rsel, rng.randrange(1000)])
        else:
            add('setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)',
                ['address', 'uint256', 'bytes32', 'address', 'bytes4', 'uint256'],
                [target, rng.randrange(4), bkey, taddr, rsel, rng.choice([0, 1, 2, 7])])
    return calls


def verify_responder_semantics(via_ir: bool, observations: dict[str, list[dict]]) -> None:
    encode, _, _, _, _ = _eth_deps()
    enc_u256 = lambda n: '0x' + encode(['uint256'], [n]).hex()
    for route, rows in observations.items():
        if rows[0]['status'] != 'ok' or rows[0]['data'] != enc_u256(int(MATCH_ADDR, 16)):
            raise HarnessError(f'{route}: tx 0 assertDeployMatch matching call failed')
        if rows[1]['status'] != 'revert' or rows[1]['data'] != PANIC_ASSERT:
            raise HarnessError(f'{route}: tx 1 mismatching assertDeployMatch did not Panic(0x01)')
        if rows[2]['status'] != 'revert' or len(rows[2]['data']) != 2 + 68 * 2:
            raise HarnessError(f'{route}: tx 2 reverting callee payload was not forwarded')
        for idx in (3, 4, 5):
            if rows[idx]['status'] != 'revert' or rows[idx]['data'] != '0x':
                raise HarnessError(f'{route}: tx {idx} invalid/short/empty return did not revert empty')
        # Mode 0: stored (5) == _stepWord(2, 9, 5) -> true (100009) under via-IR, false (9) under legacy.
        want_m0 = enc_u256(100009 if via_ir else 9)
        want_m1 = enc_u256(9 if via_ir else 100009)
        if rows[6]['data'] != want_m0 or rows[7]['data'] != want_m1:
            raise HarnessError(f'{route}: pipeline comparison order mismatch on mode 0/1')
        # Tx 11: (100 / 0) == deployWord(reverting): Panic(0x12) under via-IR, custom revert under legacy.
        if via_ir:
            if rows[11]['data'] != PANIC_DIV_ZERO or len(rows[12]['data']) != 2 + 68 * 2:
                raise HarnessError(f'{route}: via-IR competing revert order mismatch on tx 11/12')
        else:
            if len(rows[11]['data']) != 2 + 68 * 2 or rows[12]['data'] != PANIC_DIV_ZERO:
                raise HarnessError(f'{route}: legacy competing revert order mismatch on tx 11/12')
        # Tx 18 vs 19: RHS custom revert beats outer 0x12, and outer 0x12 beats inner 0x11.
        if len(rows[18]['data']) != 2 + 68 * 2 or rows[19]['data'] != PANIC_DIV_ZERO:
            raise HarnessError(f'{route}: struct-mapping revert order mismatch on tx 18/19')


def reentrant_hooks() -> list[tuple[int, int, int, int, int, int]]:
    sel = reenter_mutate_sel()
    return [
        (0, 0, 0, 0, 0, NO_CALLBACK),
        (0, 0, 0, 0, 0, NO_CALLBACK | REVERT_AFTER),
        (sel, 3, int.from_bytes(B_NEW, 'big'), int(T_NEW, 16), 42, 0),
        (sel, 3, int.from_bytes(B_NEW, 'big'), int(T_NEW, 16), 42, REVERT_AFTER),
        (sel, 3, int.from_bytes(B_NEW, 'big'), int(T_NEW, 16), 999, 0),
        (sel, 3, int.from_bytes(B_ALT, 'big'), int(T_ALT, 16), 5, 0),
    ]


def reentrant_plan(count: int, seed: int, caller: str, hooks: list[str]) -> list[dict]:
    inert, failing, cb_42, cb_revert_after, cb_fail_inner, cb_5 = hooks
    targets = [*hooks, EMPTY, SENDER]
    rng = random.Random(seed)
    calls: list[dict] = []
    first_block = len(LIBRARIES) + len(hooks) + 2
    sel = b'\xab\xcd\xef\x01'

    def add(fn, tys, vals):
        make_call(calls, caller, first_block, fn, tys, vals)

    # Tx 0: seed initial storage (curBucket = B_INIT, curTarget = T_INIT, stored = 1).
    add('reenterMutate(bytes32,address,uint256)', ['bytes32', 'address', 'uint256'],
        [B_INIT, T_INIT, 1])
    # Tx 1: setReentrantStorageKeys(cb_42) -> RHS re-enters and updates (B_NEW, T_NEW, 42) BEFORE
    # outer LHS reads curBucket and _packKey(curTarget, sel).
    add('setReentrantStorageKeys(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
        [cb_42, sel, 77])
    # Tx 2..3: compareCallAndState mode 8 & 9 across re-entrant callback setting stored = 42.
    add('compareCallAndState(address,uint256,uint256,address)',
        ['address', 'uint256', 'uint256', 'address'], [cb_42, 8, 0, T_NEW])
    add('compareCallAndState(address,uint256,uint256,address)',
        ['address', 'uint256', 'uint256', 'address'], [cb_42, 9, 0, T_NEW])
    # Tx 4..6: reverting callback / post-callback revert / inert hook.
    add('setReentrantStorageKeys(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
        [cb_revert_after, sel, 88])
    add('setReentrantStorageKeys(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
        [cb_fail_inner, sel, 99])
    add('setReentrantStorageKeys(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
        [inert, sel, 55])

    while len(calls) < count:
        target = rng.choice(targets)
        choice = rng.randrange(3)
        if choice == 0:
            add('setReentrantStorageKeys(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
                [target, rng.getrandbits(32).to_bytes(4, 'big'), rng.randrange(500)])
        elif choice == 1:
            add('compareCallAndState(address,uint256,uint256,address)',
                ['address', 'uint256', 'uint256', 'address'],
                [target, rng.choice([8, 9]), 0, T_INIT])
        else:
            add('reenterMutate(bytes32,address,uint256)', ['bytes32', 'address', 'uint256'],
                [rng.choice([B_INIT, B_NEW, B_ALT]), rng.choice([T_INIT, T_NEW]),
                 rng.choice([2, 10, 999])])
    return calls


def _render_driver(driver_src: str, directory: Path, solc: Path) -> str:
    rendered = driver_src.replace(ANCHOR, f'from "{directory}"\n  entry "Sequence.sol"')
    if '0.8.38' in solc.name:
        rendered = rendered.replace(
            'using { evmVersion := "osaka"',
            'using { solc := "0.8.38+commit.1835d247", evmVersion := "osaka"',
        )
    return rendered


def run_responder_campaign(directory: Path, via_ir: bool, transactions: int, seed: int,
                           shrink_attempts: int, solc: Path = SOLC,
                           enforce_semantics: bool = True) -> tuple[int, dict]:
    encode, _, _, EVM, Denote = _eth_deps()
    directory = directory.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    source = FIXTURE.read_text(encoding='utf-8')
    driver_src = (DRIVER_IR if via_ir else DRIVER_LEGACY).read_text(encoding='utf-8')
    if driver_src.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported source anchor')
    (directory / 'Sequence.sol').write_text(source, encoding='utf-8')
    driver = directory / 'Driver.lean'
    driver.write_text(_render_driver(driver_src, directory, solc), encoding='utf-8')

    linked = {name: address(i) for i, name in enumerate(LIBRARIES)}
    caller = address(len(LIBRARIES))
    accounts = [address(len(LIBRARIES) + 1 + i) for i in range(len(RESPONDERS))]

    settings = {
        'evmVersion': 'osaka',
        'viaIR': via_ir,
        'optimizer': {'enabled': True, 'runs': 466},
        'metadata': {'bytecodeHash': 'none'},
        'libraries': {'Sequence.sol': linked},
        'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object',
            'evm.bytecode.linkReferences', 'evm.methodIdentifiers']}},
    }
    responder_src = RESPONDER.read_text(encoding='utf-8').replace(
        'pragma solidity 0.8.34;', 'pragma solidity >=0.8.34 <0.9.0;')
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {
            'Sequence.sol': {'content': source},
            RESPONDER.name: {'content': responder_src},
        },
        'settings': settings,
    }, directory, directory / 'solc', solc=solc)['contracts']

    seq_contracts = compiled['Sequence.sol']
    for name in LIBRARIES + (CONTRACT,):
        bc = seq_contracts[name]['evm']['bytecode']
        if bc['linkReferences'] or '__$' in bc['object']:
            raise HarnessError(f'{name} is not fully linked')
    identifiers = seq_contracts[CONTRACT]['evm']['methodIdentifiers']
    signatures = roots(driver_src)
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in signatures])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text(encoding='utf-8')}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')

    lib_codes = ['0x' + seq_contracts[name]['evm']['bytecode']['object'] for name in LIBRARIES]
    caller_a = '0x' + seq_contracts[CONTRACT]['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    mock = compiled[RESPONDER.name]['RecordingCallResponder']['evm']
    runtime = '0x' + mock['deployedBytecode']['object']
    responder_deploys = [
        '0x' + mock['bytecode']['object'] + encode(['uint256', 'bool', 'uint256'], list(p)).hex()
        for p in RESPONDERS
    ]
    initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, words in zip(accounts, RESPONDERS, strict=True)
        for slot, val in enumerate(words)
    ]
    calls = responder_plan(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {
        'program': 'recording-call-responder-v1',
        'accounts': [str(int(a, 16)) for a in accounts],
        'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))],
        'gas': '1000000',
    }
    adapters = {
        'source': EVM(directory / 'A', [*lib_codes, caller_a, *responder_deploys], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment,
                        account_code=[(account, runtime) for account in accounts]),
        'compiled': EVM(directory / 'C', [*lib_codes, caller_c, *responder_deploys], initial),
    }
    result = replay_three_routes(calls, adapters)
    report = {
        'variant': 'responders',
        'viaIR': via_ir,
        'transactions': calls,
        'observations': result['observations'],
        'divergences': result['divergences'],
        'seed': seed,
        'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
    }
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    if enforce_semantics:
        verify_responder_semantics(via_ir, result['observations'])
    write_json(directory / 'campaign.json', report)
    return 0, report


def run_reentrant_campaign(directory: Path, via_ir: bool, transactions: int, seed: int,
                           shrink_attempts: int, solc: Path = SOLC) -> tuple[int, dict]:
    encode, _, _, EVM, Denote = _eth_deps()
    directory = directory.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    source = FIXTURE.read_text(encoding='utf-8')
    driver_src = (DRIVER_IR if via_ir else DRIVER_LEGACY).read_text(encoding='utf-8')
    (directory / 'Sequence.sol').write_text(source, encoding='utf-8')
    driver = directory / 'Driver.lean'
    driver.write_text(_render_driver(driver_src, directory, solc), encoding='utf-8')

    hooks_cfg = reentrant_hooks()
    linked = {name: address(i) for i, name in enumerate(LIBRARIES)}
    caller = address(len(LIBRARIES))
    accounts = [address(len(LIBRARIES) + 1 + i) for i in range(len(hooks_cfg))]

    settings = {
        'evmVersion': 'osaka',
        'viaIR': via_ir,
        'optimizer': {'enabled': True, 'runs': 466},
        'metadata': {'bytecodeHash': 'none'},
        'libraries': {'Sequence.sol': linked},
        'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object',
            'evm.bytecode.linkReferences', 'evm.methodIdentifiers']}},
    }
    hook_src = HOOK.read_text(encoding='utf-8').replace(
        'pragma solidity 0.8.34;', 'pragma solidity >=0.8.34 <0.9.0;')
    compiled = solc_compile({
        'language': 'Solidity',
        'sources': {
            'Sequence.sol': {'content': source},
            HOOK.name: {'content': hook_src},
        },
        'settings': settings,
    }, directory, directory / 'solc', solc=solc)['contracts']

    seq_contracts = compiled['Sequence.sol']
    identifiers = seq_contracts[CONTRACT]['evm']['methodIdentifiers']
    signatures = roots(driver_src)
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in signatures])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text(encoding='utf-8')}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']

    lib_codes = ['0x' + seq_contracts[name]['evm']['bytecode']['object'] for name in LIBRARIES]
    caller_a = '0x' + seq_contracts[CONTRACT]['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    hook_evm = compiled[HOOK.name]['ReentrantCallbackHook']['evm']
    runtime = '0x' + hook_evm['deployedBytecode']['object']
    hook_deploys = [
        '0x' + hook_evm['bytecode']['object'] + encode(['uint256'] * 6, list(h)).hex()
        for h in hooks_cfg
    ]
    initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, h in zip(accounts, hooks_cfg, strict=True)
        for slot, val in enumerate(h) if val
    ]
    calls = reentrant_plan(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    environment = {
        'program': 'reentrant-callback-v1',
        'accounts': [str(int(a, 16)) for a in accounts],
        'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))],
        'gas': '1000000',
    }
    adapters = {
        'source': EVM(directory / 'A', [*lib_codes, caller_a, *hook_deploys], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment,
                        account_code=[(account, runtime) for account in accounts]),
        'compiled': EVM(directory / 'C', [*lib_codes, caller_c, *hook_deploys], initial),
    }
    result = replay_three_routes(calls, adapters)
    report = {
        'variant': 'reentrant',
        'viaIR': via_ir,
        'transactions': calls,
        'observations': result['observations'],
        'divergences': result['divergences'],
        'seed': seed,
    }
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report

    # Verify pipeline-specific re-entrant comparison order on tx 2 (mode 8: stored == _invokeAndReturn)
    enc_u256 = lambda n: '0x' + encode(['uint256'], [n]).hex()
    want_tx2 = enc_u256(100042 if via_ir else 42)
    for route, rows in result['observations'].items():
        if rows[1]['status'] != 'ok':
            raise HarnessError(f'{route}: tx 1 setReentrantStorageKeys failed')
        if rows[2]['status'] != 'ok' or rows[2]['data'] != want_tx2:
            raise HarnessError(f'{route}: tx 2 re-entrant comparison order mismatch')
        if rows[5]['status'] != 'revert' or len(rows[5]['data']) <= 10:
            raise HarnessError(f'{route}: tx 5 inner callback revert bytes not bubbled')

    # Negative control: disable callbacks on Denote only and verify divergence on tx 0..2.
    inert_initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, h in zip(accounts, hooks_cfg, strict=True)
        for slot, val in enumerate((*h[:5], h[5] | NO_CALLBACK)) if val
    ]
    neg_dir = directory / 'negative'
    neg_adapters = {
        'source': EVM(neg_dir / 'A', [*lib_codes, caller_a, *hook_deploys], initial),
        'model': Denote(neg_dir / 'B', driver, caller, inert_initial,
                        byte_call_environment=environment,
                        account_code=[(account, runtime) for account in accounts]),
        'compiled': EVM(neg_dir / 'C', [*lib_codes, caller_c, *hook_deploys], initial),
    }
    neg_result = replay_three_routes(calls[:3], neg_adapters)
    if not neg_result['divergences']:
        raise HarnessError('re-entry negative control failed: model without callbacks did not diverge')
    write_json(directory / 'campaign.json', report)
    return 0, report


def run_mutations(output: Path, selected: list[str] | None = None) -> int:
    import json
    root = Path.cwd()
    names = selected or list(MUTANTS)
    for name in names:
        rel, before, _ = MUTANTS[name]
        if (root / rel).read_text(encoding='utf-8').count(before) != 1:
            raise HarnessError(f'{name}: mutation anchor must occur exactly once in {rel}')
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in names:
        rel, before, after = MUTANTS[name]
        work = output / name
        snapshot(work)
        try:
            env = dict(os_env_with_scripts(work))
            base_argv = [
                sys.executable, '-m',
                'solidity_differential.check_stateful_comparison_and_struct_map_rhs',
                '--responders-only', '--via-ir-only', '--no-enforce-semantics',
                '--transactions', '22', '--shrink-attempts', '20',
            ]
            base_res = run_bounded(
                [*base_argv, '--output', str(work / '.lake/baseline')],
                cwd=work, env=env, timeout=900,
            )
            (work / 'baseline.log').write_text(base_res.stdout + base_res.stderr, encoding='utf-8')
            base_file = work / '.lake/baseline/responders-ir/campaign.json'
            base_camp = json.loads(base_file.read_text(encoding='utf-8')) if base_file.exists() else {}
            if base_res.returncode != 0 or base_camp.get('divergences') or not base_camp.get('transactions'):
                raise HarnessError(f'{name}: unmodified positive control failed in snapshot')

            # Mutate Import.lean in the isolated snapshot and rebuild Import (capped at 1800s).
            target_file = work / rel
            text = target_file.read_text(encoding='utf-8')
            if text.count(before) != 1:
                raise HarnessError(f'{name}: nonunique mutation anchor in snapshot')
            target_file.write_text(text.replace(before, after), encoding='utf-8')
            command(['lake', 'build', 'Compiler.SolidityImport.Import'],
                    cwd=work, timeout=1800, log=work / 'build.log')
            res = run_bounded(
                [*base_argv, '--output', str(work / '.lake/mutated')],
                cwd=work, env=env, timeout=900,
            )
            (work / 'mutated.log').write_text(res.stdout + res.stderr, encoding='utf-8')
            campaign_file = work / '.lake/mutated/responders-ir/campaign.json'
            if not campaign_file.exists():
                raise HarnessError(
                    f'{name}: mutated run produced no campaign.json (build/tool failure is not detection)')
            camp = json.loads(campaign_file.read_text(encoding='utf-8'))
            if res.returncode == 0 or not camp.get('divergences'):
                raise HarnessError(f'{name}: mutant SURVIVED without A/B/C divergence!')
            reduced_file = work / '.lake/mutated/responders-ir/reduced.json'
            reduced = json.loads(reduced_file.read_text(encoding='utf-8'))
            if not reduced.get('deletion_minimal') or not reduced.get('transactions'):
                raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
            reports.append({
                'name': name,
                'detected': True,
                'baselinePassed': True,
                'firstDivergence': camp['divergences'][0]['id'],
                'witness': reduced,
            })
            print(f'MUTANT DETECTED [{name}]: diverged at tx {camp["divergences"][0]["id"]}',
                  flush=True)
        finally:
            release(work)
    write_json(output / 'mutations.json', {'passed': True, 'mutants': reports})
    return 0


def os_env_with_scripts(directory: Path) -> dict[str, str]:
    import os
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=48)
    parser.add_argument('--seed', type=int, default=2976)
    parser.add_argument('--shrink-attempts', type=int, default=60)
    parser.add_argument('--solc', type=Path, default=SOLC)
    parser.add_argument('--responders-only', action='store_true')
    parser.add_argument('--via-ir-only', action='store_true')
    parser.add_argument('--no-enforce-semantics', action='store_true')
    parser.add_argument('--mutations', action='store_true')
    parser.add_argument('--mutant', action='append')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()

    Path('.lake').mkdir(exist_ok=True)
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='stateful-cmp-rhs-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=True)

    if args.mutations:
        return run_mutations(output, args.mutant)

    if args.transactions < 22:
        parser.error('at least 22 transactions are needed to cover the deterministic prefix')

    pipelines = [(True, 'ir')] if args.via_ir_only else [(True, 'ir'), (False, 'legacy')]
    completed = []
    for via_ir, label in pipelines:
        code, _ = run_responder_campaign(
            output / f'responders-{label}', via_ir, args.transactions, args.seed,
            args.shrink_attempts, solc=args.solc, enforce_semantics=not args.no_enforce_semantics)
        if code:
            raise SystemExit(f'responder A/B/C divergence ({label}): {output / f"responders-{label}"}')
        completed.append(f'responders-{label}')
        if not args.responders_only:
            code, _ = run_reentrant_campaign(
                output / f'reentrant-{label}', via_ir, max(24, args.transactions // 2), args.seed,
                args.shrink_attempts, solc=args.solc)
            if code:
                raise SystemExit(f'reentrant A/B/C divergence ({label}): {output / f"reentrant-{label}"}')
            completed.append(f'reentrant-{label}')

    write_json(output / 'summary.json', {
        'passed': True,
        'campaigns': completed,
        'transactions': args.transactions,
        'seed': args.seed,
        'solc': str(args.solc),
    })
    print(f'stateful comparison & struct-mapping RHS A/B/C agree ({", ".join(completed)}): {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
