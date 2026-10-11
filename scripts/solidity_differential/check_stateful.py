"""Real A/B/C sequence regression for the handwritten scalar instrument fixture."""
import argparse
import hashlib
import random
from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence
from .identity import ImplementationIdentity
from .programs import stateful_scalar_source


OFFER_MEM_SIG = 'inspectOfferMem(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),uint256)'
OFFER_CD_SIG = 'inspectOfferCd(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),uint256,address)'
RATIFY_OFFER_CD_SIG = 'ratifyOfferCd(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),bytes32,uint256)'


def _encode_mixed_payload_call(
    rate_floor,
    *,
    min_rate=1200,
    allowed_taker=0x3001,
    active=1,
    tag=0xAABBCCDD << 224,
    weights=(10, 20),
    extra_len=None,
    extra_words=(0x11223344 << 224,),
    label_len=None,
    label_words=(0x616c706861 << 216,),
    raw_offset=64,
    raw_len=None,
    weights_rel_offset=None,
    extra_rel_offset=None,
    label_rel_offset=None,
):
    actual_extra_len = (32 * len(extra_words)) if extra_len is None else extra_len
    actual_label_len = (32 * len(label_words)) if label_len is None else label_len
    w_off = (7 * 32) if weights_rel_offset is None else weights_rel_offset
    e_off = (w_off + 32 * (1 + len(weights))) if extra_rel_offset is None else extra_rel_offset
    l_off = (e_off + 32 * (1 + len(extra_words))) if label_rel_offset is None else label_rel_offset
    inner_words = [
        min_rate,
        allowed_taker,
        active,
        tag,
        w_off,
        e_off,
        l_off,
        len(weights),
        *weights,
        actual_extra_len,
        *extra_words,
        actual_label_len,
        *label_words,
    ]
    actual_raw_len = (32 * len(inner_words)) if raw_len is None else raw_len
    return [raw_offset, rate_floor, actual_raw_len, *inner_words]


def _encode_offer_call(
    extra_scalars,
    *,
    chain_id=1,
    midnight=0x1111,
    loan_token=0x2222,
    collateral_params=(),
    maturity=1700000000,
    rcf_threshold=5000,
    enter_gate=0x3333,
    liquidator_gate=0x4444,
    buy=1,
    maker=0x5555,
    start=100,
    expiry=200,
    tick=120,
    group=0xABCD,
    callback=0x6666,
    cb_words=(),
    cb_len=None,
    receiver_if_seller=0x7777,
    ratifier=0x8888,
    reduce_only=0,
    max_units=1000,
    max_assets=2000,
    fee_cap=300,
    offer_offset=None,
    market_rel_offset=None,
    cp_rel_offset=None,
    cb_rel_offset=None,
):
    head_arity = 1 + len(extra_scalars)
    top_off = (32 * head_arity) if offer_offset is None else offer_offset
    mkt_off = (15 * 32) if market_rel_offset is None else market_rel_offset
    cp_off = (8 * 32) if cp_rel_offset is None else cp_rel_offset
    mkt_words = [
        chain_id,
        midnight,
        loan_token,
        cp_off,
        maturity,
        rcf_threshold,
        enter_gate,
        liquidator_gate,
        len(collateral_params),
    ]
    for cp in collateral_params:
        mkt_words.extend(cp)
    default_cb_off = 15 * 32 + 32 * len(mkt_words)
    cb_off = default_cb_off if cb_rel_offset is None else cb_rel_offset
    actual_cb_len = (32 * len(cb_words)) if cb_len is None else cb_len
    offer_head = [
        mkt_off,
        buy,
        maker,
        start,
        expiry,
        tick,
        group,
        callback,
        cb_off,
        receiver_if_seller,
        ratifier,
        reduce_only,
        max_units,
        max_assets,
        fee_cap,
    ]
    return [top_off, *extra_scalars, *offer_head, *mkt_words, actual_cb_len, *cb_words]


def _encode_ratify_offer_call(
    root,
    actual_rate,
    *,
    min_rate=500,
    allowed_taker=0,
    leaf_index=0,
    proof=(),
    proof_rel_offset=128,
    cb_len=None,
    collateral_params=(),
    buy=1,
    reduce_only=0,
    max_units=1000,
):
    cb_words = (min_rate, allowed_taker, leaf_index, proof_rel_offset, len(proof), *proof)
    return _encode_offer_call(
        [root, actual_rate],
        collateral_params=collateral_params,
        cb_words=cb_words,
        cb_len=cb_len,
        buy=buy,
        reduce_only=reduce_only,
        max_units=max_units,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant', choices=['baseline', 'scoped', 'early-return'], default='baseline')
    parser.add_argument('--dirty-mappings', action='store_true',
        help='seed the MappingDirtySequence layout with noncanonical low bytes and nonzero upper bits')
    parser.add_argument('--argument-bits', type=int, default=256,
        help='unsigned width of the change argument; generates canonical ABI words')
    parser.add_argument('--change-prefix', type=int, nargs='+', default=[],
        help='deterministic initial change arguments before random calls')
    parser.add_argument('--seed', type=int, default=2448)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--senders', type=int, default=1, help='number of funded transaction senders (1 to 10)')
    parser.add_argument('--shrink-attempts', type=int, default=1000)
    parser.add_argument('--model-driver', type=Path,
        default=Path('Contracts/SolidityImportSmoke/SequenceModel.lean'))
    parser.add_argument('--solc-version', choices=('0.8.34', '0.8.10'), default='0.8.34')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--source-fixture', type=Path,
        default=Path(__file__).parent / 'fixtures/Sequence.sol')
    args = parser.parse_args()
    if args.argument_bits not in range(8, 257, 8):
        parser.error('argument width must be a byte-aligned unsigned width from 8 to 256')
    if args.dirty_mappings and args.argument_bits != 256:
        parser.error('dirty mapping fixture requires uint256 arguments')
    if not 1 <= args.senders <= 10:
        parser.error('sender count must be between one and ten')
    if args.transactions < 3 or args.shrink_attempts < 2:
        parser.error('at least three transactions and two shrink attempts required')
    if args.dirty_mappings and args.transactions < 5:
        parser.error('dirty mapping coverage requires at least five transactions')
    if any(value < 0 or value >= (1 << args.argument_bits) for value in args.change_prefix):
        parser.error('change prefix values must fit the argument width')
    if len(args.change_prefix) > args.transactions - 3:
        parser.error('change prefix exceeds the transaction budget')
    if args.dirty_mappings and args.change_prefix:
        parser.error('change prefix cannot replace the dirty mapping witness prefix')
    if args.output is None:
        output = Path(tempfile.mkdtemp(prefix='stateful-abc-', dir='.lake')).resolve()
    else:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    fixture = args.source_fixture.resolve()
    source_text = stateful_scalar_source(fixture.read_text(), args.variant)
    solc_bin = SOLC if args.solc_version == '0.8.34' else SOLC.with_name('solc-0.8.10')
    evm_version = 'osaka' if args.solc_version == '0.8.34' else 'london'
    optimizer_runs = 466 if args.solc_version == '0.8.34' else 1
    source_settings = {'evmVersion': evm_version,
        'optimizer': {'enabled': True, 'runs': optimizer_runs},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}
    if args.solc_version == '0.8.34':
        source_settings['viaIR'] = True
    request = {'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source_text}},
        'settings': source_settings}
    source = solc_compile(request, fixture.parent, output / 'source', solc=solc_bin)['contracts']['Sequence.sol']['SequenceFixture']['evm']
    names = [f'change(uint{args.argument_bits})', 'fail()', 'read()']
    for extra_name in (
        'inspectBytes(bytes,uint256)',
        'redeemRewards(bytes)',
        'getRewardTokens()',
        'echoMsgData()',
        'applyRounding(uint8,uint256)',
        'inspectStatic((uint128,uint64,bool),uint256)',
        'applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)',
        'inspectArraysAndStrings(uint256[],address[],string,uint256)',
        'inspectNarrowArray(uint64[],uint256)',
        'inspectBytesMemory(bytes,bytes,string,uint256)',
        'concatStrings(string,string,uint256)',
        'buildPayload(bytes,bytes,uint256)',
        'syncStorage(string,bytes,uint256)',
        'getName()',
        'getPayload()',
        'hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)',
        'checkInterface(bytes4,uint256)',
        'royaltyAndHolderCheck(uint256,uint256)',
        'dequeAndBitmapStep(string,uint256)',
        'slotAndShortStringStep(string,uint32,uint32,uint256)',
        'vaultLabel()',
        'trancheHistorySnapshot(uint256)',
        'lookupWindow(uint48,uint256)',
        'quoteTickRoundtrip(uint256,uint256)',
        'DOMAIN_SEPARATOR()',
        OFFER_MEM_SIG,
        OFFER_CD_SIG,
        'decodeMixedPayload(bytes,uint256)',
        RATIFY_OFFER_CD_SIG,
        'checkpoints(address,uint32)',
        'latestTotalCheckpoint()',
        'pendingDefaultAdminView()',
        'voteWindow(uint256,uint256)',
        'VAULT_NAME()',
        'asset()',
        'currentEpoch()',
        'history(uint256)',
        'tiers(uint256)',
        'positions(address)',
        'probeBuiltins(uint256,uint256)',
    ):
        if extra_name in source['methodIdentifiers']:
            names.append(extra_name)
    write_json(output / 'selectors.json', [int(source['methodIdentifiers'][name], 16) for name in names])
    driver = args.model_driver.resolve()
    extra_inputs = [fixture]
    imported_dep = fixture.parent / 'Solc0810Imported.sol'
    if imported_dep.exists():
        extra_inputs.append(imported_dep)
    identity = ImplementationIdentity(driver, extra_inputs=extra_inputs)
    write_json(output / 'implementation.json', identity.manifest)
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            timeout=600, log=output / 'compile-model.log')
    identity.verify()
    compiled = solc_compile({'language': 'Yul', 'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': evm_version, 'optimizer': {'enabled': True, 'runs': optimizer_runs},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, fixture.parent, output / 'compiled', solc=solc_bin)
    objects = list(compiled['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled object')
    source_code = '0x' + source['bytecode']['object']
    compiled_code = '0x' + objects[0]['evm']['bytecode']['object']
    with Anvil(output / 'deployment-discovery') as node:
        senders = node.rpc('eth_accounts')[:args.senders]
        if len(senders) != args.senders:
            raise HarnessError('Anvil did not provide the requested funded senders')
        sender = senders[0]
        deployed = node.transact({'from': sender, 'data': source_code, 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('source fixture deployment failed')
        account = deployed['receipt']['contractAddress']
        initial_storage = []
        if args.dirty_mappings:
            def mapping_slot(base, key):
                return int(node.rpc('web3_sha3', '0x' + format(key, '064x') + format(base, '064x')), 16)
            dirty = (0xabcdef << 232) | (0x123456 << 128) | 0x102
            slots = {mapping_slot(3, 7)}
            for owner in senders:
                key = int(owner, 16)
                slots.update((mapping_slot(0, key),
                    mapping_slot(mapping_slot(1, key), int(account, 16)),
                    mapping_slot(mapping_slot(2, key), 7)))
            initial_storage = [[account, '0x' + format(slot, '064x'),
                                '0x' + format(dirty, '064x')] for slot in sorted(slots)]
    write_json(output / 'initial-storage.json', initial_storage)
    rng = random.Random(args.seed)
    calls = [(names[0], [7]), ('fail()', []), ('read()', [])]
    calls.extend((names[0], [value]) for value in args.change_prefix)
    if 'inspectBytes(bytes,uint256)' in source['methodIdentifiers']:
        bytes_prefix = [
            ('getRewardTokens()', []),
            ('redeemRewards(bytes)', [32, 0]),
            ('redeemRewards(bytes)', [32, 5, 0x1122334455 << 216]),
            ('redeemRewards(bytes)', [32, 33, 1]),
            ('redeemRewards(bytes)', [64, 0]),
            ('inspectBytes(bytes,uint256)', [64, 7, 0]),
            ('inspectBytes(bytes,uint256)', [64, 9, 5, 0xdeadbeef01 << 216]),
            ('inspectBytes(bytes,uint256)', [64, 11, 32, (1 << 256) - 1]),
            ('inspectBytes(bytes,uint256)', [64, 13, 33, 1]),
            ('inspectBytes(bytes,uint256)', [64, 15, 1 << 64, 0]),
            ('inspectBytes(bytes,uint256)', [1 << 64, 17, 0]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(bytes_prefix[:remaining_budget])
    if 'applyRounding(uint8,uint256)' in source['methodIdentifiers']:
        enum_prefix = [
            ('echoMsgData()', []),
            ('applyRounding(uint8,uint256)', [0, 10]),
            ('applyRounding(uint8,uint256)', [1, 20]),
            ('applyRounding(uint8,uint256)', [2, 30]),
            ('applyRounding(uint8,uint256)', [3, 40]),
            ('applyRounding(uint8,uint256)', [255, 50]),
            ('applyRounding(uint8,uint256)', [256, 60]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(enum_prefix[:remaining_budget])
    if 'applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)' in source['methodIdentifiers']:
        bundle_prefix = [
            ('inspectStatic((uint128,uint64,bool),uint256)', [3, 5, 1, 10]),
            ('inspectStatic((uint128,uint64,bool),uint256)', [3, 5, 0, 10]),
            ('inspectStatic((uint128,uint64,bool),uint256)', [1 << 128, 5, 1, 10]),
            ('inspectStatic((uint128,uint64,bool),uint256)', [3, 5, 2, 10]),
            ('applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)', [64, 0, 10, 96, 128, 0, 0]),
            ('applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)', [64, 0, 10, 96, 224, 1, 7, 3, 1, 1, 11]),
            ('applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)', [64, 1, 10, 96, 320, 2, 7, 3, 1, 13, 5, 1, 2, 11, 17]),
            ('applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)', [64, 0, 10, 96, 224, 1, 7, 1 << 64, 1, 1, 11]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(bundle_prefix[:remaining_budget])
    if 'inspectArraysAndStrings(uint256[],address[],string,uint256)' in source['methodIdentifiers']:
        array_str_prefix = [
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 160, 192, 7, 0, 0, 0]),
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 192, 256, 11, 1, 100, 1, 0x1234, 5, 0x68656c6c6f << 216]),
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 224, 320, 19, 2, 100, 200, 2, 0x1111, 0x2222, 32, 0x41424344 << 224]),
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 192, 288, 23, 1, 100, 2, 0x1111, 0x2222, 0]),
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 192, 256, 29, 1, 100, 1, 1 << 160, 0]),
            ('inspectArraysAndStrings(uint256[],address[],string,uint256)', [128, 192, 256, 31, 1, 100, 1, 0x1234, 33, 1]),
            ('inspectNarrowArray(uint64[],uint256)', [64, 3, 0]),
            ('inspectNarrowArray(uint64[],uint256)', [64, 5, 2, 10, 25]),
            ('inspectNarrowArray(uint64[],uint256)', [64, 7, 1, (1 << 64) - 1]),
            ('inspectNarrowArray(uint64[],uint256)', [64, 9, 1, 1 << 64]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(array_str_prefix[:remaining_budget])
    if 'inspectBytesMemory(bytes,bytes,string,uint256)' in source['methodIdentifiers']:
        bytes_mem_prefix = [
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [128, 160, 192, 7, 0, 0, 0]),
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [128, 192, 256, 11, 4, 0x11223344 << 224, 5, 0xdeadbeef01 << 216, 3, 0x616263 << 232]),
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [128, 192, 288, 19, 32, (1 << 256) - 1, 33, 0x123456789abcdef0, 0xff << 248, 5, 0x68656c6c6f << 216]),
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [128, 160, 192, 23, 65, 0, 0]),
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [96, 160, 192, 29, 0, 0, 0]),
            ('inspectBytesMemory(bytes,bytes,string,uint256)', [128, 160, 192, 31, 0, 1 << 64, 0]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(bytes_mem_prefix[:remaining_budget])
    if 'concatStrings(string,string,uint256)' in source['methodIdentifiers']:
        dyn_ret_prefix = [
            ('concatStrings(string,string,uint256)', [96, 128, 0, 0, 0]),
            ('concatStrings(string,string,uint256)', [96, 160, 4, 5, 0x68656c6c6f << 216, 5, 0x776f726c64 << 216]),
            ('concatStrings(string,string,uint256)', [96, 160, 1, 5, 0x616c706861 << 216, 4, 0x62657461 << 224]),
            ('concatStrings(string,string,uint256)', [96, 160, 2, 6, 0x70617265746f << 208, 3, 0x63646f << 232]),
            ('concatStrings(string,string,uint256)', [96, 160, 3, 4, 0x69646c65 << 224, 0]),
            ('concatStrings(string,string,uint256)', [96, 160, 7, 4, 0x69646c65 << 224, 7, 0x7472616e636865 << 200]),
            ('concatStrings(string,string,uint256)', [96, 160, 8, 32, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 3, 0x363738 << 232]),
            ('concatStrings(string,string,uint256)', [64, 128, 0, 0, 0]),
            ('buildPayload(bytes,bytes,uint256)', [96, 160, 0, 4, 0x11223344 << 224, 2, 0xaabb << 240]),
            ('buildPayload(bytes,bytes,uint256)', [96, 128, 1, 0, 0]),
            ('buildPayload(bytes,bytes,uint256)', [96, 128, 2, 0, 0]),
            ('buildPayload(bytes,bytes,uint256)', [96, 160, 3, 5, 0xdeadbeef01 << 216, 3, 0x010203 << 232]),
            ('buildPayload(bytes,bytes,uint256)', [96, 128, 4, 0, 0]),
            ('buildPayload(bytes,bytes,uint256)', [96, 128, 9, 0, 6, 0xfeedfacecafe << 208]),
            ('buildPayload(bytes,bytes,uint256)', [96, 128, 5, 0, 1 << 64]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(dyn_ret_prefix[:remaining_budget])
    if 'syncStorage(string,bytes,uint256)' in source['methodIdentifiers']:
        storage_bytes_prefix = [
            ('getName()', []),
            ('getPayload()', []),
            ('syncStorage(string,bytes,uint256)', [96, 160, 0, 5, 0x616c706861 << 216, 4, 0x11223344 << 224]),
            ('getName()', []),
            ('getPayload()', []),
            ('syncStorage(string,bytes,uint256)', [96, 192, 1, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232, 33, 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20, 0xff << 248]),
            ('getName()', []),
            ('getPayload()', []),
            ('syncStorage(string,bytes,uint256)', [96, 160, 2, 4, 0x62657461 << 224, 3, 0xaabbcc << 232]),
            ('getName()', []),
            ('getPayload()', []),
            ('syncStorage(string,bytes,uint256)', [96, 128, 3, 0, 0]),
            ('getName()', []),
            ('syncStorage(string,bytes,uint256)', [96, 160, 4, 6, 0x70617265746f << 208, 0]),
            ('getPayload()', []),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(storage_bytes_prefix[:remaining_budget])
    if 'hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)' in source['methodIdentifiers']:
        market_bundle_prefix = [
            ('hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)', [64, 100, 10, 64, 0]),
            ('hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)', [64, 100, 10, 64, 1, 7, 3, 1]),
            ('hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)', [64, 250, 15, 64, 2, 7, 3, 1, 13, 5, 0]),
            ('hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)', [64, 100, 10, 64, 1, 7, 1 << 64, 1]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(market_bundle_prefix[:remaining_budget])
    if 'checkInterface(bytes4,uint256)' in source['methodIdentifiers']:
        check_iface_prefix = [
            ('checkInterface(bytes4,uint256)', [0x01ffc9a7 << 224, 7]),
            ('checkInterface(bytes4,uint256)', [0x7965db0b << 224, 11]),
            ('checkInterface(bytes4,uint256)', [0x12345678 << 224, 19]),
            ('checkInterface(bytes4,uint256)', [(0x01ffc9a7 << 224) | 1, 23]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(check_iface_prefix[:remaining_budget])
    if 'royaltyAndHolderCheck(uint256,uint256)' in source['methodIdentifiers']:
        royalty_prefix = [
            ('royaltyAndHolderCheck(uint256,uint256)', [0, 10000]),
            ('royaltyAndHolderCheck(uint256,uint256)', [1, 25000]),
            ('royaltyAndHolderCheck(uint256,uint256)', [2, 50000]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(royalty_prefix[:remaining_budget])
    if 'dequeAndBitmapStep(string,uint256)' in source['methodIdentifiers']:
        deque_prefix = [
            ('dequeAndBitmapStep(string,uint256)', [64, 5, 5, 0x616c706861 << 216]),
            ('dequeAndBitmapStep(string,uint256)', [64, 14, 0]),
            ('dequeAndBitmapStep(string,uint256)', [64, 9, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232]),
            ('dequeAndBitmapStep(string,uint256)', [64, 3, 4, 0x62657461 << 224]),
            ('dequeAndBitmapStep(string,uint256)', [96, 1, 0]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(deque_prefix[:remaining_budget])
    if 'slotAndShortStringStep(string,uint32,uint32,uint256)' in source['methodIdentifiers']:
        slot_short_prefix = [
            ('vaultLabel()', []),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 12, 3, 0, 5, 0x616c706861 << 216]),
            ('vaultLabel()', []),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 6, 4, 1, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232]),
            ('vaultLabel()', []),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 18, 2, 0, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232]),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 8, 2, 99, 0]),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 1 << 32, 2, 0, 0]),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [96, 8, 2, 0, 0]),
            ('slotAndShortStringStep(string,uint32,uint32,uint256)', [128, 9, 1, 2, 4, 0x62657461 << 224]),
            ('vaultLabel()', []),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(slot_short_prefix[:remaining_budget])
    if 'trancheHistorySnapshot(uint256)' in source['methodIdentifiers']:
        tranche_hist_prefix = [
            ('trancheHistorySnapshot(uint256)', [0]),
            ('trancheHistorySnapshot(uint256)', [1]),
            ('trancheHistorySnapshot(uint256)', [2]),
            ('trancheHistorySnapshot(uint256)', [97]),
            ('trancheHistorySnapshot(uint256)', [98]),
            ('trancheHistorySnapshot(uint256)', [99]),
            ('trancheHistorySnapshot(uint256)', [3]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(tranche_hist_prefix[:remaining_budget])
    if 'lookupWindow(uint48,uint256)' in source['methodIdentifiers']:
        lookup_window_prefix = [
            ('lookupWindow(uint48,uint256)', [1, 0]),
            ('lookupWindow(uint48,uint256)', [3, 0]),
            ('lookupWindow(uint48,uint256)', [6, 1]),
            ('lookupWindow(uint48,uint256)', [4, 97]),
            ('lookupWindow(uint48,uint256)', [5, 98]),
            ('lookupWindow(uint48,uint256)', [5, 99]),
            ('lookupWindow(uint48,uint256)', [1 << 48, 0]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(lookup_window_prefix[:remaining_budget])
    if 'quoteTickRoundtrip(uint256,uint256)' in source['methodIdentifiers']:
        quote_tick_prefix = [
            ('quoteTickRoundtrip(uint256,uint256)', [0, 8]),
            ('quoteTickRoundtrip(uint256,uint256)', [3368, 8]),
            ('quoteTickRoundtrip(uint256,uint256)', [3376, 8]),
            ('quoteTickRoundtrip(uint256,uint256)', [6744, 8]),
            ('quoteTickRoundtrip(uint256,uint256)', [1200, 24]),
            ('quoteTickRoundtrip(uint256,uint256)', [4800, 0]),
            ('quoteTickRoundtrip(uint256,uint256)', [6745, 8]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(quote_tick_prefix[:remaining_budget])
    if OFFER_MEM_SIG in source['methodIdentifiers']:
        offer_prefix = [
            ('DOMAIN_SEPARATOR()', []),
            (OFFER_MEM_SIG, _encode_offer_call([500])),
            (OFFER_MEM_SIG, _encode_offer_call(
                [750],
                collateral_params=((0xA1, 8500, 1500, 0xB1),),
                cb_len=5,
                cb_words=(0x1122334455 << 216,),
            )),
            (OFFER_MEM_SIG, _encode_offer_call(
                [900],
                buy=0,
                reduce_only=1,
                collateral_params=((0xA1, 8000, 1200, 0xB1), (0xA2, 9000, 1800, 0xB2)),
                cb_len=35,
                cb_words=(0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232),
            )),
            (OFFER_MEM_SIG, _encode_offer_call([500], max_units=1 << 128)),
            (OFFER_MEM_SIG, _encode_offer_call([500], buy=2)),
            (OFFER_CD_SIG, _encode_offer_call([600, 0x9999])),
            (OFFER_CD_SIG, _encode_offer_call(
                [850, 0xAAAA],
                buy=0,
                reduce_only=1,
                collateral_params=((0xA1, 8200, 1400, 0xB1), (0xA2, 8800, 1600, 0xB2)),
                cb_len=4,
                cb_words=(0xDEADBEEF << 224,),
            )),
            (OFFER_CD_SIG, _encode_offer_call([600, 0x9999], collateral_params=((0xA1, 8200, 1400, 1 << 160),))),
            (OFFER_CD_SIG, _encode_offer_call([600, 0x9999], cb_len=65)),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(offer_prefix[:remaining_budget])
    if 'decodeMixedPayload(bytes,uint256)' in source['methodIdentifiers']:
        ratifier_prefix = [
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(
                900,
                min_rate=950,
                allowed_taker=0x3005,
                active=0,
                tag=0x11223344 << 224,
                weights=(5, 15, 25),
                extra_len=35,
                extra_words=(0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232),
                label_len=6,
                label_words=(0x70617265746f << 208,),
            )),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1500, min_rate=1200)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000, active=2)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000, allowed_taker=1 << 160)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000, tag=(0xAABBCCDD << 224) | 1)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000, raw_len=64)),
            ('decodeMixedPayload(bytes,uint256)', _encode_mixed_payload_call(1000, extra_len=65)),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0, 600, min_rate=500, allowed_taker=0, leaf_index=0, proof=())),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(
                0,
                850,
                min_rate=700,
                allowed_taker=0,
                leaf_index=1,
                proof=(0x1111, 0x2222),
                collateral_params=((0xA1, 8200, 1400, 0xB1),),
            )),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0, 400, min_rate=500)),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0, 600, min_rate=500, allowed_taker=0x9999)),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0xDEAD, 600, min_rate=500)),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0, 600, min_rate=500, allowed_taker=1 << 160)),
            (RATIFY_OFFER_CD_SIG, _encode_ratify_offer_call(0, 600, min_rate=500, cb_len=64)),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(ratifier_prefix[:remaining_budget])
    if 'voteWindow(uint256,uint256)' in source['methodIdentifiers']:
        votes_prefix = [
            ('latestTotalCheckpoint()', []),
            ('pendingDefaultAdminView()', []),
            ('checkpoints(address,uint32)', [0x4000, 0]),
            ('checkpoints(address,uint32)', [0x4001, 0]),
            ('checkpoints(address,uint32)', [0x4000, 99]),
            ('checkpoints(address,uint32)', [1 << 160, 0]),
            ('checkpoints(address,uint32)', [0x4000, 1 << 32]),
            ('voteWindow(uint256,uint256)', [0, 0]),
            ('voteWindow(uint256,uint256)', [100, 1]),
            ('voteWindow(uint256,uint256)', [250, 0]),
            ('voteWindow(uint256,uint256)', [1, 97]),
            ('voteWindow(uint256,uint256)', [1, 98]),
            ('voteWindow(uint256,uint256)', [1, 99]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(votes_prefix[:remaining_budget])
    if 'probeBuiltins(uint256,uint256)' in source['methodIdentifiers']:
        getters_prefix = [
            ('VAULT_NAME()', []),
            ('tiers(uint256)', [3]),
            ('tiers(uint256)', [0]),
            ('asset()', []),
            ('currentEpoch()', []),
            ('history(uint256)', [0]),
            ('history(uint256)', [99]),
            ('positions(address)', [0x3000]),
            ('probeBuiltins(uint256,uint256)', [0, 10]),
            ('probeBuiltins(uint256,uint256)', [96, 10]),
            ('probeBuiltins(uint256,uint256)', [97, 10]),
            ('probeBuiltins(uint256,uint256)', [98, 10]),
            ('probeBuiltins(uint256,uint256)', [99, 10]),
            ('probeBuiltins(uint256,uint256)', [0, 77]),
            ('read()', []),
        ]
        remaining_budget = max(0, args.transactions - len(calls))
        calls.extend(getters_prefix[:remaining_budget])
    while len(calls) < args.transactions:
        name = rng.choice(names)
        if name == names[0]:
            call_args = [rng.choice([0, 1, (1 << args.argument_bits) - 1, rng.getrandbits(args.argument_bits)])]
        elif name == 'redeemRewards(bytes)':
            call_args = rng.choice([[32, 0], [32, 5, 0x1122334455 << 216], [32, 32, (1 << 256) - 1], [32, 33, 1], [64, 0]])
        elif name == 'inspectBytes(bytes,uint256)':
            tag = rng.choice([0, 1, 2, 3, 7, 19])
            call_args = rng.choice([[64, tag, 0], [64, tag, 5, 0xdeadbeef01 << 216], [64, tag, 32, (1 << 256) - 1], [64, tag, 33, 1], [64, tag, 1 << 64, 0], [1 << 64, tag, 0]])
        elif name == 'applyRounding(uint8,uint256)':
            call_args = [rng.choice([0, 1, 2, 3, 4, 255, 256]), rng.choice([0, 1, 7, 19, 999])]
        elif name == 'inspectStatic((uint128,uint64,bool),uint256)':
            call_args = rng.choice([[3, 5, 1, 10], [3, 5, 0, 10], [1 << 128, 5, 1, 10], [3, 5, 2, 10]])
        elif name == 'applyBundle((uint256,(uint256,uint64,bool)[],uint256[]),uint256)':
            call_args = rng.choice([
                [64, 0, 10, 96, 128, 0, 0],
                [64, 0, 10, 96, 224, 1, 7, 3, 1, 1, 11],
                [64, 1, 10, 96, 320, 2, 7, 3, 1, 13, 5, 1, 2, 11, 17],
                [64, 0, 10, 96, 224, 1, 7, 1 << 64, 1, 1, 11],
            ])
        elif name == 'inspectArraysAndStrings(uint256[],address[],string,uint256)':
            call_args = rng.choice([
                [128, 160, 192, 7, 0, 0, 0],
                [128, 192, 256, 11, 1, 100, 1, 0x1234, 5, 0x68656c6c6f << 216],
                [128, 224, 320, 19, 2, 100, 200, 2, 0x1111, 0x2222, 32, 0x41424344 << 224],
                [128, 192, 288, 23, 1, 100, 2, 0x1111, 0x2222, 0],
                [128, 192, 256, 29, 1, 100, 1, 1 << 160, 0],
                [128, 192, 256, 31, 1, 100, 1, 0x1234, 33, 1],
            ])
        elif name == 'inspectNarrowArray(uint64[],uint256)':
            call_args = rng.choice([
                [64, 3, 0],
                [64, 5, 2, 10, 25],
                [64, 7, 1, (1 << 64) - 1],
                [64, 9, 1, 1 << 64],
            ])
        elif name == 'inspectBytesMemory(bytes,bytes,string,uint256)':
            call_args = rng.choice([
                [128, 160, 192, 7, 0, 0, 0],
                [128, 192, 256, 11, 4, 0x11223344 << 224, 5, 0xdeadbeef01 << 216, 3, 0x616263 << 232],
                [128, 192, 288, 19, 32, (1 << 256) - 1, 33, 0x123456789abcdef0, 0xff << 248, 5, 0x68656c6c6f << 216],
                [128, 160, 192, 23, 65, 0, 0],
                [96, 160, 192, 29, 0, 0, 0],
                [128, 160, 192, 31, 0, 1 << 64, 0],
            ])
        elif name == 'concatStrings(string,string,uint256)':
            call_args = rng.choice([
                [96, 128, 0, 0, 0],
                [96, 160, 4, 5, 0x68656c6c6f << 216, 5, 0x776f726c64 << 216],
                [96, 160, 1, 5, 0x616c706861 << 216, 4, 0x62657461 << 224],
                [96, 160, 2, 6, 0x70617265746f << 208, 3, 0x63646f << 232],
                [96, 160, 3, 4, 0x69646c65 << 224, 0],
                [96, 160, 7, 4, 0x69646c65 << 224, 7, 0x7472616e636865 << 200],
            ])
        elif name == 'buildPayload(bytes,bytes,uint256)':
            call_args = rng.choice([
                [96, 160, 0, 4, 0x11223344 << 224, 2, 0xaabb << 240],
                [96, 128, 1, 0, 0],
                [96, 128, 2, 0, 0],
                [96, 160, 3, 5, 0xdeadbeef01 << 216, 3, 0x010203 << 232],
                [96, 128, 4, 0, 0],
                [96, 128, 9, 0, 6, 0xfeedfacecafe << 208],
            ])
        elif name == 'syncStorage(string,bytes,uint256)':
            call_args = rng.choice([
                [96, 128, 0, 0, 0],
                [96, 160, 0, 5, 0x616c706861 << 216, 4, 0x11223344 << 224],
                [96, 192, 1, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232, 33, 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20, 0xff << 248],
                [96, 160, 2, 4, 0x62657461 << 224, 3, 0xaabbcc << 232],
                [96, 128, 3, 0, 0],
                [96, 160, 4, 6, 0x70617265746f << 208, 0],
            ])
        elif name == 'hashMarketBundle((uint256,(uint256,uint64,bool)[]),uint256)':
            call_args = rng.choice([
                [64, 100, 10, 64, 0],
                [64, 100, 10, 64, 1, 7, 3, 1],
                [64, 250, 15, 64, 2, 7, 3, 1, 13, 5, 0],
                [64, 100, 10, 64, 1, 7, 1 << 64, 1],
            ])
        elif name == 'checkInterface(bytes4,uint256)':
            call_args = rng.choice([
                [0x01ffc9a7 << 224, 7],
                [0x7965db0b << 224, 11],
                [0x12345678 << 224, 19],
                [0xffffffff << 224, 29],
                [(0x01ffc9a7 << 224) | 1, 23],
            ])
        elif name == 'royaltyAndHolderCheck(uint256,uint256)':
            call_args = rng.choice([
                [0, 10000],
                [1, 25000],
                [2, 50000],
                [3, 75000],
            ])
        elif name == 'dequeAndBitmapStep(string,uint256)':
            call_args = rng.choice([
                [64, 5, 5, 0x616c706861 << 216],
                [64, 14, 0],
                [64, 9, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232],
                [64, 3, 4, 0x62657461 << 224],
                [64, 22, 6, 0x70617265746f << 208],
            ])
        elif name == 'slotAndShortStringStep(string,uint32,uint32,uint256)':
            call_args = rng.choice([
                [128, 12, 3, 0, 5, 0x616c706861 << 216],
                [128, 6, 4, 1, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232],
                [128, 15, 2, 0, 4, 0x62657461 << 224],
                [128, 18, 2, 0, 35, 0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232],
                [128, 8, 2, 99, 0],
                [128, 10, 5, 3, 0],
            ])
        elif name == 'trancheHistorySnapshot(uint256)':
            call_args = rng.choice([[0], [1], [2], [3], [4], [5], [97], [98], [99]])
        elif name == 'lookupWindow(uint48,uint256)':
            call_args = rng.choice([[0, 0], [1, 0], [3, 0], [5, 1], [8, 0], [2, 97], [2, 98], [2, 99], [1 << 48, 0]])
        elif name == 'quoteTickRoundtrip(uint256,uint256)':
            call_args = rng.choice([[0, 8], [1600, 8], [3368, 8], [3376, 8], [5000, 24], [6744, 8], [6745, 8], [2400, 0]])
        elif name == OFFER_MEM_SIG:
            call_args = rng.choice([
                _encode_offer_call([500]),
                _encode_offer_call([750], collateral_params=((0xA1, 8500, 1500, 0xB1),), cb_len=5, cb_words=(0x1122334455 << 216,)),
                _encode_offer_call([900], buy=0, reduce_only=1, collateral_params=((0xA1, 8000, 1200, 0xB1), (0xA2, 9000, 1800, 0xB2)), cb_len=35, cb_words=(0x4142434445464748494a4b4c4d4e4f505152535455565758595a303132333435, 0x363738 << 232)),
                _encode_offer_call([500], max_units=1 << 128),
            ])
        elif name == OFFER_CD_SIG:
            call_args = rng.choice([
                _encode_offer_call([600, 0x9999]),
                _encode_offer_call([850, 0xAAAA], buy=0, reduce_only=1, collateral_params=((0xA1, 8200, 1400, 0xB1), (0xA2, 8800, 1600, 0xB2)), cb_len=4, cb_words=(0xDEADBEEF << 224,)),
                _encode_offer_call([600, 0x9999], collateral_params=((0xA1, 8200, 1400, 1 << 160),)),
            ])
        elif name == 'decodeMixedPayload(bytes,uint256)':
            call_args = rng.choice([
                _encode_mixed_payload_call(1000),
                _encode_mixed_payload_call(900, min_rate=950, active=0, weights=(5, 15, 25)),
                _encode_mixed_payload_call(1500, min_rate=1200),
                _encode_mixed_payload_call(1000, active=2),
            ])
        elif name == RATIFY_OFFER_CD_SIG:
            call_args = rng.choice([
                _encode_ratify_offer_call(0, 600, min_rate=500, allowed_taker=0, leaf_index=0, proof=()),
                _encode_ratify_offer_call(0, 850, min_rate=700, allowed_taker=0, leaf_index=1, proof=(0x1111, 0x2222)),
                _encode_ratify_offer_call(0, 400, min_rate=500),
                _encode_ratify_offer_call(0xDEAD, 600, min_rate=500),
            ])
        elif name == 'checkpoints(address,uint32)':
            call_args = rng.choice([[0x4000, 0], [0x4001, 0], [0x4002, 0], [0x4000, 1], [0x4000, 99]])
        elif name == 'voteWindow(uint256,uint256)':
            call_args = rng.choice([[0, 0], [50, 0], [150, 1], [300, 0], [10, 97], [10, 98], [10, 99]])
        elif name == 'history(uint256)':
            call_args = [rng.choice([0, 1, 2, 99])]
        elif name == 'tiers(uint256)':
            call_args = [rng.choice([0, 1, 2, 3, 99])]
        elif name == 'positions(address)':
            call_args = [rng.choice([0x3000, 0x3001, 0x3002, 1 << 160])]
        elif name == 'isWhitelister(bool,address)':
            call_args = rng.choice([[1, 0x4000], [0, 0x4001], [2, 0x4000], [1, 1 << 160]])
        elif name == 'nonces(bool,address,address)':
            call_args = rng.choice([[1, 0x3000, 0x4000], [0, 0x3001, 0x4000], [2, 0x3000, 0x4000]])
        elif name == 'limits(address,uint256)':
            call_args = rng.choice([[0x3000, 0], [0x3000, 1], [0x3000, 2], [0x4000, 0], [1 << 160, 0]])
        elif name == 'probeBuiltins(uint256,uint256)':
            call_args = rng.choice([[0, 10], [1, 20], [96, 10], [97, 10], [98, 10], [99, 10], [0, 77]])
        else:
            call_args = []
        calls.append((name, call_args))
    if args.dirty_mappings:
        calls = [('read()', []), ('read()', []), ('change(uint256)', [7]),
                 ('fail()', []), ('read()', [])] + calls[5:]
    sender_rng = random.Random(args.seed)
    transaction_senders = [senders[index] if index < len(senders) else sender_rng.choice(senders)
                           for index in range(len(calls))]
    if args.dirty_mappings:
        transaction_senders[:5] = [senders[0], senders[0], senders[-1], senders[-1], senders[-1]]
    transactions = [{'id': str(index), 'function': name.split('(')[0], 'args': args,
        'sender': transaction_senders[index], 'target': account, 'value': '0x0',
        'timestamp': 1000000100 + index, 'blockNumber': 2 + index,
        'data': '0x' + source['methodIdentifiers'][name] + ''.join(format(arg, '064x') for arg in args)}
        for index, (name, args) in enumerate(calls)]
    adapters = {'source': EVMAdapter(output / 'A', [source_code], initial_storage=initial_storage),
        'model': DenoteAdapter(output / 'B', driver, account, initial_storage=initial_storage, identity=identity),
        'compiled': EVMAdapter(output / 'C', [compiled_code], initial_storage=initial_storage)}
    write_json(output / 'provenance.json', {
        'solcSha256': hashlib.sha256(solc_bin.read_bytes()).hexdigest(),
        'anvilVersion': command(['anvil', '--version']).strip(),
        'leanVersion': command(['lake', 'env', 'lean', '--version']).strip(),
        'sourceSha256': hashlib.sha256(source_text.encode()).hexdigest(),
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
        'variant': args.variant, 'seed': args.seed, 'transactionCount': args.transactions,
        'changePrefix': args.change_prefix, 'argumentBits': args.argument_bits, 'senderCount': args.senders, 'dirtyMappings': args.dirty_mappings,
        'evmVersion': evm_version, 'optimizerRuns': optimizer_runs})
    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'seed': args.seed, 'transactions': transactions, **result})
    if args.dirty_mappings and not result['divergences']:
        # Guarantee both bool normalization cases actually executed before accepting coverage.
        rows = result['observations']['source']
        for index, expected in ((0, 1), (1, 0)):
            row = rows[index]
            if row['status'] != 'ok' or len(row['data']) != 258 or int(row['data'][66:130], 16) != expected:
                raise HarnessError('dirty mapping prefix did not observe the required bool values')
    if result['divergences']:
        reduced = shrink_sequence(transactions,
            lambda candidate: replay_three_routes(candidate, adapters)['divergences'],
            max_attempts=args.shrink_attempts)
        write_json(output / 'reduced.json', reduced)
        raise HarnessError(f"stateful A/B/C divergence: {output / 'campaign.json'}")
    print(f'{args.transactions} real A/B/C transactions agree; discovery and replay: {output}')


if __name__ == '__main__':
    main()
