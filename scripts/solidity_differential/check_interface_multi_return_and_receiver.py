"""Three-route Anvil differential check for multi-return typed-interface staticcalls
and general receiver expressions (`InterfaceMultiReturnAndReceiver.sol`).

Compares:
  Route A: solc 0.8.34 (viaIR, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`InterfaceMultiReturnAndReceiverModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_interface_multi_return_and_receiver
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
SETTINGS = {
    'evmVersion': 'osaka',
    'viaIR': True,
    'optimizer': {'enabled': True, 'runs': 466},
    'metadata': {'bytecodeHash': 'none'},
}
FUNCTIONS = [
    'configure(address,uint256,address,address)',
    'readStatusDecl(address)',
    'readStatusAssign(address)',
    'readStatusDirect(address)',
    'readStatusElided(address)',
    'readStatusDiscarded(address)',
    'readQuote(address,uint256)',
    'probeViaHelper(uint256,uint256)',
    'probeViaFactory(address,uint256,uint256)',
    'probeViaState(uint256)',
    'probeViaConditional(bool,uint256,uint256)',
    'statusViaHelper(uint256)',
]


def address(nonce: int) -> str:
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/InterfaceMultiReturnAndReceiver.sol'
    oracle = root / 'Contracts/SolidityImportSmoke/MultiWordStaticOracle.sol'
    driver = root / 'Contracts/SolidityImportSmoke/InterfaceMultiReturnAndReceiverModel.lean'
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='interface-multi-return-', dir=root / '.lake')).resolve()

    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                fixture.name: {'content': fixture.read_text()},
                oracle.name: {'content': oracle.read_text()},
            },
            'settings': {
                **SETTINGS,
                'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
            },
        },
        fixture.parent,
        output / 'solc',
        solc=SOLC,
    )['contracts']
    caller_evm = compiled[fixture.name]['InterfaceMultiReturnAndReceiver']['evm']
    identifiers = caller_evm['methodIdentifiers']
    selectors = [int(identifiers[sig], 16) for sig in FUNCTIONS]
    write_json(output / 'selectors.json', selectors)

    identity = ImplementationIdentity(driver, extra_inputs=[fixture, oracle])
    command(
        ['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
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
        solc=SOLC,
    )
    objects = list(compiled_yul['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled Yul object')

    caller_a = '0x' + caller_evm['bytecode']['object']
    caller_c = '0x' + objects[0]['evm']['bytecode']['object']
    mock_bin = compiled[oracle.name]['MultiWordStaticOracle']['evm']['bytecode']['object']

    caller = address(0)
    # Deterministic oracle addresses (deployed at nonces 1..12).
    target_a_addr = address(9)
    target_b_addr = address(10)
    target_a_int = int(target_a_addr, 16)
    target_b_int = int(target_b_addr, 16)

    # (w0, w1, w2, failed, length, mask)
    oracle_specs = [
        (42, 1, 0, False, 64, 0),                                   # 1: srcGood (uint256=42, bool=true)
        (42, 2, 0, False, 64, 0),                                   # 2: srcDirtyBool (bool=2 -> revert empty)
        (42, 1, 0, False, 63, 0),                                   # 3: srcShort63 (63 bytes -> revert empty)
        (99, 0, 777, False, 96, 0),                                 # 4: srcExtra96 (extra word ignored)
        (0xDEADBEEF << 224, 0, 0, True, 4, 0),                      # 5: srcReverts (forwards 0xdeadbeef)
        (100, 1, target_a_int, False, 96, 0xFF),                    # 6: srcQuoteGood (valid uint16, bool, addr; folds arg)
        (0x10000, 1, target_a_int, False, 96, 0),                   # 7: srcQuoteDirtyU16 (dirty uint16 -> revert empty)
        (5, 1, (1 << 160) + 3, False, 96, 0),                       # 8: srcQuoteDirtyAddr (dirty addr -> revert empty)
        (31, 0, 0, False, 32, 0xFFFF),                              # 9: targetA (probe returns calldata-dependent word)
        (52, 0, 0, False, 32, 0xFFFF),                              # 10: targetB (distinct calldata-dependent word)
        (target_a_int, 0, 0, False, 32, 0),                         # 11: factoryGood (returns targetA)
        ((1 << 160) + target_b_int, 0, 0, False, 32, 0),            # 12: factoryDirtyAddr (dirty addr -> revert empty)
    ]
    accounts = [address(i + 1) for i in range(len(oracle_specs))]
    src_good, src_dirty_bool, src_short_63, src_extra_96, src_reverts = accounts[0:5]
    src_quote_good, src_quote_dirty_u16, src_quote_dirty_addr = accounts[5:8]
    factory_good, factory_dirty_addr = accounts[10:12]

    oracle_bytecodes = [
        '0x' + mock_bin + encode(['uint256', 'uint256', 'uint256', 'bool', 'uint256', 'uint256'], list(spec)).hex()
        for spec in oracle_specs
    ]
    initial = [
        (acct, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for acct, spec in zip(accounts, oracle_specs, strict=True)
        for slot, val in enumerate(spec)
    ]

    calls = []

    def add(sig: str, types: list[str], values: list):
        idx = len(calls)
        encoded = encode(types, values)
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        calls.append({
            'id': str(idx),
            'function': sig[:sig.index('(')],
            'args': words,
            'sender': SENDER,
            'target': caller,
            'data': '0x' + identifiers[sig] + encoded.hex(),
            'value': '0x0',
            'timestamp': 1000000100 + idx,
            'blockNumber': len(oracle_specs) + 2 + idx,
        })

    # Seed state variables and mappings for helper/state/conditional receivers.
    add('configure(address,uint256,address,address)',
        ['address', 'uint256', 'address', 'address'],
        [target_a_addr, 7, target_b_addr, src_good])

    # Multi-return `(uint256, bool)` across decl, assign, direct return, elided, discarded.
    add('readStatusDecl(address)', ['address'], [src_good])
    add('readStatusAssign(address)', ['address'], [src_good])
    add('readStatusDirect(address)', ['address'], [src_good])
    add('readStatusElided(address)', ['address'], [src_good])
    add('readStatusDiscarded(address)', ['address'], [src_good])
    add('readStatusDirect(address)', ['address'], [src_extra_96])

    # Exact Solidity ABI decoding rejections & revert forwarding on multi-return staticcalls.
    add('readStatusDecl(address)', ['address'], [src_dirty_bool])
    add('readStatusElided(address)', ['address'], [src_dirty_bool])
    add('readStatusDiscarded(address)', ['address'], [src_dirty_bool])
    add('readStatusDecl(address)', ['address'], [src_short_63])
    add('readStatusDecl(address)', ['address'], [EMPTY])
    add('readStatusDecl(address)', ['address'], [src_reverts])

    # 3-tuple `(uint16, bool, address)` with arguments and per-word ABI bounds.
    add('readQuote(address,uint256)', ['address', 'uint256'], [src_quote_good, 5])
    add('readQuote(address,uint256)', ['address', 'uint256'], [src_quote_good, 19])
    add('readQuote(address,uint256)', ['address', 'uint256'], [src_quote_dirty_u16, 5])
    add('readQuote(address,uint256)', ['address', 'uint256'], [src_quote_dirty_addr, 5])

    # General receiver expressions: internal helper, chained factory staticcall, state var, conditional.
    add('probeViaHelper(uint256,uint256)', ['uint256', 'uint256'], [7, 10])
    add('probeViaFactory(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [factory_good, 1, 10])
    add('probeViaFactory(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [factory_dirty_addr, 1, 10])
    add('probeViaState(uint256)', ['uint256'], [10])
    add('probeViaConditional(bool,uint256,uint256)', ['bool', 'uint256', 'uint256'], [True, 7, 10])
    add('probeViaConditional(bool,uint256,uint256)', ['bool', 'uint256', 'uint256'], [False, 7, 10])
    add('statusViaHelper(uint256)', ['uint256'], [7])

    environment = {
        'program': 'multi-word-static-oracle-v1',
        'accounts': [str(int(a, 16)) for a in accounts],
        'emptyAccounts': [str(int(EMPTY, 16))],
        'gas': '1000000',
    }
    adapters = {
        'source': EVMAdapter(output / 'A', [caller_a, *oracle_bytecodes], initial),
        'model': DenoteAdapter(output / 'B', driver, caller, initial, identity=identity,
                               byte_call_environment=environment),
        'compiled': EVMAdapter(output / 'C', [caller_c, *oracle_bytecodes], initial),
    }

    result = replay_three_routes(calls, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': calls, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in interface multi-return & receiver: {output / 'campaign.json'}")
    statuses = {row['status'] for row in result['observations']['source']}
    if statuses != {'ok', 'revert'}:
        raise HarnessError('interface multi-return campaign must exercise both ok and revert paths')
    print(f"Anvil 3-route A/B/C PASS: {len(calls)}/{len(calls)} transactions agree bit-for-bit ({output})")


if __name__ == '__main__':
    main()
