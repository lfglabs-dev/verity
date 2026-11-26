"""Three-route Anvil differential check for checked/hoisted/effectful external-call,
event, and custom-error arguments (`CheckedArgumentSequence.sol`), under both via-IR
and legacy solc 0.8.34 pipelines.

Compares:
  Route A: solc 0.8.34 (viaIR=true and viaIR=false, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`CheckedArgumentSequenceModel.lean` / `CheckedArgumentLegacyModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_checked_arguments
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
FUNCTIONS = [
    'callChecked(address,uint256,uint256)',
    'callOverflow(address,uint256)',
    'callDynamic(address,bytes,uint256)',
    'callVoid(address,uint256,uint256)',
    'emitMeasured(uint256,uint256)',
    'revertField(uint256)',
    'revertNamedField()',
    'callEffectfulPost(address,uint256)',
    'callEffectfulPre(address,uint256)',
    'revertEffectful(uint256)',
    'requireEffectful(bool,uint256)',
    'seedWeight(uint256)',
    'read()',
]


def address(nonce: int) -> str:
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def run_pipeline(root: Path, output: Path, via_ir: bool, driver: Path):
    fixture = root / 'Contracts/SolidityImportSmoke/CheckedArgumentSequence.sol'
    word_oracle = root / 'Contracts/SolidityImportSmoke/InterfaceWordStaticCallOracle.sol'
    void_responder = root / 'Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol'
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
                word_oracle.name: {'content': word_oracle.read_text()},
                void_responder.name: {'content': void_responder.read_text()},
            },
            'settings': {
                **settings,
                'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}},
            },
        },
        fixture.parent,
        output / 'solc',
        solc=SOLC,
    )['contracts']
    caller_evm = compiled[fixture.name]['CheckedArgumentFixture']['evm']
    identifiers = caller_evm['methodIdentifiers']
    selectors = [int(identifiers[sig], 16) for sig in FUNCTIONS]
    write_json(output / 'selectors.json', selectors)

    identity = ImplementationIdentity(driver, extra_inputs=[fixture, word_oracle, void_responder])
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
    caller = address(0)

    def make_tx(calls: list, block_base: int, sig: str, types: list[str], values: list):
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
            'blockNumber': block_base + idx,
        })

    # Part 1: Staticcall, event, custom-error, and effectful-arg calls against WordStaticOracle.
    # A full mask folds selector + calldata size + every argument word in exact order.
    word_mask = (1 << 256) - 1
    oracle_specs = [
        (0, False, 32, word_mask),               # 1: ok folding oracle
        (0xDEADBEEF << 224, True, 4, 0),         # 2: reverting oracle
    ]
    oracle_bin = compiled[word_oracle.name]['WordStaticOracle']['evm']['bytecode']['object']
    oracle_accounts = [address(i + 1) for i in range(len(oracle_specs))]
    oracle_ok, oracle_rev = oracle_accounts
    oracle_bytecodes = [
        '0x' + oracle_bin + encode(['uint256', 'bool', 'uint256', 'uint256'], list(spec)).hex()
        for spec in oracle_specs
    ]
    oracle_initial = [
        (acct, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for acct, spec in zip(oracle_accounts, oracle_specs, strict=True)
        for slot, val in enumerate(spec)
    ]

    static_calls = []
    block_base = len(oracle_specs) + 2
    make_tx(static_calls, block_base, 'seedWeight(uint256)', ['uint256'], [42])
    # Checked staticcall arguments: ok, ValueTooWide before underflow, underflow before call, reverting target.
    make_tx(static_calls, block_base, 'callChecked(address,uint256,uint256)',
            ['address', 'uint256', 'uint256'], [oracle_ok, 17, 9])
    make_tx(static_calls, block_base, 'callChecked(address,uint256,uint256)',
            ['address', 'uint256', 'uint256'], [oracle_ok, 1 << 104, 0])
    make_tx(static_calls, block_base, 'callChecked(address,uint256,uint256)',
            ['address', 'uint256', 'uint256'], [oracle_ok, 5, 0])
    make_tx(static_calls, block_base, 'callChecked(address,uint256,uint256)',
            ['address', 'uint256', 'uint256'], [oracle_rev, 5, 2])
    # Checked overflow argument before call.
    make_tx(static_calls, block_base, 'callOverflow(address,uint256)',
            ['address', 'uint256'], [oracle_ok, 7])
    make_tx(static_calls, block_base, 'callOverflow(address,uint256)',
            ['address', 'uint256'], [oracle_ok, (1 << 256) - 1])
    # Dynamic bytes + checked downcast.
    make_tx(static_calls, block_base, 'callDynamic(address,bytes,uint256)',
            ['address', 'bytes', 'uint256'], [oracle_ok, b'\x01\x02\x03', 99])
    make_tx(static_calls, block_base, 'callDynamic(address,bytes,uint256)',
            ['address', 'bytes', 'uint256'], [oracle_ok, bytes(range(35)), 1 << 104])
    # Effectful external-call argument order: (a, a++) and (a, ++a).
    make_tx(static_calls, block_base, 'callEffectfulPost(address,uint256)',
            ['address', 'uint256'], [oracle_ok, 3])
    make_tx(static_calls, block_base, 'callEffectfulPre(address,uint256)',
            ['address', 'uint256'], [oracle_ok, 3])
    make_tx(static_calls, block_base, 'callEffectfulPost(address,uint256)',
            ['address', 'uint256'], [oracle_ok, (1 << 256) - 1])
    # Checked event arguments + storage read: ok, overflow, underflow.
    make_tx(static_calls, block_base, 'emitMeasured(uint256,uint256)', ['uint256', 'uint256'], [10, 5])
    make_tx(static_calls, block_base, 'emitMeasured(uint256,uint256)', ['uint256', 'uint256'], [(1 << 256) - 1, 1])
    make_tx(static_calls, block_base, 'emitMeasured(uint256,uint256)', ['uint256', 'uint256'], [43, 0])
    # Custom-error arguments: checked storage expr, named storage member, effectful snapshot, eager require.
    make_tx(static_calls, block_base, 'revertField(uint256)', ['uint256'], [5])
    make_tx(static_calls, block_base, 'revertField(uint256)', ['uint256'], [(1 << 256) - 1])
    make_tx(static_calls, block_base, 'revertNamedField()', [], [])
    make_tx(static_calls, block_base, 'revertEffectful(uint256)', ['uint256'], [10])
    make_tx(static_calls, block_base, 'requireEffectful(bool,uint256)', ['bool', 'uint256'], [True, 10])
    make_tx(static_calls, block_base, 'requireEffectful(bool,uint256)', ['bool', 'uint256'], [False, 10])
    make_tx(static_calls, block_base, 'read()', [], [])

    static_env = {
        'program': 'word-static-oracle-v1',
        'accounts': [str(int(a, 16)) for a in oracle_accounts],
        'emptyAccounts': [str(int(EMPTY, 16))],
        'gas': '1000000',
    }
    static_adapters = {
        'source': EVMAdapter(output / 'static-A', [caller_a, *oracle_bytecodes], oracle_initial),
        'model': DenoteAdapter(output / 'static-B', driver, caller, oracle_initial, identity=identity,
                               byte_call_environment=static_env),
        'compiled': EVMAdapter(output / 'static-C', [caller_c, *oracle_bytecodes], oracle_initial),
    }
    static_result = replay_three_routes(static_calls, static_adapters)
    write_json(output / 'static-campaign.json', {'transactions': static_calls, **static_result})
    if static_result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in checked-arguments (viaIR={via_ir}, static): {output / 'static-campaign.json'}")
    if {r['status'] for r in static_result['observations']['source']} != {'ok', 'revert'}:
        raise HarnessError('checked-arguments static campaign must exercise both ok and revert paths')

    # Part 2: Void external call with checked arguments against RecordingCallResponder.
    resp_specs = [
        (0, False, 0),                           # 1: ok responder (records call count + calldata words)
        (0xCAFEBABE << 224, True, 4),            # 2: reverting responder
    ]
    resp_evm = compiled[void_responder.name]['RecordingCallResponder']['evm']
    resp_bin = resp_evm['bytecode']['object']
    resp_runtime = '0x' + resp_evm['deployedBytecode']['object']
    resp_accounts = [address(i + 1) for i in range(len(resp_specs))]
    resp_ok, resp_rev = resp_accounts
    resp_bytecodes = [
        '0x' + resp_bin + encode(['uint256', 'bool', 'uint256'], list(spec)).hex()
        for spec in resp_specs
    ]
    resp_initial = [
        (acct, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for acct, spec in zip(resp_accounts, resp_specs, strict=True)
        for slot, val in enumerate(spec)
    ]

    void_calls = []
    void_base = len(resp_specs) + 2
    make_tx(void_calls, void_base, 'callVoid(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [resp_ok, 12, 34])
    make_tx(void_calls, void_base, 'callVoid(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [resp_ok, 1 << 104, (1 << 256) - 1])
    make_tx(void_calls, void_base, 'callVoid(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [resp_ok, 12, (1 << 256) - 1])
    make_tx(void_calls, void_base, 'callVoid(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [resp_rev, 12, 34])
    make_tx(void_calls, void_base, 'callVoid(address,uint256,uint256)', ['address', 'uint256', 'uint256'], [EMPTY, 12, 34])

    void_env = {
        'program': 'recording-call-responder-v1',
        'accounts': [str(int(a, 16)) for a in resp_accounts],
        'emptyAccounts': [str(int(EMPTY, 16))],
        'gas': '1000000',
    }
    void_adapters = {
        'source': EVMAdapter(output / 'void-A', [caller_a, *resp_bytecodes], resp_initial),
        'model': DenoteAdapter(output / 'void-B', driver, caller, resp_initial, identity=identity,
                               byte_call_environment=void_env,
                               account_code=[(acct, resp_runtime) for acct in resp_accounts]),
        'compiled': EVMAdapter(output / 'void-C', [caller_c, *resp_bytecodes], resp_initial),
    }
    void_result = replay_three_routes(void_calls, void_adapters)
    identity.verify()
    write_json(output / 'void-campaign.json', {'transactions': void_calls, **void_result})
    if void_result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in checked-arguments (viaIR={via_ir}, void): {output / 'void-campaign.json'}")
    if {r['status'] for r in void_result['observations']['source']} != {'ok', 'revert'}:
        raise HarnessError('checked-arguments void campaign must exercise both ok and revert paths')
    return len(static_calls) + len(void_calls)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='checked-arguments-', dir=root / '.lake')).resolve()

    n_ir = run_pipeline(
        root, output / 'via-ir', True,
        root / 'Contracts/SolidityImportSmoke/CheckedArgumentSequenceModel.lean',
    )
    n_legacy = run_pipeline(
        root, output / 'legacy', False,
        root / 'Contracts/SolidityImportSmoke/CheckedArgumentLegacyModel.lean',
    )
    print(f"Anvil 3-route A/B/C PASS: via-IR {n_ir}/{n_ir} + legacy {n_legacy}/{n_legacy} transactions agree bit-for-bit ({output})")


if __name__ == '__main__':
    main()
