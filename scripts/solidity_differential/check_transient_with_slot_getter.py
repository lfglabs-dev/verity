"""Three-route Anvil differential check for R9 + R9b:
- R9: EIP-7201 constant-slot storage-pointer getters (`$.slot := STORE_SLOT` and literal)
  inside functions accessing a `transient bool` state variable.
- R9b: Recognized structured OpenZeppelin v5 `LowLevelCall` helpers (`staticcallNoReturn`,
  `callNoReturn`, `returnDataSize`, `returnData`, `bubbleRevert`) and renamed equivalent
  helpers inside closures combining `transient bool` + `$.slot := CONST` + `Address.functionStaticCall`
  / `Address.functionCall`.

Compares:
  Route A: solc 0.8.34 (viaIR, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`TransientWithSlotGetterModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_transient_with_slot_getter
"""
from __future__ import annotations

from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes

FUNCTIONS = [
    'addDirect(uint256,address)',
    'addInBatch(uint256,uint256,address)',
    'addInBatchRevert(uint256,address)',
    'staticCallInBatch(address,bytes,address)',
    'callInBatch(address,bytes,address)',
    'renamedStaticCallInBatch(address,bytes,address)',
    'readState(address)',
]

USER_A = 0x100000000000000000000000000000000000a11c
USER_B = 0x200000000000000000000000000000000000b0b0
EMPTY = '0x' + '00' * 19 + '77'

RESPONDER_SOURCE = """// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock compiled by solc only (never imported).
contract R9bResponder {
    uint256 private value;
    bool private failed;
    uint256 private respLen;
    bool private staticSafe;
    uint256 private calls;
    uint256 private lastValue;
    uint256 private lastSize;

    constructor(uint256 v, bool f, uint256 n, bool s) {
        value = v;
        failed = f;
        respLen = n;
        staticSafe = s;
    }

    fallback() external payable {
        uint256 v = value;
        bool f = failed;
        uint256 n = respLen;
        if (staticSafe) {
            if (msg.value != 0) {
                assembly ("memory-safe") { revert(0, 0) }
            }
            uint256 word = v + msg.data.length;
            assembly ("memory-safe") {
                mstore(0, word)
                if f { revert(0, n) }
                return(0, n)
            }
        }
        uint256 word = v + msg.value + msg.data.length;
        if (f) {
            assembly ("memory-safe") {
                mstore(0, word)
                revert(0, n)
            }
        }
        calls += 1;
        lastValue = msg.value;
        lastSize = msg.data.length;
        assembly ("memory-safe") {
            mstore(0, word)
            return(0, n)
        }
    }
}
"""

# (value, failed, respLen, staticSafe)
RESPONDERS = [
    (100, False, 32, False),       # 0: stateful call returning 1 word (100 + msg.value + calldata.len)
    (0, False, 0, False),          # 1: stateful call returning empty bytes (abi.decode reverts)
    (0xdeadbeef, True, 36, False), # 2: stateful call reverting with 36-byte payload (bubbleRevert)
    (0, True, 0, False),           # 3: stateful call reverting with empty payload (FailedCall)
    (200, False, 32, True),        # 4: static-safe responder returning 1 word (200 + calldata.len)
    (0xcafe, True, 20, True),      # 5: static-safe responder reverting with 20-byte payload (bubbleRevert)
    (0, True, 0, True),            # 6: static-safe responder reverting with empty payload (FailedCall)
]


def u256_bytes(v: int) -> bytes:
    return int(v).to_bytes(32, 'big')


def addr_int(addr: str) -> int:
    return int(addr, 16)


def encode_words(args: list[int]) -> bytes:
    return b''.join(u256_bytes(a) for a in args)


def encode_addr_bytes_addr(target: str, payload: bytes, account: int) -> bytes:
    padded = payload + b'\x00' * ((32 - len(payload) % 32) % 32)
    return (u256_bytes(addr_int(target)) + u256_bytes(96) + u256_bytes(account) +
            u256_bytes(len(payload)) + padded)


def main():
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/TransientWithSlotGetterFixture.sol'
    driver = root / 'Contracts/SolidityImportSmoke/TransientWithSlotGetterModel.lean'
    output = Path(tempfile.mkdtemp(prefix='r9b-transient-slot-lowlevel-', dir=root / '.lake')).resolve()

    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                'TransientWithSlotGetterFixture.sol': {'content': fixture.read_text()},
                'R9bResponder.sol': {'content': RESPONDER_SOURCE},
            },
            'settings': {
                'evmVersion': 'osaka',
                'viaIR': True,
                'optimizer': {'enabled': True, 'runs': 466},
                'metadata': {'bytecodeHash': 'none'},
                'outputSelection': {'*': {'*': [
                    'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}},
            },
        },
        fixture.parent,
        output / 'solc',
        solc=SOLC,
    )['contracts']

    source_evm = compiled['TransientWithSlotGetterFixture.sol']['TransientWithSlotGetterFixture']['evm']
    selectors = [int(source_evm['methodIdentifiers'][sig], 16) for sig in FUNCTIONS]
    write_json(output / 'selectors.json', selectors)

    identity = ImplementationIdentity(driver, extra_inputs=[fixture])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            timeout=900, log=output / 'compile-model.log')
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
    )['contracts']['Model.yul']
    if len(compiled_yul) != 1:
        raise HarnessError('expected exactly one Verity-compiled Yul object')

    caller_a = '0x' + source_evm['bytecode']['object']
    caller_c = '0x' + next(iter(compiled_yul.values()))['evm']['bytecode']['object']
    mock_evm = compiled['R9bResponder.sol']['R9bResponder']['evm']
    mock_runtime = '0x' + mock_evm['deployedBytecode']['object']

    responders = [
        '0x' + mock_evm['bytecode']['object'] +
        b''.join(u256_bytes(int(x)) for x in params).hex()
        for params in RESPONDERS
    ]

    with Anvil(output / 'deploy-check') as node:
        sender = node.rpc('eth_accounts')[0]
        dep0 = node.transact({'from': sender, 'data': caller_a, 'gas': hex(5000000)})
        if dep0['receipt']['status'] != '0x1':
            raise HarnessError('failed to deploy TransientWithSlotGetterFixture')
        caller = dep0['receipt']['contractAddress']
        accounts = []
        for code in responders:
            dep = node.transact({'from': sender, 'data': code, 'gas': hex(5000000)})
            if dep['receipt']['status'] != '0x1':
                raise HarnessError('failed to deploy R9bResponder')
            accounts.append(dep['receipt']['contractAddress'])

    initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, params in zip(accounts, RESPONDERS, strict=True)
        for slot, val in enumerate(params)
    ]

    transactions = []

    def add_encoded(sig: str, encoded: bytes):
        idx = len(transactions)
        sel = source_evm['methodIdentifiers'][sig]
        name = sig[:sig.index('(')]
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        transactions.append({
            'id': str(idx),
            'function': name,
            'args': words,
            'sender': sender,
            'target': caller,
            'value': '0x0',
            'timestamp': 1000000200 + idx,
            'blockNumber': len(RESPONDERS) + 2 + idx,
            'data': '0x' + sel + encoded.hex(),
        })

    def add(sig: str, args: list[int]):
        add_encoded(sig, encode_words(args))

    # 1. R9 baseline: initial state, direct add, batch add, reverting batch add
    add('readState(address)', [USER_A])
    add('readState(address)', [USER_B])
    add('addDirect(uint256,address)', [10, USER_A])
    add('readState(address)', [USER_A])
    add('addInBatch(uint256,uint256,address)', [5, 7, USER_A])
    add('readState(address)', [USER_A])
    add('addInBatchRevert(uint256,address)', [999, USER_A])
    add('readState(address)', [USER_A])

    # 2. R9b: Address.functionStaticCall inside transient+slot-getter batch
    add_encoded('staticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[4], b'\x01\x02\x03', USER_A))
    add('readState(address)', [USER_A])
    # bubbleRevert, FailedCall, AddressEmptyCode, staticcall to state-writing responder
    add_encoded('staticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[5], b'\xaa', USER_A))
    add_encoded('staticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[6], b'\xbb', USER_A))
    add_encoded('staticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(EMPTY, b'\xcc', USER_A))
    add_encoded('staticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[0], b'\xdd', USER_A))
    add('readState(address)', [USER_A])

    # 3. R9b: Address.functionCall inside transient+slot-getter batch
    add_encoded('callInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[0], b'\x11\x22\x33\x44', USER_B))
    add('readState(address)', [USER_B])
    # short-return abi.decode revert, bubbleRevert, FailedCall, AddressEmptyCode
    add_encoded('callInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[1], b'\x11', USER_B))
    add_encoded('callInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[2], b'\x22', USER_B))
    add_encoded('callInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[3], b'\x33', USER_B))
    add_encoded('callInBatch(address,bytes,address)',
                encode_addr_bytes_addr(EMPTY, b'\x44', USER_B))
    add('readState(address)', [USER_B])

    # 4. R9b library-name independence + 1-arg bubbleRevert(bytes memory)
    add_encoded('renamedStaticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[4], b'\x55\x66', USER_B))
    add_encoded('renamedStaticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[5], b'\x77', USER_B))
    add_encoded('renamedStaticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(accounts[6], b'\x88', USER_B))
    add_encoded('renamedStaticCallInBatch(address,bytes,address)',
                encode_addr_bytes_addr(EMPTY, b'\x99', USER_B))

    # 5. Post-call direct + overflow rollback + final state check
    add('addDirect(uint256,address)', [1, USER_A])
    add('addInBatch(uint256,uint256,address)', [2**255, 1, USER_B])
    add('readState(address)', [USER_A])
    add('readState(address)', [USER_B])

    environment = {
        'program': 'r9b-responder-v1',
        'accounts': [str(int(a, 16)) for a in accounts],
        'emptyAccounts': [str(int(EMPTY, 16)), str(int(sender, 16))],
        'gas': '1000000',
    }
    adapters = {
        'source': EVMAdapter(output / 'A', [caller_a, *responders], initial),
        'model': DenoteAdapter(output / 'B', driver, caller, initial,
                               byte_call_environment=environment,
                               account_code=[(a, mock_runtime) for a in accounts]),
        'compiled': EVMAdapter(output / 'C', [caller_c, *responders], initial),
    }

    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in R9+R9b transient+slot-getter+LowLevelCall: {output / 'campaign.json'}")
    rows = result['observations']['source']
    if {r['status'] for r in rows} != {'ok', 'revert'}:
        raise HarnessError('R9+R9b campaign must exercise both ok and revert transactions')
    print(f"R9+R9b Anvil 3-route A/B/C PASS: {len(transactions)}/{len(transactions)} transactions agree bit-for-bit across solc, Lean Denote, and Verity Yul ({output})")


if __name__ == '__main__':
    main()
