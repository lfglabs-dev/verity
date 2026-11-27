"""Three-route Anvil differential check for R7: OpenZeppelin v5 `LowLevelCall.returnData()`
and `Address.functionCall` / `Address.functionCallWithValue` / `Address.functionStaticCall`.

Compares:
  Route A: solc 0.8.34 (viaIR, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`LowLevelReturnDataModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_low_level_returndata
 or: python3 scripts/solidity_differential/check_low_level_returndata.py
"""
from __future__ import annotations

from pathlib import Path
import sys
import tempfile

if __package__ in (None, ''):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from solidity_differential.anvil import Anvil, SequenceAdapter as EVMAdapter
from solidity_differential.denote import SequenceAdapter as DenoteAdapter
from solidity_differential.engine import HarnessError, SOLC, command, solc_compile, write_json
from solidity_differential.identity import ImplementationIdentity
from solidity_differential.stateful import replay_three_routes

EMPTY = '0x' + '00' * 19 + '77'

FUNCTIONS = [
    'callRawBytes(address,bytes)',
    'callDecodeWord(address,bytes)',
    'callWithValueDecode(address,bytes,uint256)',
    'callDiscard(address,bytes)',
    'staticCallRawBytes(address,bytes)',
    'staticCallDecodeWord(address,bytes)',
    'directReturnData(address,bytes)',
    'directReturnDataLength(address,bytes)',
    'readState()',
]

RESPONDER_SOURCE = """// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock compiled by solc only (never imported).
contract LowLevelR7Responder {
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
    (77, False, 37, False),        # 1: stateful call returning 37 unaligned bytes
    (0, False, 0, False),          # 2: stateful call returning empty bytes (has code -> succeeds)
    (0xdeadbeef, True, 36, False), # 3: stateful call reverting with 36-byte payload (bubbleRevert)
    (0, True, 0, False),           # 4: stateful call reverting with empty payload (FailedCall)
    (200, False, 32, True),        # 5: static-safe responder returning 1 word (200 + calldata.len)
    (333, False, 5, True),         # 6: static-safe responder returning 5 unaligned bytes
    (0xcafe, True, 20, True),      # 7: static-safe responder reverting with 20-byte payload (bubbleRevert)
    (0, True, 0, True),            # 8: static-safe responder reverting with empty payload (FailedCall)
]


def u256_bytes(v: int) -> bytes:
    return int(v).to_bytes(32, 'big')


def addr_int(addr: str) -> int:
    return int(addr, 16)


def encode_addr_bytes(addr: str, payload: bytes) -> bytes:
    padded = payload + b'\x00' * ((32 - len(payload) % 32) % 32)
    return u256_bytes(addr_int(addr)) + u256_bytes(64) + u256_bytes(len(payload)) + padded


def encode_addr_bytes_u256(addr: str, payload: bytes, val: int) -> bytes:
    padded = payload + b'\x00' * ((32 - len(payload) % 32) % 32)
    return (u256_bytes(addr_int(addr)) + u256_bytes(96) + u256_bytes(val) +
            u256_bytes(len(payload)) + padded)


def main():
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/LowLevelReturnDataFixture.sol'
    driver = root / 'Contracts/SolidityImportSmoke/LowLevelReturnDataModel.lean'
    output = Path(tempfile.mkdtemp(prefix='r7-low-level-returndata-', dir=root / '.lake')).resolve()

    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                'LowLevelReturnDataFixture.sol': {'content': fixture.read_text()},
                'LowLevelR7Responder.sol': {'content': RESPONDER_SOURCE},
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

    source_evm = compiled['LowLevelReturnDataFixture.sol']['LowLevelReturnDataFixture']['evm']
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
    mock_evm = compiled['LowLevelR7Responder.sol']['LowLevelR7Responder']['evm']
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
            raise HarnessError('failed to deploy LowLevelReturnDataFixture')
        caller = dep0['receipt']['contractAddress']
        accounts = []
        for code in responders:
            dep = node.transact({'from': sender, 'data': code, 'gas': hex(5000000)})
            if dep['receipt']['status'] != '0x1':
                raise HarnessError('failed to deploy LowLevelR7Responder')
            accounts.append(dep['receipt']['contractAddress'])

    initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, params in zip(accounts, RESPONDERS, strict=True)
        for slot, val in enumerate(params)
    ]

    transactions = []

    def add(sig: str, encoded: bytes):
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
            'timestamp': 1000000100 + idx,
            'blockNumber': len(RESPONDERS) + 2 + idx,
            'data': '0x' + sel + encoded.hex(),
        })

    # 1. Address.functionCall raw bytes: 32-byte, 37-byte unaligned, 0-byte (code>0), EOA (AddressEmptyCode),
    #    36-byte bubbleRevert, empty-revert FailedCall
    add('callRawBytes(address,bytes)', encode_addr_bytes(accounts[0], b'\x01\x02\x03'))
    add('callRawBytes(address,bytes)', encode_addr_bytes(accounts[1], b'\xaa\xbb\xcc\xdd\xee'))
    add('callRawBytes(address,bytes)', encode_addr_bytes(accounts[2], b'\xff'))
    add('callRawBytes(address,bytes)', encode_addr_bytes(EMPTY, b'\x01'))
    add('callRawBytes(address,bytes)', encode_addr_bytes(accounts[3], b'\x01\x02'))
    add('callRawBytes(address,bytes)', encode_addr_bytes(accounts[4], b'\x01'))

    # 2. abi.decode(Address.functionCall(...), (uint256)) + short-data revert
    add('callDecodeWord(address,bytes)', encode_addr_bytes(accounts[0], b'\x11\x22\x33\x44'))
    add('callDecodeWord(address,bytes)', encode_addr_bytes(accounts[2], b'\x11'))  # 0 bytes -> decode revert

    # 3. Address.functionCallWithValue: value == 0 succeeds, value > balance reverts InsufficientBalance
    add('callWithValueDecode(address,bytes,uint256)', encode_addr_bytes_u256(accounts[0], b'\x01\x02', 0))
    add('callWithValueDecode(address,bytes,uint256)', encode_addr_bytes_u256(accounts[0], b'\x01', 50))

    # 4. Discarded Address.functionCall: success + bubbleRevert
    add('callDiscard(address,bytes)', encode_addr_bytes(accounts[2], b'\xaa\xbb'))
    add('callDiscard(address,bytes)', encode_addr_bytes(accounts[3], b'\xaa'))

    # 5. Address.functionStaticCall: raw bytes, abi.decode, EOA empty code, bubbleRevert, FailedCall,
    #    and staticcall to state-writing responder (fails with empty revert -> FailedCall)
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(accounts[5], b'\x01\x02\x03\x04\x05'))
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(accounts[6], b'\x99'))
    add('staticCallDecodeWord(address,bytes)', encode_addr_bytes(accounts[5], b'\x01\x02\x03'))
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(EMPTY, b'\x01'))
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(accounts[7], b'\x01'))
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(accounts[8], b'\x01'))
    add('staticCallRawBytes(address,bytes)', encode_addr_bytes(accounts[0], b'\x01'))

    # 6. Direct LowLevelCall.returnData() & LowLevelCall.returnData().length
    add('directReturnData(address,bytes)', encode_addr_bytes(accounts[1], b'\x10\x20'))
    add('directReturnData(address,bytes)', encode_addr_bytes(accounts[3], b'\x10'))
    add('directReturnDataLength(address,bytes)', encode_addr_bytes(accounts[6], b'\x10\x20\x30'))
    add('directReturnDataLength(address,bytes)', encode_addr_bytes(accounts[7], b'\x10'))
    add('readState()', b'')

    environment = {
        'program': 'r7-responder-v1',
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
        raise HarnessError(f"3-route A/B/C divergence in R7 LowLevelCall.returnData: {output / 'campaign.json'}")
    rows = result['observations']['source']
    if {r['status'] for r in rows} != {'ok', 'revert'}:
        raise HarnessError('R7 campaign must exercise both ok and revert transactions')
    print(f"R7 Anvil 3-route A/B/C PASS: {len(transactions)}/{len(transactions)} transactions agree bit-for-bit across solc, Lean Denote, and Verity Yul ({output})")


if __name__ == '__main__':
    main()
