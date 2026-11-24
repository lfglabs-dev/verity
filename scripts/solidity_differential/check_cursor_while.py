"""Three-route Anvil differential check for R8: `while (CursorLib.hasNext(cur))` over a
packed 32-bit lane memory struct cursor mutated by reference via `CursorLib.next(arr, cur)`.

Exercises:
  - 0-item cursor (0 iterations)
  - 1-item cursor
  - 8-item exact slot boundary
  - 11-item cursor crossing slot rollover `c.idx % 8 == 0`
  - 19-item cursor crossing two slot rollovers (`packedSlots[0] -> [1] -> [2]`)
  - `using CursorLib for Cursor` syntax (`cur.hasNext()`)
  - Struct-member fixed storage array (`bucket.words`)
  - External staticcall per cursor item (`IItemOracle(oracle).score(item)`) against `WordStaticOracle`
    with value + boolean flag (`allOdd`) accumulation

Compares:
  Route A: solc 0.8.34 (viaIR, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`CursorWhileModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_cursor_while
"""
from __future__ import annotations

from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes

EMPTY = '0x' + '00' * 19 + '77'

FUNCTIONS = [
    'pushItem(uint32)',
    'pushBucketItem(uint32)',
    'resetItems()',
    'sumPackedLocal()',
    'sumPackedUsingFor()',
    'sumBucketLocal()',
    'scanPackedWithOracle(address)',
    'scanNestedNamedArgs(uint256,address)',
    'scanNestedOracleCall(address)',
]

# WordStaticOracle constructor args: (value, failed, length, mask)
# Oracle 0: mask = 0xfffe (even mask), value = 1 -> result is ALWAYS odd (LSB = 1)
# Oracle 1: mask = 0xffff (full low 16 bits), value = 0 -> varies by item, flips `allOdd` to false
ORACLES = [
    (1, False, 32, 0xfffe),
    (0, False, 32, 0xffff),
]


def u256_bytes(v: int) -> bytes:
    return int(v).to_bytes(32, 'big')


def main():
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/CursorWhileFixture.sol'
    driver = root / 'Contracts/SolidityImportSmoke/CursorWhileModel.lean'
    oracle_sol = root / 'Contracts/SolidityImportSmoke/InterfaceWordStaticCallOracle.sol'
    output = Path(tempfile.mkdtemp(prefix='r8-cursor-while-', dir=root / '.lake')).resolve()

    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                'CursorWhileFixture.sol': {'content': fixture.read_text()},
                'InterfaceWordStaticCallOracle.sol': {'content': oracle_sol.read_text()},
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

    source_evm = compiled['CursorWhileFixture.sol']['CursorWhileFixture']['evm']
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
    oracle_evm = compiled['InterfaceWordStaticCallOracle.sol']['WordStaticOracle']['evm']
    oracle_runtime = '0x' + oracle_evm['deployedBytecode']['object']

    oracle_initcodes = [
        '0x' + oracle_evm['bytecode']['object'] +
        b''.join(u256_bytes(int(x)) for x in params).hex()
        for params in ORACLES
    ]

    with Anvil(output / 'deploy-check') as node:
        sender = node.rpc('eth_accounts')[0]
        dep0 = node.transact({'from': sender, 'data': caller_a, 'gas': hex(5000000)})
        if dep0['receipt']['status'] != '0x1':
            raise HarnessError('failed to deploy CursorWhileFixture')
        caller = dep0['receipt']['contractAddress']
        oracle_addrs = []
        for code in oracle_initcodes:
            dep = node.transact({'from': sender, 'data': code, 'gas': hex(5000000)})
            if dep['receipt']['status'] != '0x1':
                raise HarnessError('failed to deploy WordStaticOracle')
            oracle_addrs.append(dep['receipt']['contractAddress'])

    initial = [
        (account, '0x' + slot.to_bytes(32, 'big').hex(), '0x' + int(val).to_bytes(32, 'big').hex())
        for account, params in zip(oracle_addrs, ORACLES, strict=True)
        for slot, val in enumerate(params)
    ]

    transactions = []

    def add(sig: str, args: list[int]):
        idx = len(transactions)
        sel = source_evm['methodIdentifiers'][sig]
        name = sig[:sig.index('(')]
        encoded = b''.join(u256_bytes(a) for a in args)
        transactions.append({
            'id': str(idx),
            'function': name,
            'args': args,
            'sender': sender,
            'target': caller,
            'value': '0x0',
            'timestamp': 1000000100 + idx,
            'blockNumber': len(ORACLES) + 2 + idx,
            'data': '0x' + sel + encoded.hex(),
        })

    # 1. Empty cursor (0 items)
    add('sumPackedLocal()', [])
    add('sumPackedUsingFor()', [])
    add('sumBucketLocal()', [])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[0], 16)])
    add('scanNestedNamedArgs(uint256,address)', [7, int(sender, 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[0], 16)])

    # 2. 1 item
    add('pushItem(uint32)', [7])
    add('sumPackedLocal()', [])
    add('sumPackedUsingFor()', [])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[0], 16)])
    add('scanNestedNamedArgs(uint256,address)', [7, int(sender, 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[0], 16)])

    # 3. Fill up to 8 items (exact first slot boundary; all < 100 -> allOk == true)
    for v in [11, 22, 33, 44, 55, 66, 77]:
        add('pushItem(uint32)', [v])
    add('sumPackedLocal()', [])
    add('sumPackedUsingFor()', [])
    add('scanNestedNamedArgs(uint256,address)', [13, int(EMPTY, 16)])

    # 4. Push 3 more items (11 total -> crosses slot rollover idx % 8 == 0 into packedSlots[1]!; item 1001 >= 100 -> allOk == false)
    for v in [88, 99, 1001]:
        add('pushItem(uint32)', [v])
    add('sumPackedLocal()', [])
    add('sumPackedUsingFor()', [])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[0], 16)])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[1], 16)])
    add('scanNestedNamedArgs(uint256,address)', [13, int(EMPTY, 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[0], 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[1], 16)])

    # 5. Push 8 more items (19 total -> crosses TWO slot rollovers into packedSlots[2]!)
    for v in [10, 20, 30, 40, 50, 60, 70, 0xdeadbeef]:
        add('pushItem(uint32)', [v])
    add('sumPackedLocal()', [])
    add('sumPackedUsingFor()', [])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[0], 16)])
    add('scanPackedWithOracle(address)', [int(oracle_addrs[1], 16)])
    add('scanNestedNamedArgs(uint256,address)', [29, int(sender, 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[0], 16)])
    add('scanNestedOracleCall(address)', [int(oracle_addrs[1], 16)])

    # 6. Struct-member fixed storage array `bucket.words` across 10 items (rollover at idx == 8)
    for v in [5, 15, 25, 35, 45, 55, 65, 75, 85, 95]:
        add('pushBucketItem(uint32)', [v])
    add('sumBucketLocal()', [])

    # 7. Reset and verify empty cursor again (overwrites stale slot words ignored because count == 0)
    add('resetItems()', [])
    add('sumPackedLocal()', [])
    add('sumBucketLocal()', [])

    environment = {
        'program': 'word-static-oracle-v1',
        'accounts': [str(int(a, 16)) for a in oracle_addrs],
        'emptyAccounts': [str(int(EMPTY, 16)), str(int(sender, 16))],
        'gas': '1000000',
    }
    adapters = {
        'source': EVMAdapter(output / 'A', [caller_a, *oracle_initcodes], initial),
        'model': DenoteAdapter(output / 'B', driver, caller, initial,
                               byte_call_environment=environment,
                               account_code=[(a, oracle_runtime) for a in oracle_addrs]),
        'compiled': EVMAdapter(output / 'C', [caller_c, *oracle_initcodes], initial),
    }

    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in R8 cursor while loop: {output / 'campaign.json'}")
    print(f"R8 Anvil 3-route A/B/C PASS: {len(transactions)}/{len(transactions)} transactions agree bit-for-bit across solc, Lean Denote, and Verity Yul ({output})")


if __name__ == '__main__':
    main()
