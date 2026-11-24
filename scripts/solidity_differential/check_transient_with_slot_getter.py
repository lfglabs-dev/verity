"""Three-route Anvil differential check for R9: EIP-7201 constant-slot storage-pointer
getters (`assembly { $.slot := STORE_SLOT }` and `assembly ("memory-safe") { $.slot := 0x1111...1100 }`)
inside functions accessing a `transient bool` state variable.

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
    'readState(address)',
]

USER_A = 0x100000000000000000000000000000000000a11c
USER_B = 0x200000000000000000000000000000000000b0b0


def u256_bytes(v: int) -> bytes:
    return int(v).to_bytes(32, 'big')


def main():
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/TransientWithSlotGetterFixture.sol'
    driver = root / 'Contracts/SolidityImportSmoke/TransientWithSlotGetterModel.lean'
    output = Path(tempfile.mkdtemp(prefix='r9-transient-slot-getter-', dir=root / '.lake')).resolve()

    compiled = solc_compile(
        {
            'language': 'Solidity',
            'sources': {
                'TransientWithSlotGetterFixture.sol': {'content': fixture.read_text()},
            },
            'settings': {
                'evmVersion': 'osaka',
                'viaIR': True,
                'optimizer': {'enabled': True, 'runs': 466},
                'metadata': {'bytecodeHash': 'none'},
                'outputSelection': {'*': {'*': [
                    'evm.bytecode.object', 'evm.methodIdentifiers']}},
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

    with Anvil(output / 'deploy-check') as node:
        sender = node.rpc('eth_accounts')[0]
        dep0 = node.transact({'from': sender, 'data': caller_a, 'gas': hex(5000000)})
        if dep0['receipt']['status'] != '0x1':
            raise HarnessError('failed to deploy TransientWithSlotGetterFixture')
        caller = dep0['receipt']['contractAddress']

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
            'timestamp': 1000000200 + idx,
            'blockNumber': 2 + idx,
            'data': '0x' + sel + encoded.hex(),
        })

    # 1. Initial empty state
    add('readState(address)', [USER_A])
    add('readState(address)', [USER_B])

    # 2. Direct add (transient _inBatch == false -> +delta, batchRuns unchanged)
    add('addDirect(uint256,address)', [10, USER_A])
    add('readState(address)', [USER_A])

    # 3. Batch add (transient _inBatch == true during _addValue -> +2*a, batchRuns++, then literal-slot +b, reset _inBatch)
    add('addInBatch(uint256,uint256,address)', [5, 7, USER_A])
    add('readState(address)', [USER_A])

    # 4. Reverting batch add (must roll back both raw-slot storage AND transient _inBatch)
    add('addInBatchRevert(uint256,address)', [999, USER_A])
    add('readState(address)', [USER_A])

    # 5. Second user direct + batch + direct (verifies transient reset across tx boundaries and raw-slot mapping isolation)
    add('addDirect(uint256,address)', [25, USER_B])
    add('addInBatch(uint256,uint256,address)', [12, 30, USER_B])
    add('addDirect(uint256,address)', [1, USER_A])
    add('readState(address)', [USER_A])
    add('readState(address)', [USER_B])

    # 6. Overflow revert in batch (checked arithmetic panic rolls back cleanly)
    add('addInBatch(uint256,uint256,address)', [2**255, 1, USER_B])
    add('readState(address)', [USER_B])

    adapters = {
        'source': EVMAdapter(output / 'A', [caller_a], []),
        'model': DenoteAdapter(output / 'B', driver, caller, []),
        'compiled': EVMAdapter(output / 'C', [caller_c], []),
    }

    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in R9 transient+slot-getter: {output / 'campaign.json'}")
    print(f"R9 Anvil 3-route A/B/C PASS: {len(transactions)}/{len(transactions)} transactions agree bit-for-bit across solc, Lean Denote, and Verity Yul ({output})")


if __name__ == '__main__':
    main()
