"""Three-route Anvil differential check for 2D struct-valued mappings inside ERC-7201 raw-slot structs.

Compares:
  Route A: solc 0.8.34 (viaIR, osaka, runs=466) bytecode on Anvil
  Route B: Verity Lean Denote model (`RawSlotTwoDimStructMappingModel.lean`)
  Route C: Verity compiled Yul bytecode on Anvil

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_raw_slot_2d_struct_mapping
"""
from __future__ import annotations

import argparse
from pathlib import Path
import tempfile

from .anvil import Anvil, SequenceAdapter as EVMAdapter
from .denote import SequenceAdapter as DenoteAdapter
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes

FUNCTIONS = [
    'writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)',
    'readDirectGrid(uint256,uint256)',
    'updateViaPointer(uint256,uint256,uint128,uint64,bool)',
    'writeAndReadAccount(address,uint256,uint128,uint8,address,uint96)',
    'readRowHelper(uint256,uint256)',
    'deleteGridEntry(uint256,uint256)',
    'rawGridWords(uint256,uint256)',
    'rawAccountWords(address,uint256)',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'Contracts/SolidityImportSmoke/RawSlotTwoDimStructMapping.sol'
    driver = root / 'Contracts/SolidityImportSmoke/RawSlotTwoDimStructMappingModel.lean'
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='raw-slot-2d-struct-', dir=root / '.lake')).resolve()

    source_text = fixture.read_text()
    request = {
        'language': 'Solidity',
        'sources': {'RawSlotTwoDimStructMapping.sol': {'content': source_text}},
        'settings': {
            'evmVersion': 'osaka',
            'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
        },
    }
    compiled_sol = solc_compile(request, fixture.parent, output / 'solc', solc=SOLC)
    source = compiled_sol['contracts']['RawSlotTwoDimStructMapping.sol']['RawSlotTwoDimStructMapping']['evm']
    selectors = [int(source['methodIdentifiers'][sig], 16) for sig in FUNCTIONS]
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
    )
    objects = list(compiled_yul['contracts']['Model.yul'].values())
    if len(objects) != 1:
        raise HarnessError('expected exactly one Verity-compiled Yul object')

    source_code = '0x' + source['bytecode']['object']
    compiled_code = '0x' + objects[0]['evm']['bytecode']['object']

    with Anvil(output / 'deploy-check') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': source_code, 'gas': hex(5000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('failed to deploy source fixture')
        account = deployed['receipt']['contractAddress']

    calls = [
        # Direct write & read on 2D uint256=>uint256=>Entry mapping + raw double-Keccak sload
        ('writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)',
         [11, 22, 1000, 500, 2, 1, 0xBEEF, 7777]),
        ('readDirectGrid(uint256,uint256)', [11, 22]),
        ('readRowHelper(uint256,uint256)', [11, 22]),
        ('rawGridWords(uint256,uint256)', [11, 22]),
        # Distinct key stays zeroed
        ('readDirectGrid(uint256,uint256)', [11, 23]),
        # Storage pointer binding freezes slot & updates packed fields without clobbering siblings
        ('updateViaPointer(uint256,uint256,uint128,uint64,bool)', [11, 22, 250, 999, 0]),
        ('readDirectGrid(uint256,uint256)', [11, 22]),
        ('rawGridWords(uint256,uint256)', [11, 22]),
        # Second key pair with high-bit values (testing bit-packing boundaries)
        ('writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)',
         [0, (1 << 255) + 7, (1 << 128) - 1, (1 << 64) - 1, 1, 1, (1 << 160) - 1, (1 << 96) - 1]),
        ('readDirectGrid(uint256,uint256)', [0, (1 << 255) + 7]),
        ('rawGridWords(uint256,uint256)', [0, (1 << 255) + 7]),
        # Address-keyed 2D struct mapping: whole-struct assign + memory copy + raw double-Keccak sload
        ('writeAndReadAccount(address,uint256,uint128,uint8,address,uint96)',
         [0x1234567890ABCDEF1234567890ABCDEF12345678, 7, 900, 2, 0xCAFEBABE, 321]),
        ('rawAccountWords(address,uint256)',
         [0x1234567890ABCDEF1234567890ABCDEF12345678, 7]),
        # Delete clears both packed words at the exact double-Keccak slot
        ('deleteGridEntry(uint256,uint256)', [11, 22]),
        ('readDirectGrid(uint256,uint256)', [11, 22]),
        ('rawGridWords(uint256,uint256)', [11, 22]),
        # Out-of-range enum ordinal (3 >= 3) triggers Panic(0x21) across all 3 routes
        ('writeDirectGrid(uint256,uint256,uint128,uint64,uint8,bool,address,uint96)',
         [1, 2, 10, 20, 3, 0, 0x1, 1]),
        # Overflow on uint128 amount += delta in updateViaPointer triggers Panic(0x11)
        ('updateViaPointer(uint256,uint256,uint128,uint64,bool)', [0, (1 << 255) + 7, 1, 10, 0]),
    ]

    transactions = [
        {
            'id': str(idx),
            'function': sig.split('(')[0],
            'args': args,
            'sender': sender,
            'target': account,
            'value': '0x0',
            'timestamp': 1000000100 + idx,
            'blockNumber': 2 + idx,
            'data': '0x' + source['methodIdentifiers'][sig] + ''.join(format(a, '064x') for a in args),
        }
        for idx, (sig, args) in enumerate(calls)
    ]

    adapters = {
        'source': EVMAdapter(output / 'A', [source_code]),
        'model': DenoteAdapter(output / 'B', driver, account, identity=identity),
        'compiled': EVMAdapter(output / 'C', [compiled_code]),
    }

    result = replay_three_routes(transactions, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': transactions, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in raw-slot 2D struct mapping: {output / 'campaign.json'}")
    print(f"Anvil 3-route A/B/C PASS: {len(transactions)}/{len(transactions)} transactions agree bit-for-bit across solc, Lean Denote, and Verity Yul ({output})")


if __name__ == '__main__':
    main()
