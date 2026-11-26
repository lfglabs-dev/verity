"""Three-route Anvil differential check for:
  1. Non-zero loop bounds & helper loop early return (`LoopBoundsAndHelperReturn.sol`)
  2. Storage-pointer post-assignment guards (`StoragePointerGuardSequence.sol`, via-IR + legacy)
  3. Enum storage packing (clean + seeded dirty slot Panic(0x21)), nested struct `abi.decode`,
     and interface-declared struct ABI schemas (`EnumStructNestedDecode.sol`)

Compares Route A (solc 0.8.34), Route B (Verity Denote), and Route C (compiled Verity Yul).

Run: PYTHONPATH=scripts python3 -m solidity_differential.check_loops_storage_guards_and_enum_decode
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


def address(nonce: int) -> str:
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def compile_pair(fixture: Path, contract_name: str, functions: list[str], driver: Path,
                 output: Path, via_ir: bool):
    output.mkdir(parents=True, exist_ok=True)
    settings = {
        'evmVersion': 'osaka',
        'viaIR': via_ir,
        'optimizer': {'enabled': True, 'runs': 466},
        'metadata': {'bytecodeHash': 'none'},
    }
    compiled_sol = solc_compile(
        {
            'language': 'Solidity',
            'sources': {fixture.name: {'content': fixture.read_text()}},
            'settings': {
                **settings,
                'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
            },
        },
        fixture.parent,
        output / 'solc',
        solc=SOLC,
    )
    evm = compiled_sol['contracts'][fixture.name][contract_name]['evm']
    identifiers = evm['methodIdentifiers']
    selectors = [int(identifiers[sig], 16) for sig in functions]
    write_json(output / 'selectors.json', selectors)

    identity = ImplementationIdentity(driver, extra_inputs=[fixture])
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
        raise HarnessError(f'expected exactly one Verity-compiled Yul object for {contract_name}')
    return ('0x' + evm['bytecode']['object'],
            '0x' + objects[0]['evm']['bytecode']['object'],
            identifiers, identity)


def run_sequence(name: str, output: Path, source_code: str, compiled_code: str,
                 driver: Path, identity: ImplementationIdentity, calls: list[dict],
                 initial_storage: list[tuple[str, str, str]] = ()):
    caller = address(0)
    adapters = {
        'source': EVMAdapter(output / 'A', [source_code], initial_storage),
        'model': DenoteAdapter(output / 'B', driver, caller, initial_storage, identity=identity),
        'compiled': EVMAdapter(output / 'C', [compiled_code], initial_storage),
    }
    result = replay_three_routes(calls, adapters)
    identity.verify()
    write_json(output / 'campaign.json', {'transactions': calls, **result})
    if result['divergences']:
        raise HarnessError(f"3-route A/B/C divergence in {name}: {output / 'campaign.json'}")
    statuses = {row['status'] for row in result['observations']['source']}
    if statuses != {'ok', 'revert'}:
        raise HarnessError(f'{name} must exercise both ok and revert paths')
    return len(calls)


def build_txs(identifiers: dict[str, str], specs: list[tuple[str, list[int]]]) -> list[dict]:
    caller = address(0)
    txs = []
    for idx, (sig, words) in enumerate(specs):
        txs.append({
            'id': str(idx),
            'function': sig[:sig.index('(')],
            'args': words,
            'sender': SENDER,
            'target': caller,
            'data': '0x' + identifiers[sig] + ''.join(format(w, '064x') for w in words),
            'value': '0x0',
            'timestamp': 1000000100 + idx,
            'blockNumber': 2 + idx,
        })
    return txs


def run_loops(root: Path, output: Path) -> int:
    functions = [
        'sumRange(uint256,uint256)',
        'sumFromConst(uint256)',
        'sumFromExpr(uint256,uint256)',
        'predeclaredRange(uint256,uint256)',
        'narrowStartWrap(uint8,uint256)',
        'sumDown(uint256,uint256)',
        'helperDecrementReturn(uint8,uint256)',
        'helperNonZeroControl(uint8,uint256,uint256,uint256)',
        'helperNestedReturn(uint8,uint256)',
        'helperWhileReturn(uint256,uint256)',
        'helperWhileTrueReturn(uint256,uint256)',
        'voidForEarlyReturn(uint8,uint256)',
        'voidWhileEarlyReturn(uint256,uint256)',
    ]
    fixture = root / 'Contracts/SolidityImportSmoke/LoopBoundsAndHelperReturn.sol'
    driver = root / 'Contracts/SolidityImportSmoke/LoopBoundsAndHelperReturnModel.lean'
    src_code, cmp_code, ids, ident = compile_pair(
        fixture, 'LoopBoundsAndHelperReturn', functions, driver, output, via_ir=True
    )
    specs = [
        ('sumRange(uint256,uint256)', [3, 7]),
        ('sumRange(uint256,uint256)', [7, 7]),
        ('sumRange(uint256,uint256)', [9, 4]),
        ('sumFromConst(uint256)', [6]),
        ('sumFromConst(uint256)', [2]),
        ('sumFromExpr(uint256,uint256)', [2, 6]),
        ('predeclaredRange(uint256,uint256)', [2, 6]),
        ('predeclaredRange(uint256,uint256)', [6, 3]),
        ('narrowStartWrap(uint8,uint256)', [250, 255]),
        ('narrowStartWrap(uint8,uint256)', [250, 256]),   # Panic(0x11)
        ('narrowStartWrap(uint8,uint256)', [255, 256]),   # Panic(0x11)
        ('narrowStartWrap(uint8,uint256)', [250, 200]),
        ('sumDown(uint256,uint256)', [5, 2]),
        ('sumDown(uint256,uint256)', [2, 5]),
        ('helperDecrementReturn(uint8,uint256)', [5, 3]),
        ('helperDecrementReturn(uint8,uint256)', [5, 9]),
        ('helperNonZeroControl(uint8,uint256,uint256,uint256)', [7, 2, 5, 4]),
        ('helperNonZeroControl(uint8,uint256,uint256,uint256)', [7, 2, 4, 6]),
        ('helperNonZeroControl(uint8,uint256,uint256,uint256)', [5, 9, 9, 9]),
        ('helperNestedReturn(uint8,uint256)', [4, 21]),
        ('helperNestedReturn(uint8,uint256)', [4, 99]),
        ('helperWhileReturn(uint256,uint256)', [13, 2]),
        ('helperWhileReturn(uint256,uint256)', [13, 99]),
        ('helperWhileTrueReturn(uint256,uint256)', [13, 2]),
        ('helperWhileTrueReturn(uint256,uint256)', [13, 99]),
        ('voidForEarlyReturn(uint8,uint256)', [6, 3]),
        ('voidForEarlyReturn(uint8,uint256)', [6, 99]),
        ('voidWhileEarlyReturn(uint256,uint256)', [13, 2]),
        ('voidWhileEarlyReturn(uint256,uint256)', [13, 99]),
    ]
    return run_sequence('loops', output, src_code, cmp_code, driver, ident, build_txs(ids, specs))


def run_storage_guards(root: Path, output: Path, via_ir: bool, driver: Path) -> int:
    functions = [
        'add(uint256,uint256)',
        'addChecked(uint256,uint256)',
        'addRaw(uint256,uint256)',
        'store(uint256,bool,uint256)',
        'storeRaw(uint256,bool,uint256)',
        'read(uint256)',
        'readRaw(uint256)',
    ]
    fixture = root / 'Contracts/SolidityImportSmoke/StoragePointerGuardSequence.sol'
    src_code, cmp_code, ids, ident = compile_pair(
        fixture, 'StoragePointerGuardFixture', functions, driver, output, via_ir=via_ir
    )
    specs = [
        ('add(uint256,uint256)', [7, 5]),           # revert ItemInactive(7)
        ('addChecked(uint256,uint256)', [7, 5]),    # revert ItemInactive(7)
        ('addRaw(uint256,uint256)', [9, 25]),       # revert ItemInactive(9)
        ('store(uint256,bool,uint256)', [7, 1, 10]),
        ('add(uint256,uint256)', [7, 5]),
        ('addChecked(uint256,uint256)', [7, 20]),
        ('read(uint256)', [7]),
        ('storeRaw(uint256,bool,uint256)', [9, 1, 100]),
        ('addRaw(uint256,uint256)', [9, 25]),
        ('readRaw(uint256)', [9]),
        ('add(uint256,uint256)', [7, (1 << 256) - 1]),  # Panic(0x11)
    ]
    label = f"storage-guards-{'via-ir' if via_ir else 'legacy'}"
    return run_sequence(label, output, src_code, cmp_code, driver, ident, build_txs(ids, specs))


def run_enum_decode(root: Path, output: Path) -> int:
    functions = [
        'writePacked(uint64,uint8,uint64,bool)',
        'writeLevelParam(uint8)',
        'readLevelCast()',
        'isHigh()',
        'readUnusedLevel()',
        'copyPackedToMemory()',
        'pushAndReadArray(uint64,uint8,uint64,bool)',
        'decodeOuter(bytes)',
        'decodeOuterTuple(bytes)',
        'decodeInterfaceConfig(bytes)',
        'processInterfaceOrder((address,uint256,bytes))',
        'sumInterfaceItems((address,uint256)[])',
    ]
    fixture = root / 'Contracts/SolidityImportSmoke/EnumStructNestedDecode.sol'
    driver = root / 'Contracts/SolidityImportSmoke/EnumStructNestedDecodeModel.lean'
    src_code, cmp_code, ids, ident = compile_pair(
        fixture, 'EnumStructNestedDecode', functions, driver, output, via_ir=True
    )

    def bytes_arg(payload_words: list[int]) -> list[int]:
        return [32, 32 * len(payload_words), *payload_words]

    order_ok = [32, 0xABCD, 55, 96, 3, 0x010203 * (1 << 232)]
    order_dirty = [32, (1 << 160) + 1, 55, 96, 3, 0x010203 * (1 << 232)]
    items_ok = [32, 2, 0x1111, 10, 0x2222, 25]
    items_dirty = [32, 2, 0x1111, 10, (1 << 160) + 7, 25]

    clean_specs = [
        ('writePacked(uint64,uint8,uint64,bool)', [0x1122, 1, 0x3344, 1]),
        ('writePacked(uint64,uint8,uint64,bool)', [0x1122, 2, 0x3344, 1]),       # Panic(0x21)
        ('readLevelCast()', []),
        ('isHigh()', []),
        ('copyPackedToMemory()', []),
        ('writeLevelParam(uint8)', [0]),
        ('writeLevelParam(uint8)', [2]),                                         # ABI decode revert empty
        ('readLevelCast()', []),
        ('pushAndReadArray(uint64,uint8,uint64,bool)', [7, 1, 9, 1]),
        ('pushAndReadArray(uint64,uint8,uint64,bool)', [7, 2, 9, 1]),            # Panic(0x21)
        ('decodeOuter(bytes)', bytes_arg([10, 1, 20, 1, 1, 100])),
        ('decodeOuter(bytes)', bytes_arg([10, 2, 20, 1, 1, 100])),               # dirty nested enum
        ('decodeOuter(bytes)', bytes_arg([10, 1, 20, 1, 2, 100])),               # dirty outer enum
        ('decodeOuter(bytes)', bytes_arg([10, 1, 20, 2, 1, 100])),               # dirty nested bool
        ('decodeOuter(bytes)', bytes_arg([10, 1, 20, 1, 1])),                    # short buffer
        ('decodeOuterTuple(bytes)', bytes_arg([10, 1, 20, 0, 1, 100, 5])),
        ('decodeInterfaceConfig(bytes)', bytes_arg([0x1234, 2, 40])),
        ('decodeInterfaceConfig(bytes)', bytes_arg([(1 << 160) + 1, 2, 40])),    # dirty interface addr
        ('decodeInterfaceConfig(bytes)', bytes_arg([0x1234, 3, 40])),            # dirty interface enum
        ('processInterfaceOrder((address,uint256,bytes))', order_ok),
        ('processInterfaceOrder((address,uint256,bytes))', order_dirty),
        ('sumInterfaceItems((address,uint256)[])', items_ok),
        ('sumInterfaceItems((address,uint256)[])', items_dirty),
    ]
    n_clean = run_sequence(
        'enum-decode-clean', output / 'clean', src_code, cmp_code, driver, ident, build_txs(ids, clean_specs)
    )

    # Seed dirty enum ordinal (= 2 >= 2) in packed slot 0: cast/compare/copy revert Panic(0x21),
    # while unreferenced local initializer (`readUnusedLevel`) does not panic.
    dirty_word = 0x55 + (2 << 64) + (0x66 << 72) + (1 << 136)
    dirty_initial = [(address(0), '0x' + '00' * 32, '0x' + dirty_word.to_bytes(32, 'big').hex())]
    dirty_specs = [
        ('readLevelCast()', []),         # Panic(0x21)
        ('isHigh()', []),                # Panic(0x21)
        ('copyPackedToMemory()', []),    # Panic(0x21)
        ('readUnusedLevel()', []),       # succeeds with 0x55
    ]
    n_dirty = run_sequence(
        'enum-decode-dirty', output / 'dirty', src_code, cmp_code, driver, ident,
        build_txs(ids, dirty_specs), initial_storage=dirty_initial,
    )
    return n_clean + n_dirty


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='loops-guards-enum-', dir=root / '.lake')).resolve()

    n_loops = run_loops(root, output / 'loops')
    n_guards_ir = run_storage_guards(
        root, output / 'storage-guards-via-ir', True,
        root / 'Contracts/SolidityImportSmoke/StoragePointerGuardSequenceModel.lean',
    )
    n_guards_legacy = run_storage_guards(
        root, output / 'storage-guards-legacy', False,
        root / 'Contracts/SolidityImportSmoke/StoragePointerGuardLegacyModel.lean',
    )
    n_enum = run_enum_decode(root, output / 'enum-decode')
    total = n_loops + n_guards_ir + n_guards_legacy + n_enum
    print(
        f"Anvil 3-route A/B/C PASS: {total}/{total} transactions agree bit-for-bit "
        f"(loops={n_loops}, storage-guards-ir={n_guards_ir}, storage-guards-legacy={n_guards_legacy}, "
        f"enum-decode={n_enum}) ({output})"
    )


if __name__ == '__main__':
    main()
