"""Linked library DELEGATECALLs through source EVM, Denote and compiled model (#2728).

`LinkedLibraryCallSequence.sol` calls `public` and `external` functions of two libraries
directly (`L.f(...)`), which solc lowers to a DELEGATECALL into the linked library; one library
function itself DELEGATECALLs the other library. The source route deploys both libraries,
links them into the contract (standard-JSON `libraries`) and replays the sequence. The model is
imported with `linkedLibrariesMatchSource := true`, which inlines the library bodies in the
caller's frame. The campaign covers value-type and storage-reference arguments (a mapping
struct entry and a plain storage struct), packed results written to a mapping, `msg.sender`
and `address(this)` inside the library (events and storage), the library's custom error,
`Error(string)` and panic (0x11 overflow, 0x12 division by zero) forwarded as the caller's
revert data with all writes rolled back, a discarded void call, a view call, a result used in
a binary operation, invalid enum arguments (caller ABI revert) and several senders. A
divergence is shrunk to a deletion-minimal sequence.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .check_ecrecover import address
from .check_linked_library_call_rejections import MUTANTS
from .denote import SequenceAdapter as Denote
from .engine import MUTANT_BUILD_TIMEOUT, ROOT, SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/LinkedLibraryCallSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/LinkedLibraryCallSequenceModel.lean')
CONTRACT = 'LinkedLibraryCallFixture'
# Deployment order: the leaf library, the library that links it, then the contract.
LIBRARIES = ('LinkedPackLib', 'LinkedCounterLib')
DATA_RUNTIMES = (b'\x00', b'\x00' + b'\x11' * 32)
UNDEPLOYED = ('0x000000000000000000000000000000000000dead',
              '0x0000000000000000000000000000000000000063')
SENDERS = ('0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266',
           '0x70997970c51812dc3a010c7d01b50e0d17dc79c8',
           '0x3c44cdddb6a900fa2b585dd299e03d12fa4293bc')
SOLC_RELEASES = {
    '0.8.34': ('0.8.34+commit.80d5c536', ROOT / '.lake/solidity-import/solc-0.8.34'),
    '0.8.38': ('0.8.38+commit.1835d247', ROOT / '.lake/solidity-import/solc-0.8.38'),
}
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"'
PROFILE_ANCHOR = 'using { evmVersion := "osaka", viaIR := true,'
HALF = 2 ** 255


def selector_of(text):
    return keccak(text=text)[:4]


ERR_TOO_LARGE = '0x' + selector_of('ValueTooLarge(uint256)').hex()
ERR_BAD_PAYLOAD = '0x' + selector_of('BadPayload(uint256,bytes1)').hex()
ERR_STRING = '0x' + selector_of('Error(string)').hex()
PANIC_OVERFLOW = '0x' + (selector_of('Panic(uint256)') + (0x11).to_bytes(32, 'big')).hex()
PANIC_DIVISION = '0x' + (selector_of('Panic(uint256)') + (0x12).to_bytes(32, 'big')).hex()
PANIC_BOUNDS = '0x' + (selector_of('Panic(uint256)') + (0x32).to_bytes(32, 'big')).hex()

SIGNATURES = {
    'setConfig': ('setConfig(bytes32,address,uint8)', ['bytes32', 'address', 'uint256']),
    'setConfigLogged': ('setConfigLogged(bytes32,address,uint8)', ['bytes32', 'address', 'uint256']),
    'word': ('word(bytes32)', ['bytes32']),
    'bump': ('bump(bytes32,uint256)', ['bytes32', 'uint256']),
    'bumpMain': ('bumpMain(uint256)', ['uint256']),
    'bumpPacked': ('bumpPacked(bytes32,uint256,address)', ['bytes32', 'uint256', 'address']),
    'reset': ('reset(bytes32)', ['bytes32']),
    'addExternal': ('addExternal(bytes32,uint256)', ['bytes32', 'uint256']),
    'cleanNarrow': ('cleanNarrow(uint256,uint256,uint256,uint256,uint256,uint256)',
                    ['uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256']),
    'cleanReturnFromWide': ('cleanReturnFromWide(uint256,uint256,bytes32)',
                            ['uint256', 'uint256', 'bytes32']),
    'entryCleanVoid': ('entryCleanVoid(bytes32,uint256,uint256,uint256)',
                       ['bytes32', 'uint256', 'uint256', 'uint256']),
    'share': ('share(bytes32,uint256)', ['bytes32', 'uint256']),
    'roundTripBytesIsolation': ('roundTripBytesIsolation(bytes,bytes1,bytes1,uint8)',
                                ['bytes', 'bytes1', 'bytes1', 'uint8']),
    'echoAndCallerMutate': ('echoAndCallerMutate(bytes,uint8,bytes1)',
                            ['bytes', 'uint8', 'bytes1']),
    'duplicateDisjoint': ('duplicateDisjoint(uint8,uint8,bytes1)',
                          ['uint8', 'uint8', 'bytes1']),
    'nestedBytesAndStorage': ('nestedBytesAndStorage(bytes32,bytes,uint256,uint256,bytes1)',
                              ['bytes32', 'bytes', 'uint256', 'uint256', 'bytes1']),
    'argOrderBytes': ('argOrderBytes(bytes,uint256,bytes1)',
                      ['bytes', 'uint256', 'bytes1']),
    'revertFromBytesLib': ('revertFromBytesLib(bytes32,bytes,uint8)',
                           ['bytes32', 'bytes', 'uint8']),
    'inspectCode': ('inspectCode(bytes32,uint256,uint256)',
                    ['bytes32', 'uint256', 'uint256']),
    'total': ('total(bytes32)', ['bytes32']),
    'last': ('last(bytes32)', ['bytes32']),
    'calls': ('calls(bytes32)', ['bytes32']),
    'mainState': ('mainState()', []),
}


def runtime_initcode(runtime):
    assert len(runtime) < 256
    prefix = bytes([0x60, len(runtime), 0x80, 0x60, 0x0b, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3])
    return '0x' + (prefix + runtime).hex()


def transactions_for(count, seed, contract, coded):
    rng = random.Random(seed)
    calls = []
    expected = {}
    keys = [keccak(text=f'linked-library-{i}') for i in range(3)]
    pointers = ['0x' + '00' * 19 + '42', '0x' + 'ff' * 20, contract]
    code_targets = [*coded, *SENDERS, *UNDEPLOYED]

    def add(name, values, sender=SENDERS[0], expect=None):
        signature, types = SIGNATURES[name]
        data = selector_of(signature) + encode(types, values)
        words = [int.from_bytes(data[i:i + 32], 'big') for i in range(4, len(data), 32)]
        index = len(calls)
        calls.append({'id': str(index), 'function': name, 'args': words, 'sender': sender,
                      'target': contract, 'data': '0x' + data.hex(), 'value': '0x0',
                      'timestamp': 1000000100 + index,
                      'blockNumber': len(LIBRARIES) + len(DATA_RUNTIMES) + 2 + index})
        if expect is not None:
            expected[str(index)] = expect

    def observe(key):
        for name in ('total', 'last', 'calls', 'word'):
            add(name, [key])
        add('mainState', [])

    for mode in range(4):
        add('setConfig', [keys[0], pointers[mode % 3], mode], expect=('ok', None))
        add('setConfigLogged', [keys[1], pointers[(mode + 1) % 3], mode], expect=('ok', None))
        observe(keys[0])
        observe(keys[1])
    for mode in (4, 5, 255, 2 ** 256 - 1):
        add('setConfig', [keys[2], pointers[0], mode], expect=('revert', '0x'))
        add('setConfigLogged', [keys[2], pointers[0], mode], expect=('revert', '0x'))
    observe(keys[2])
    for sender in SENDERS:
        add('bump', [keys[0], 5], sender, expect=('ok', None))
        observe(keys[0])
    add('bump', [keys[0], 7], expect=('revert', ERR_STRING))
    add('bump', [keys[0], HALF + 1], expect=('revert', ERR_TOO_LARGE))
    add('bump', [keys[1], HALF], expect=('ok', None))
    add('bump', [keys[1], HALF], SENDERS[1], expect=('revert', PANIC_OVERFLOW))
    observe(keys[1])
    add('share', [keys[0], 0], expect=('revert', PANIC_DIVISION))
    add('share', [keys[0], 4], expect=('ok', None))
    add('bumpMain', [3], expect=('ok', None))
    add('bumpMain', [7], expect=('revert', ERR_STRING))
    add('bumpMain', [HALF], expect=('ok', None))
    add('bumpMain', [HALF], expect=('revert', PANIC_OVERFLOW))
    observe(keys[0])
    add('bumpPacked', [keys[2], 9, pointers[1]], SENDERS[2], expect=('ok', None))
    add('bumpPacked', [keys[2], 7, pointers[1]], expect=('revert', ERR_STRING))
    add('bumpPacked', [keys[2], HALF + 2, pointers[0]], expect=('revert', ERR_TOO_LARGE))
    observe(keys[2])
    add('reset', [keys[0]], expect=('ok', None))
    add('reset', [keys[2]], expect=('ok', None))
    add('addExternal', [keys[0], 11], SENDERS[1], expect=('ok', None))
    add('cleanNarrow', [0x105, 0x1ff, 2, 0x207, (1 << 160) | 0x42,
                        (0x11223344 << 224) | 0x99], expect=('ok', None))
    add('cleanNarrow', [0x200, 0x17f, 0, 0x100, (0xff << 160) | 1, 0xdeadbeef], expect=('ok', None))
    add('cleanReturnFromWide', [0x105, (1 << 160) | 0x42,
                                ((0x11223344 << 224) | 0x99).to_bytes(32, 'big')],
        expect=('ok', None))
    add('entryCleanVoid', [keys[0], 0x105, (1 << 160) | 0x42, (0x11223344 << 224) | 0x99],
        expect=('ok', None))
    # Bytes memory copy-in isolation, copy-out disjointness, unaligned lengths, slices, storage
    # bytes, multi-arg evaluation order, and reverts with data from bytes-accepting library calls.
    for blob in (b'', b'\x11', b'\x11\x22', bytes(range(1, 32)), bytes(range(1, 33)),
                 bytes(range(1, 34)), bytes(range(1, 66))):
        add('roundTripBytesIsolation', [blob, b'\xfe', b'\xaa', 0x77], expect=('ok', None))
    for mode in (0, 1, 2):
        add('echoAndCallerMutate', [b'\x33\x44\x55', mode, b'\xee'], expect=('ok', None))
        add('echoAndCallerMutate', [b'', mode, b'\x99'], expect=('ok', None))
    add('duplicateDisjoint', [0x22, 0, b'\x99'], expect=('ok', None))
    add('duplicateDisjoint', [0xab, 33, b'\x12'], expect=('ok', None))
    add('nestedBytesAndStorage', [keys[0], b'\x10\x20\x30\x40\x50', 1, 4, b'\xdd'],
        SENDERS[1], expect=('ok', None))
    add('nestedBytesAndStorage', [keys[1], bytes(range(40)), 0, 0, b'\xcc'],
        SENDERS[2], expect=('ok', None))
    add('argOrderBytes', [b'\x11\x22\x33', 3, b'\xee'], expect=('ok', None))
    add('argOrderBytes', [b'', 5, b'\xee'], expect=('ok', None))
    add('argOrderBytes', [b'\x11\x22', 0, b'\xee'], expect=('revert', PANIC_DIVISION))
    add('revertFromBytesLib', [keys[0], b'\x42\x43', 0], expect=('revert', ERR_BAD_PAYLOAD))
    add('revertFromBytesLib', [keys[0], b'\x42\x43', 1], expect=('revert', ERR_STRING))
    add('revertFromBytesLib', [keys[0], b'\x42\x43', 2], expect=('revert', PANIC_BOUNDS))
    # Frame-neutral extcodesize in direct and nested internal library helpers across
    # deployed contracts (1-byte and 33-byte runtime), funded EOAs, and not-yet-deployed
    # addresses, with clean and upper-bit-dirty 256-bit words.
    for addr, rlen, mask in (
        (coded[0], 1, 0),
        (coded[0], 1, 1 << 160),
        (coded[1], 33, 0),
        (coded[1], 33, 0xff << 160),
        (SENDERS[0], 0, 0),
        (SENDERS[1], 0, 3 << 160),
        (UNDEPLOYED[0], 0, 0),
        (UNDEPLOYED[1], 0, 7 << 160),
    ):
        salt = 5
        want_tag = ((rlen + salt) << 16) if rlen else (((salt << 16) | 1) | 0x100)
        want_data = '0x' + encode(['uint256', 'uint256', 'uint256'], [rlen, rlen, want_tag]).hex()
        add('inspectCode', [keys[1], mask | int(addr, 16), salt], expect=('ok_data', want_data))
    observe(keys[0])
    observe(keys[1])
    observe(keys[2])
    while len(calls) < count:
        key = rng.choice(keys)
        sender = rng.choice(SENDERS)
        choice = rng.randrange(19)
        amount = rng.choice([0, 1, 7, 2 ** 64, HALF - 1, HALF, HALF + 1, rng.getrandbits(256)])
        rand_len = rng.choice([0, 1, 2, 15, 31, 32, 33, 64, 65])
        rand_bytes = bytes(rng.randrange(256) for _ in range(rand_len))
        if choice == 0:
            add('setConfig', [key, rng.choice(pointers), rng.choice([0, 1, 2, 3, 3, 4])], sender)
        elif choice == 1:
            add('setConfigLogged', [key, rng.choice(pointers), rng.randrange(6)], sender)
        elif choice == 2:
            add('bump', [key, amount], sender)
        elif choice == 3:
            add('bumpMain', [amount], sender)
        elif choice == 4:
            add('bumpPacked', [key, amount, rng.choice(pointers)], sender)
        elif choice == 5:
            add('reset', [key], sender)
        elif choice == 6:
            add('share', [key, rng.choice([0, 1, 3, 2 ** 255])], sender)
        elif choice == 7:
            add('addExternal', [key, amount], sender)
        elif choice == 8:
            add('cleanNarrow', [rng.getrandbits(256), rng.getrandbits(256),
                                rng.choice([0, 1, 2, rng.getrandbits(256)]),
                                rng.getrandbits(256), rng.getrandbits(256),
                                rng.getrandbits(256)], sender)
        elif choice == 9:
            add('cleanReturnFromWide', [rng.getrandbits(256), rng.getrandbits(256),
                                        rng.getrandbits(256).to_bytes(32, 'big')], sender)
        elif choice == 10:
            add('entryCleanVoid', [key, rng.getrandbits(256), rng.getrandbits(256),
                                   rng.getrandbits(256)], sender)
        elif choice == 11:
            add('roundTripBytesIsolation',
                [rand_bytes, bytes([rng.randrange(256)]), bytes([rng.randrange(256)]),
                 rng.randrange(256)], sender)
        elif choice == 12:
            add('echoAndCallerMutate',
                [rand_bytes, rng.randrange(4), bytes([rng.randrange(256)])], sender)
        elif choice == 13:
            add('duplicateDisjoint',
                [rng.randrange(256), rng.choice([0, 1, 30, 31, 32, 33]),
                 bytes([rng.randrange(256)])], sender)
        elif choice == 14:
            start = rng.randint(0, len(rand_bytes))
            end = rng.randint(start, len(rand_bytes))
            add('nestedBytesAndStorage',
                [key, rand_bytes, start, end, bytes([rng.randrange(256)])], sender)
        elif choice == 15:
            add('argOrderBytes',
                [rand_bytes, rng.choice([0, 1, 2, 3, 9]), bytes([rng.randrange(256)])], sender)
        elif choice == 16:
            add('revertFromBytesLib', [key, rand_bytes, rng.randrange(3)], sender)
        elif choice == 17:
            high = rng.choice([0, 1 << 160, rng.randrange(1 << 96) << 160])
            add('inspectCode',
                [key, high | int(rng.choice(code_targets), 16), rng.randrange(256)], sender)
        else:
            observe(key)
    return calls, expected


def configure_profile(source, template, solc_version, via_ir):
    release, solc_bin = SOLC_RELEASES[solc_version]
    if solc_version != '0.8.34':
        source = source.replace('pragma solidity 0.8.34;', f'pragma solidity {solc_version};', 1)
    if template.count(PROFILE_ANCHOR) != 1:
        raise HarnessError('nonunique profile anchor in driver template')
    via_ir_lit = 'true' if via_ir else 'false'
    template = template.replace(
        PROFILE_ANCHOR,
        f'using {{ solc := "{release}", evmVersion := "osaka", viaIR := {via_ir_lit},')
    settings = {**SETTINGS, 'viaIR': via_ir}
    return source, template, settings, solc_bin


def campaign(directory, source, template, transactions, seed, shrink_attempts, solc=SOLC,
             linked_source=None, solc_version='0.8.34', via_ir=True, lean_cwd=None):
    """Replay the three routes. `linked_source`, when given, is compiled for the libraries the
    source route deploys instead of `source` (a deployment that breaks the linking assumption)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    source, template, settings, solc = configure_profile(source, template, solc_version, via_ir)
    if linked_source is not None and solc_version != '0.8.34':
        linked_source = linked_source.replace('pragma solidity 0.8.34;',
                                              f'pragma solidity {solc_version};', 1)
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    # Libraries take the deployer's first nonces, the contract the next one, on every route.
    linked = {name: address(i) for i, name in enumerate(LIBRARIES)}
    contract = address(len(LIBRARIES))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source}},
        'settings': {**settings, 'libraries': {'Sequence.sol': linked},
                     'outputSelection': {'*': {'*': [
                         'evm.bytecode.object', 'evm.bytecode.linkReferences',
                         'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']['Sequence.sol']
    for name in LIBRARIES + (CONTRACT,):
        bytecode = compiled[name]['evm']['bytecode']
        if bytecode['linkReferences'] or '__$' in bytecode['object']:
            raise HarnessError(f'{name} is not fully linked')
    for name, user in (('LinkedPackLib', 'LinkedCounterLib'), ('LinkedPackLib', CONTRACT),
                       ('LinkedCounterLib', CONTRACT)):
        if linked[name][2:] not in compiled[user]['evm']['bytecode']['object']:
            raise HarnessError(f'{user} does not hold the linked address of {name}')
    identifiers = compiled[CONTRACT]['evm']['methodIdentifiers']
    signatures = [line[len('  function '):] for line in template.splitlines()
                  if line.startswith('  function ')]
    # The enum parameter's ABI type is uint8.
    write_json(directory / 'selectors.json',
               [int(identifiers[s.replace('Mode', 'uint8')], 16) for s in signatures])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log', cwd=lean_cwd)
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    libraries = ['0x' + compiled[name]['evm']['bytecode']['object'] for name in LIBRARIES]
    source_libraries = libraries
    if linked_source is not None:
        other = solc_compile({
            'language': 'Solidity', 'sources': {'Sequence.sol': {'content': linked_source}},
            'settings': {**settings, 'libraries': {'Sequence.sol': linked},
                         'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
        }, directory, directory / 'solc-linked', solc=solc)['contracts']['Sequence.sol']
        source_libraries = ['0x' + other[name]['evm']['bytecode']['object'] for name in LIBRARIES]
        if source_libraries == libraries:
            raise HarnessError('negative control links the same library code')
    model_code = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    coded = [address(len(LIBRARIES) + 1 + i) for i in range(len(DATA_RUNTIMES))]
    data_initcodes = [runtime_initcode(rt) for rt in DATA_RUNTIMES]
    expected_code = [(addr, '0x' + rt.hex()) for addr, rt in zip(coded, DATA_RUNTIMES, strict=True)]
    calls, expected = transactions_for(transactions, seed, contract, coded)
    write_json(directory / 'transactions.json', calls)
    # The compiled model does not call the libraries; deploying them keeps the nonces (and so
    # the contract and data-contract addresses) equal across routes.
    denote_cmd = (('sh', '-c', f'cd {lean_cwd} && exec lake env lean --run "$@"', '--')
                  if lean_cwd is not None else ('lake', 'env', 'lean', '--run'))
    adapters = {
        'source': EVM(directory / 'A',
                      [*source_libraries, '0x' + compiled[CONTRACT]['evm']['bytecode']['object'],
                       *data_initcodes], [], expected_code=expected_code),
        'model': Denote(directory / 'B', driver, contract, [], byte_call_environment={},
                        account_code=expected_code, lean_command=denote_cmd),
        'compiled': EVM(directory / 'C', [*libraries, model_code, *data_initcodes], [],
                        expected_code=expected_code)}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed, 'libraries': linked,
              'contract': contract, 'coded': coded, 'solc': solc_version, 'viaIR': via_ir,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    # Vacuity guard: the source EVM must show each intended outcome (successful linked calls,
    # exact extcodesize observations across contract/EOA/undeployed targets, every forwarded
    # revert payload and the caller's ABI revert).
    rows = {row['id']: row for row in result['observations']['source']}
    for ident, (status, want) in expected.items():
        row = rows[ident]
        if status == 'ok':
            ok = row['status'] == 'ok'
        elif status == 'ok_data':
            ok = row['status'] == 'ok' and row['data'] == want
        elif want == '0x':
            ok = row['status'] == 'revert' and row['data'] == '0x'
        else:
            ok = row['status'] == 'revert' and row['data'].startswith(want)
        if not ok:
            raise HarnessError(f'transaction {ident}: expected {status} {want} from the EVM, got {row}')
    write_json(directory / 'campaign.json', report)
    return 0, report


def run_abc_mutant(output, name, transactions, seed, solc_version, via_ir):
    from .mutations import release, snapshot
    relative_path, anchor, replacement, _ = MUTANTS[name]
    snap = output / 'snapshot'
    snapshot(snap)
    imp = snap / relative_path
    original = imp.read_text()
    if original.count(anchor) != 1:
        raise HarnessError(f'mutation anchor for {name} is not unique')
    imp.write_text(original.replace(anchor, replacement))
    command(['lake', 'build', 'Compiler.SolidityImport.Import',
             'Compiler.SolidityImport.Differential',
             'Compiler.SolidityImport.SequenceRunner',
             'Compiler.Codegen'],
            cwd=snap, timeout=MUTANT_BUILD_TIMEOUT, log=output / 'build.log')
    code, report = campaign(
        output / 'run', (snap / FIXTURE).read_text(), (snap / DRIVER).read_text(),
        transactions, seed, 20, solc_version=solc_version, via_ir=via_ir, lean_cwd=snap)
    if not code or not report['divergences']:
        raise SystemExit(f'linked library mutant {name} survived A/B/C: {output}')
    release(snap)
    write_json(output / 'complete.json', {
        'exit': 0, 'mutant': name, 'detected': True,
        'divergenceCount': len(report['divergences'])
    })
    print(f'linked library A/B/C mutant {name} detected ({len(report["divergences"])} divergences): {output}')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=200)
    parser.add_argument('--seed', type=int, default=2728)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--solc', choices=tuple(SOLC_RELEASES), default='0.8.34')
    parser.add_argument('--legacy', action='store_true', help='compile source and import model with viaIR := false')
    parser.add_argument('--mutant', choices=('alias-copy-in', 'drop-copy-out'),
                        help='build a mutated importer snapshot and require A/B/C divergence')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--negative-control', action='store_true',
                        help='link a library whose code differs from the imported source and '
                             'require a divergence')
    args = parser.parse_args()
    via_ir = not args.legacy
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='linked-library-call-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=args.output is None)
    if args.mutant:
        return run_abc_mutant(output, args.mutant, args.transactions, args.seed, args.solc, via_ir)
    if args.negative_control:
        source = FIXTURE.read_text()
        mutated = source.replace('(uint256(mode) << 160) | uint160(pointer);\n    }\n\n    function packLogged',
                                 '(uint256(mode) << 161) | uint160(pointer);\n    }\n\n    function packLogged')
        if mutated == source:
            raise HarnessError('negative control anchor missing')
        code, _ = campaign(output, source, DRIVER.read_text(), args.transactions, args.seed, 20,
                           linked_source=mutated, solc_version=args.solc, via_ir=via_ir)
        if not code:
            raise SystemExit(f'a library linked with other code went undetected: {output}')
        print(f'linked library negative control diverges as expected: {output}')
        return 0
    code, _ = campaign(output, FIXTURE.read_text(), DRIVER.read_text(), args.transactions, args.seed,
                       args.shrink_attempts, solc_version=args.solc, via_ir=via_ir)
    if code:
        raise SystemExit(f'linked library call divergence: {output}')
    write_json(output / 'summary.json', {
        'passed': True, 'transactions': args.transactions,
        'seed': args.seed, 'solc': args.solc, 'viaIR': via_ir,
        'scope': 'linked library DELEGATECALLs: source EVM (libraries '
                 'deployed and linked) / Denote / compiled model'})
    print(f'linked library call A/B/C agree (solc {args.solc}, viaIR={via_ir}): {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
