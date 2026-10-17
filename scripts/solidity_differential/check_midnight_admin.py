"""Stateful A/B/C campaign against the unmodified, pinned Midnight contract.

This exercises ten administrative/authorization entry points, not the complete
Midnight interface. Constructor equivalence is outside scope: every route starts
from the same explicit storage world, with the deployer as configurator. The
source route deploys the complete real contract, never an extracted Solidity
fixture. All source files, compiler identity and execution receipts are retained.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import sys

from eth_abi import encode
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes, shrink_sequence

PIN = '96d31343e993329e7a593dde46516a2c0cbcd142'
SENDERS = (
    '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266',
    '0x70997970c51812dc3a010c7d01b50e0d17dc79c8',
    '0x3c44cdddb6a900fa2b585dd299e03d12fa4293bc',
)
SIGNATURES = (
    'setConfigurator(address)', 'setFeeSetter(address)',
    'setFeeClaimer(address)', 'setTickSpacingSetter(address)',
    'enableLltv(uint256)', 'enableLiquidationCursor(uint256)',
    'setDefaultSettlementFee(address,uint256,uint256)',
    'setDefaultContinuousFee(address,uint256)',
    'setConsumed(bytes32,uint128,address)',
    'setIsAuthorized(address,bool,address)',
)
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}


def pinned_sources(repository):
    """Require exact tracked inputs; untracked production files cannot sneak in."""
    repository = Path(repository).resolve()
    revision = command(['git', '-C', repository, 'rev-parse', 'HEAD']).strip()
    if revision != PIN:
        raise HarnessError('Midnight source revision differs from pinned corpus')
    if command(['git', '-C', repository, 'status', '--porcelain', '--', 'src']):
        raise HarnessError('Midnight production sources are dirty')
    names = command(['git', '-C', repository, 'ls-files', '-z', 'src']).split('\0')
    files = [repository / name for name in names if name.endswith('.sol')]
    if repository / 'src/Midnight.sol' not in files:
        raise HarnessError('pinned Midnight source is absent')
    if any(p.is_symlink() or not p.resolve().is_relative_to(repository) for p in files):
        raise HarnessError('Midnight source escapes pinned checkout')
    return {p.relative_to(repository).as_posix(): {'content': p.read_text()} for p in files}, files


def transactions_for(count, seed, target):
    rng = random.Random(seed)
    calls = []
    configurator = SENDERS[0]

    def add(signature, values, sender):
        types = signature[signature.index('(') + 1:-1].split(',')
        index = len(calls)
        words = [int.from_bytes(v, 'big') if isinstance(v, bytes) else
                 int(v, 16) if isinstance(v, str) else int(v) for v in values]
        calls.append({'id': str(index), 'function': signature.split('(')[0],
            'args': words, 'sender': sender, 'target': target,
            'data': '0x' + (keccak(text=signature)[:4] + encode(types, values)).hex(),
            'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})

    # Deterministic prefix exercises successful configuration, exact custom
    # errors, role handover, delegation, revocation and monotonic consumption.
    prefix = [
        (1, [SENDERS[0]], SENDERS[0]), (2, [SENDERS[1]], SENDERS[0]),
        (3, [SENDERS[2]], SENDERS[0]), (4, [10**18], SENDERS[0]),
        (4, [10**18 + 1], SENDERS[0]), (5, [10**18 - 1], SENDERS[0]),
        (5, [10**18], SENDERS[0]),
        (6, [SENDERS[2], 0, 0], SENDERS[0]),
        (6, [SENDERS[2], 7, 0], SENDERS[0]),
        (7, [SENDERS[2], 0], SENDERS[0]),
        (7, [SENDERS[2], (1 << 256) - 1], SENDERS[0]),
        (9, [SENDERS[1], True, SENDERS[0]], SENDERS[0]),
        (8, [bytes(32), 5, SENDERS[0]], SENDERS[1]),
        (8, [bytes(32), 4, SENDERS[0]], SENDERS[1]),
        (9, [SENDERS[1], False, SENDERS[0]], SENDERS[0]),
        (8, [bytes(32), 6, SENDERS[0]], SENDERS[1]),
        (0, [SENDERS[1]], SENDERS[0]),
        (1, [SENDERS[2]], SENDERS[0]),
        (1, [SENDERS[2]], SENDERS[1]),
        (0, [SENDERS[0]], SENDERS[1]),
    ]
    if count < len(prefix):
        raise HarnessError(f'at least {len(prefix)} transactions required')
    for index, args, sender in prefix:
        add(SIGNATURES[index], args, sender)
    while len(calls) < count:
        index = rng.randrange(len(SIGNATURES))
        sender = configurator if rng.randrange(2) else rng.choice(SENDERS)
        other = rng.choice(SENDERS)
        if index < 4:
            args = [other]
            if index == 0 and sender == configurator:
                configurator = other
        elif index in (4, 5):
            args = [rng.choice([0, 1, 10**18 - 1, 10**18, 10**18 + 1, (1 << 256) - 1])]
        elif index == 6:
            args = [other, rng.randrange(9), rng.choice([0, 10**12, 10**12 + 1, 10**18])]
        elif index == 7:
            args = [other, rng.choice([0, 1, 10**8, (1 << 256) - 1])]
        elif index == 8:
            args = [rng.randrange(4).to_bytes(32, 'big'), rng.choice([0, 1, 5, (1 << 128) - 1]), other]
        else:
            args = [other, bool(rng.randrange(2)), rng.choice(SENDERS)]
        add(SIGNATURES[index], args, sender)
    return calls


def driver_source(repository, mutant=None):
    roots = '\n'.join('  function ' + signature for signature in SIGNATURES)
    definition = 'def model : CompilationModel := tested.model'
    if mutant == 'drop-events':
        definition = '''def model : CompilationModel :=
  { tested.model with functions := tested.model.functions.map fun fn =>
      { fn with body := fn.body.filter fun statement =>
          match statement with
          | .emit _ _ => false
          | _ => true } }'''
    return f'''import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
open Compiler.CompilationModel
solidity_import tested from {json.dumps(str(repository))} entry "src/Midnight.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract Midnight
{roots}
{definition}
def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        model Compiler.CompilationModel.SolidityImport.Differential.oracle args
'''


def campaign(repository, output, count, seed, shrink_attempts, mutant=None):
    repository, output = Path(repository).resolve(), Path(output).resolve()
    if not output.is_relative_to(Path.cwd().resolve()):
        raise HarnessError('generated Lean driver output must be inside Lake workspace')
    output.mkdir(parents=True, exist_ok=False)
    sources, files = pinned_sources(repository)
    host = {'Linux': 'linux-amd64', 'Darwin': 'macosx-amd64'}.get(platform.system())
    manifest = json.loads(Path('scripts/solidity_import_corpus/manifest.json').read_text())
    compiler_hash = hashlib.sha256(SOLC.read_bytes()).hexdigest()
    if host is None or compiler_hash != manifest['compilers']['0.8.34'][host]['sha256']:
        raise HarnessError('source compiler checksum differs from pinned corpus')
    # Let solc follow the real Midnight import graph. Compiling every unrelated
    # periphery file would require dependencies absent from this core corpus.
    entry = solc_compile({'language': 'Solidity',
        'sources': {'src/Midnight.sol': sources['src/Midnight.sol']},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.methodIdentifiers', 'storageLayout']}}}},
        repository, output / 'source-solc')['contracts']['src/Midnight.sol']['Midnight']
    driver = output / 'Driver.lean'
    driver.write_text(driver_source(repository, mutant))
    selectors = [int(entry['evm']['methodIdentifiers'][signature], 16) for signature in SIGNATURES]
    write_json(output / 'selectors.json', selectors)
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json',
             output / 'model.yul'], timeout=900, log=output / 'model-compile.log')
    generated = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}},
        output, output / 'model-solc')['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('compiled model must have exactly one deployment object')
    # RLP([20-byte sender, nonce 0]): list-prefix d6, address-prefix 94,
    # address bytes, empty-string 80. Every replay deploys at nonce zero.
    address = '0x' + keccak(b'\xd6\x94' + bytes.fromhex(SENDERS[0][2:]) + b'\x80')[-20:].hex()
    config = [row for row in entry['storageLayout']['storage'] if row['label'] == 'configurator']
    if len(config) != 1 or config[0]['offset'] != 0:
        raise HarnessError('unexpected configurator storage layout')
    initial = [[address, '0x' + int(config[0]['slot']).to_bytes(32, 'big').hex(),
                '0x' + int(SENDERS[0], 16).to_bytes(32, 'big').hex()]]
    identity = ImplementationIdentity(driver, extra_inputs=files)
    revision = command(['git', 'rev-parse', 'HEAD']).strip()
    calls = transactions_for(count, seed, address)
    write_json(output / 'transactions.json', calls)
    adapters = {
        'source': EVM(output / 'A', ['0x' + entry['evm']['bytecode']['object']], initial),
        'model': Denote(output / 'B', driver, address, initial, identity=identity),
        'compiled': EVM(output / 'C', ['0x' + next(iter(generated.values()))['evm']['bytecode']['object']], initial),
    }
    result = replay_three_routes(calls, adapters)
    if command(['git', 'rev-parse', 'HEAD']).strip() != revision:
        raise HarnessError('candidate HEAD changed during Midnight campaign')
    pinned_sources(repository)
    report = {**result, 'midnightCommit': PIN, 'verityHead': revision, 'seed': seed,
        'transactions': calls, 'signatures': list(SIGNATURES), 'constructorValidated': False,
        'mutant': mutant,
        'initialStorage': initial, 'compilerSha256': compiler_hash,
        'implementation': identity.manifest,
        'sourceSha256': {name: hashlib.sha256(row['content'].encode()).hexdigest()
                         for name, row in sources.items()}}
    write_json(output / 'campaign.json', report)
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(output / 'reduced.json', reduced)
        return 1
    if {row['status'] for row in result['observations']['source']} != {'ok', 'revert'}:
        raise HarnessError('Midnight campaign must contain both success and revert')
    if mutant:
        raise HarnessError('Midnight instrument mutant escaped detection')
    print(f'Midnight administrative subset: {len(calls)} A/B/C transactions agree: {output}')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--midnight-repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--transactions', type=int, default=256)
    parser.add_argument('--seed', type=int, default=2514)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--mutant', choices=('drop-events',),
                        help='deliberate model fault; must diverge and shrink, exits 1')
    args = parser.parse_args()
    return campaign(args.midnight_repo, args.output, args.transactions, args.seed,
                    args.shrink_attempts, args.mutant)


if __name__ == '__main__':
    sys.exit(main())
