"""Config-driven stateful A/B/C campaigns over a contract in a pinned Git checkout.

The source route deploys the complete, unmodified contract compiled from a
clean checkout at an exact revision, never an extracted Solidity fixture. The
model route runs the actual imported multi-entry-point model through Denote;
the compiled route deploys the Verity-compiled model. Constructor equivalence
is outside this instrument: every route starts from the same explicit storage
world, deployed by the first sender. Transactions are a deterministic prefix
followed by seeded random calls drawn from per-argument pools, and divergences
are shrunk to replayed witnesses. Sources, compiler identity and receipts are
retained.

Configuration (JSON; `project` is relative to the configuration file):

    project, revision, entry, contract   pinned checkout and imported contract
    settings                             solc settings (`evmVersion`, `viaIR`,
                                         `optimizer`, `metadata.bytecodeHash`)
    signatures                           imported entry points, in model order
    initialStorage                       [{"label": <state variable>, "value": v}]
    prefix                               [{"signature": s, "args": [v], "sender": i,
                                           "expect": "ok" | "revert" (optional)}]
    arguments                            {<signature>: [[v, ...] per argument]}

Values are integers, booleans, `sender:<i>` addresses or 0x-prefixed hex
(addresses and bytes32). Only static word-sized argument types are supported.
A prefix row's optional `expect` is the documented source outcome: the source
route must reproduce it, or the campaign fails before any A/B/C verdict.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import sys

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import ROOT, HarnessError, SOLC, command, solc_compile, write_json
from .identity import ImplementationIdentity
from .stateful import replay_three_routes, shrink_sequence

try:
    from eth_abi import encode
except ModuleNotFoundError:
    def encode(types, values):
        words = []
        for ty, val in zip(types, values):
            if ty == 'bool':
                words.append(int(bool(val)).to_bytes(32, 'big'))
            elif ty == 'bytes32':
                words.append(bytes(val))
            elif ty == 'address':
                words.append(int(val, 16).to_bytes(32, 'big'))
            else:
                words.append(int(val).to_bytes(32, 'big'))
        return b''.join(words)

try:
    from eth_utils import keccak
except ModuleNotFoundError:
    if str(ROOT / 'scripts') not in sys.path:
        sys.path.insert(0, str(ROOT / 'scripts'))
    from keccak256 import keccak_256 as _keccak_256

    def keccak(primitive=None, *, text=None):
        return _keccak_256(text.encode('utf-8') if text is not None else primitive)

# Anvil's first funded accounts; the first one deploys every route at nonce 0.
SENDERS = (
    '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266',
    '0x70997970c51812dc3a010c7d01b50e0d17dc79c8',
    '0x3c44cdddb6a900fa2b585dd299e03d12fa4293bc',
)
MUTANTS = ('drop-events',)
WORD_TYPES = ('address', 'bool', 'bytes32') + tuple(f'uint{n}' for n in range(8, 257, 8))


def pinned_sources(repository, revision, entry):
    """Require exact tracked inputs across the checkout; untracked/ignored files cannot sneak in."""
    repository = Path(repository).resolve()
    if command(['git', '-C', repository, 'rev-parse', 'HEAD']).strip() != revision:
        raise HarnessError('source revision differs from the pinned revision')
    if command(['git', '-C', repository, 'status', '--porcelain', '--ignored']):
        raise HarnessError('pinned production sources are dirty')
    names = command(['git', '-C', repository, 'ls-files', '-z']).split('\0')
    files = [repository / name for name in names if name.endswith('.sol')]
    if repository / entry not in files:
        raise HarnessError('pinned entry source is absent')
    if any(p.is_symlink() or not p.resolve().is_relative_to(repository) for p in files):
        raise HarnessError('pinned source escapes the checkout')
    return {p.relative_to(repository).as_posix(): {'content': p.read_text()} for p in files}, files


def argument_types(signature):
    """Static word-sized ABI parameter types of a canonical signature."""
    inner = signature[signature.index('(') + 1:-1]
    types = inner.split(',') if inner else []
    if any(ty not in WORD_TYPES for ty in types):
        raise HarnessError(f'unsupported pinned-sequence argument type: {signature}')
    return types


def resolve_value(value, ty):
    """Turn a configuration value into an `eth_abi` value of type `ty`."""
    if isinstance(value, str) and value.startswith('sender:'):
        value = SENDERS[int(value[len('sender:'):])]
    if ty == 'bool':
        if type(value) is not bool:
            raise HarnessError('boolean argument requires a JSON boolean')
        return value
    if ty == 'bytes32':
        raw = int(value, 16) if isinstance(value, str) else value
        return raw.to_bytes(32, 'big')
    if ty == 'address':
        return value if isinstance(value, str) else '0x' + value.to_bytes(20, 'big').hex()
    if type(value) is not int:
        raise HarnessError('unsigned argument requires a JSON integer')
    return value


def transaction(index, signature, values, sender, target):
    """A complete transaction whose calldata words equal its model arguments."""
    types = argument_types(signature)
    if len(types) != len(values):
        raise HarnessError(f'argument count differs from signature: {signature}')
    resolved = [resolve_value(value, ty) for value, ty in zip(values, types)]
    payload = encode(types, resolved)
    return {'id': str(index), 'function': signature.split('(')[0],
            'args': [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)],
            'sender': SENDERS[sender], 'target': target,
            'data': '0x' + (keccak(text=signature)[:4] + payload).hex(),
            'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index}


def transaction_sequence(config, count, seed, target):
    """Deterministic prefix, then seeded calls drawn from per-argument pools."""
    prefix, pools = config['prefix'], config['arguments']
    if count < len(prefix):
        raise HarnessError(f'at least {len(prefix)} transactions required')
    if set(pools) != set(config['signatures']):
        raise HarnessError('every imported signature requires argument pools')
    calls = [transaction(index, row['signature'], row['args'], row['sender'], target)
             for index, row in enumerate(prefix)]
    rng = random.Random(seed)
    while len(calls) < count:
        signature = rng.choice(config['signatures'])
        values = [rng.choice(pool) for pool in pools[signature]]
        calls.append(transaction(len(calls), signature, values,
                                 rng.randrange(len(SENDERS)), target))
    return calls


def create_address(deployer):
    """CREATE address at nonce 0: keccak(RLP([deployer, 0]))[12:]."""
    # RLP: list prefix d6, address prefix 94, address bytes, empty string 80.
    return '0x' + keccak(b'\xd6\x94' + bytes.fromhex(deployer[2:]) + b'\x80')[-20:].hex()


def import_options(settings):
    optimizer = settings.get('optimizer', {})
    runs = optimizer.get('runs') if optimizer.get('enabled') else None
    fields = [f'evmVersion := {json.dumps(settings.get("evmVersion", "osaka"))}',
              f'viaIR := {"true" if settings.get("viaIR") else "false"}',
              f'optimizerRuns := {"none" if runs is None else f"some {runs}"}']
    bytecode_hash = settings.get('metadata', {}).get('bytecodeHash')
    if bytecode_hash is not None:
        fields.append(f'bytecodeHash := {json.dumps(bytecode_hash)}')
    return '{ ' + ', '.join(fields) + ' }'


def driver_source(repository, config, mutant=None):
    """Lean driver importing every configured root; mutants alter only the model."""
    if mutant not in (None, *MUTANTS):
        raise HarnessError(f'unknown pinned-sequence mutant: {mutant}')
    roots = '\n'.join('  function ' + signature for signature in config['signatures'])
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
solidity_import tested from {json.dumps(str(repository))} entry {json.dumps(config['entry'])}
  using {import_options(config['settings'])}
  contract {config['contract']}
{roots}
{definition}
def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        model Compiler.CompilationModel.SolidityImport.Differential.oracle args
'''


def initial_storage(layout, rows, address):
    """Resolve labelled full-slot state variables to explicit storage triples."""
    storage = []
    for row in rows:
        matches = [entry for entry in layout['storage'] if entry['label'] == row['label']]
        if len(matches) != 1 or matches[0]['offset'] != 0:
            raise HarnessError(f'unexpected storage layout for {row["label"]}')
        value = resolve_value(row['value'], 'address' if isinstance(row['value'], str) else 'uint256')
        word = int(value, 16) if isinstance(value, str) else value
        storage.append([address, '0x' + int(matches[0]['slot']).to_bytes(32, 'big').hex(),
                        '0x' + word.to_bytes(32, 'big').hex()])
    return storage


def load_config(path):
    path = Path(path).resolve()
    config = json.loads(path.read_text())
    required = {'project', 'revision', 'entry', 'contract', 'settings', 'signatures',
                'initialStorage', 'prefix', 'arguments'}
    if not required <= config.keys():
        raise HarnessError(f'incomplete pinned-sequence configuration: {sorted(required - config.keys())}')
    if config['settings'].get('evmVersion', 'osaka') != 'osaka':
        raise HarnessError('only the osaka evmVersion is supported')
    for index, row in enumerate(config['prefix']):
        if row.get('expect', 'ok') not in ('ok', 'revert'):
            raise HarnessError(f'prefix step {index}: expect must be "ok" or "revert"')
    config['project'] = (path.parent / config['project']).resolve()
    for signature in config['signatures']:
        argument_types(signature)
    return config


def compile_routes(config, sources, output, mutant):
    """Compile the pinned source and the Verity model; return route artifacts."""
    repository = config['project']
    settings = {**config['settings'], 'outputSelection': {'*': {'*': [
        'evm.bytecode.object', 'evm.methodIdentifiers', 'storageLayout']}}}
    # Let solc follow the entry's import graph rather than compiling every file.
    entry = solc_compile({'language': 'Solidity',
        'sources': {config['entry']: sources[config['entry']]}, 'settings': settings},
        repository, output / 'source-solc')['contracts'][config['entry']][config['contract']]
    driver = output / 'Driver.lean'
    driver.write_text(driver_source(repository, config, mutant))
    methods = entry['evm']['methodIdentifiers']
    write_json(output / 'selectors.json', [int(methods[s], 16) for s in config['signatures']])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json',
             output / 'model.yul'], timeout=900, log=output / 'model-compile.log')
    optimizer = config['settings'].get('optimizer', {'enabled': False})
    generated = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': config['settings'].get('evmVersion', 'osaka'),
                     'optimizer': optimizer,
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}},
        output, output / 'model-solc')['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('compiled model must have exactly one deployment object')
    compiled = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    return entry, driver, compiled


def compiler_checksum():
    host = {'Linux': 'linux-amd64', 'Darwin': 'macosx-amd64'}.get(platform.system())
    manifest = json.loads((ROOT / 'scripts/solidity_import_corpus/manifest.json').read_text())
    digest = hashlib.sha256(SOLC.read_bytes()).hexdigest()
    if host is None or digest != manifest['compilers']['0.8.34'][host]['sha256']:
        raise HarnessError('source compiler checksum differs from pinned corpus')
    return digest


def check_prefix_expectations(prefix, source_rows):
    """The source route reproduces each documented prefix outcome, located by step."""
    for index, (row, observed) in enumerate(zip(prefix, source_rows)):
        if 'expect' in row and observed['status'] != row['expect']:
            raise HarnessError(f'prefix step {index} ({row["signature"]}): source route '
                               f'{observed["status"]}, expected {row["expect"]}')


def campaign(config_path, output, count, seed, shrink_attempts, mutant=None):
    config, output = load_config(config_path), Path(output).resolve()
    if not output.is_relative_to(Path.cwd().resolve()):
        raise HarnessError('generated Lean driver output must be inside Lake workspace')
    output.mkdir(parents=True, exist_ok=False)
    sources, files = pinned_sources(config['project'], config['revision'], config['entry'])
    digest = compiler_checksum()
    entry, driver, compiled = compile_routes(config, sources, output, mutant)
    address = create_address(SENDERS[0])
    initial = initial_storage(entry['storageLayout'], config['initialStorage'], address)
    identity = ImplementationIdentity(driver, extra_inputs=files)
    revision = command(['git', 'rev-parse', 'HEAD']).strip()
    calls = transaction_sequence(config, count, seed, address)
    write_json(output / 'transactions.json', calls)
    adapters = {
        'source': EVM(output / 'A', ['0x' + entry['evm']['bytecode']['object']], initial),
        'model': Denote(output / 'B', driver, address, initial, identity=identity),
        'compiled': EVM(output / 'C', [compiled], initial),
    }
    result = replay_three_routes(calls, adapters)
    check_prefix_expectations(config['prefix'], result['observations']['source'])
    if command(['git', 'rev-parse', 'HEAD']).strip() != revision:
        raise HarnessError('candidate HEAD changed during pinned-sequence campaign')
    pinned_sources(config['project'], config['revision'], config['entry'])
    write_json(output / 'campaign.json', {**result, 'revision': config['revision'],
        'verityHead': revision, 'seed': seed, 'transactions': calls,
        'signatures': config['signatures'], 'constructorValidated': False, 'mutant': mutant,
        'initialStorage': initial, 'compilerSha256': digest, 'implementation': identity.manifest,
        'sourceSha256': {name: hashlib.sha256(row['content'].encode()).hexdigest()
                         for name, row in sources.items()}})
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(output / 'reduced.json', reduced)
        return 1
    if {row['status'] for row in result['observations']['source']} != {'ok', 'revert'}:
        raise HarnessError('pinned-sequence campaign must contain both success and revert')
    if mutant:
        raise HarnessError('pinned-sequence instrument mutant escaped detection')
    print(f'{config["contract"]}: {len(calls)} pinned A/B/C transactions agree: {output}')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--transactions', type=int, default=256)
    parser.add_argument('--seed', type=int, default=2514)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--mutant', choices=MUTANTS,
                        help='deliberate model fault; must diverge and shrink, exits 1')
    args = parser.parse_args()
    return campaign(args.config, args.output, args.transactions, args.seed,
                    args.shrink_attempts, args.mutant)


if __name__ == '__main__':
    sys.exit(main())
