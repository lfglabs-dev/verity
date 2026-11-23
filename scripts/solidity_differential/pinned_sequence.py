"""Config-driven stateful A/B/C campaigns over a contract in a pinned Git checkout.

The source route deploys the complete, unmodified contract compiled from a
clean checkout at an exact revision, never an extracted Solidity fixture. The
model route runs the actual imported multi-entry-point model through Denote;
the compiled route deploys the Verity-compiled model. Every route starts from
the same explicit storage world, deployed by the first sender. The source
constructor runs with the configured arguments on the source route; a probe
deployment requires every storage word it changes to equal the configured initial
storage (so the model route, which runs no constructor, starts from the same
world), and the immutables it stores are read from the deployed runtime code and
installed in the model; those bound to constructor arguments are passed to the
compiled model's constructor, which recomputes the others. A configured
dependency is compiled from the same checkout and settings and deployed first,
from its source bytecode, on the source and compiled routes; on the model route
its own imported model answers the tested contract's static calls
(`ModelResponders`). This instrument does not validate that dependency model;
`check_pinned_sequence_corpus` requires it to have its own campaign. Transactions are a deterministic prefix
followed by seeded random calls drawn from per-argument pools, and divergences
are shrunk to replayed witnesses. Sources, compiler identity and receipts are
retained.

Configuration (JSON; `project` is relative to the configuration file):

    project, revision, entry, contract   pinned checkout and imported contract
    settings                             solc settings (`evmVersion`, `viaIR`,
                                         `optimizer`, `metadata.bytecodeHash`)
    signatures                           imported entry points, in model order
    initialStorage                       [{"label": <state variable>, "value": v,
                                           "keys": [k, ...] (mapping entries only)}]
    constructorArgs                      source constructor arguments (optional)
    dependencies                         contracts deployed first (optional):
                                         [{entry, contract, signatures,
                                           constructorArgs, initialStorage}]
    prefix                               [{"signature": s, "args": [v], "sender": i,
                                           "expect": "ok" | "revert" (optional)}]
    arguments                            {<signature>: [[v, ...] per argument]}

Values are integers, booleans, `sender:<i>`, `contract` (the tested contract),
`dependency:<i>` addresses or 0x-prefixed hex (addresses and bytes32). Only static word-sized argument types are supported.
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

from .anvil import Anvil, SequenceAdapter as EVM
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
# Ample explicit gas for the model route's responder calls; gas equivalence is not claimed.
RESPONDER_GAS = 10000000
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


def resolve_value(value, ty, addresses=None):
    """Turn a configuration value into an `eth_abi` value of type `ty`.

    `addresses` maps `contract` and `dependency:<i>` to deployed addresses."""
    if isinstance(value, str) and value.startswith('sender:'):
        value = SENDERS[int(value[len('sender:'):])]
    elif isinstance(value, str) and (value == 'contract' or value.startswith('dependency:')):
        if addresses is None or value not in addresses:
            raise HarnessError(f'unknown deployed address: {value}')
        value = addresses[value]
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


def transaction(index, signature, values, sender, target, addresses=None, deployments=1):
    """A complete transaction whose calldata words equal its model arguments.

    Blocks 1..`deployments` hold the deployments; transaction `index` is mined after them."""
    types = argument_types(signature)
    if len(types) != len(values):
        raise HarnessError(f'argument count differs from signature: {signature}')
    addresses = {'contract': target} if addresses is None else addresses
    resolved = [resolve_value(value, ty, addresses) for value, ty in zip(values, types)]
    payload = encode(types, resolved)
    return {'id': str(index), 'function': signature.split('(')[0],
            'args': [int.from_bytes(payload[i:i + 32], 'big') for i in range(0, len(payload), 32)],
            'sender': SENDERS[sender], 'target': target,
            'data': '0x' + (keccak(text=signature)[:4] + payload).hex(),
            'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': deployments + 1 + index}


def transaction_sequence(config, count, seed, target, addresses=None):
    """Deterministic prefix, then seeded calls drawn from per-argument pools."""
    deployments = 1 + len(config.get('dependencies', []))
    prefix, pools = config['prefix'], config['arguments']
    if count < len(prefix):
        raise HarnessError(f'at least {len(prefix)} transactions required')
    if set(pools) != set(config['signatures']):
        raise HarnessError('every imported signature requires argument pools')
    calls = [transaction(index, row['signature'], row['args'], row['sender'], target, addresses,
                         deployments) for index, row in enumerate(prefix)]
    rng = random.Random(seed)
    while len(calls) < count:
        signature = rng.choice(config['signatures'])
        values = [rng.choice(pool) for pool in pools[signature]]
        calls.append(transaction(len(calls), signature, values,
                                 rng.randrange(len(SENDERS)), target, addresses, deployments))
    return calls


def create_address(deployer, nonce=0):
    """CREATE address: keccak(RLP([deployer, nonce]))[12:], for nonces below 2^8."""
    if type(nonce) is not int or not 0 <= nonce < 256:
        raise HarnessError('deployment nonce outside the supported range')
    # RLP: 0 is the empty string 80, 1..127 is one byte, 128..255 is 81 then the byte.
    encoded = b'\x80' if nonce == 0 else bytes([nonce]) if nonce < 128 else bytes([0x81, nonce])
    body = b'\x94' + bytes.fromhex(deployer[2:]) + encoded
    return '0x' + keccak(bytes([0xc0 + len(body)]) + body)[-20:].hex()


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


def import_command(name, repository, config, entry, contract, signatures):
    """One `solidity_import` command over the pinned checkout with the config's settings."""
    roots = '\n'.join('  function ' + signature for signature in signatures)
    return (f'solidity_import {name} from {json.dumps(str(repository))} entry {json.dumps(entry)}\n'
            f'  using {import_options(config["settings"])}\n  contract {contract}\n{roots}')


RUNNER = '''Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        model Compiler.CompilationModel.SolidityImport.Differential.oracle args'''
RESPONDERS = '''
        (configure := Compiler.CompilationModel.SolidityImport.ModelResponders.configure
          Compiler.CompilationModel.SolidityImport.Differential.oracle [{models}])'''


def driver_source(repository, config, mutant=None):
    """Lean driver importing every configured root; mutants alter only the model.

    Each dependency's own imported model answers the tested model's static calls."""
    if mutant not in (None, *MUTANTS):
        raise HarnessError(f'unknown pinned-sequence mutant: {mutant}')
    dependencies = config.get('dependencies', [])
    imports = [import_command('tested', repository, config, config['entry'], config['contract'],
                              config['signatures'])]
    imports += [import_command(f'dependency{index}', repository, config, row['entry'],
                               row['contract'], row['signatures'])
                for index, row in enumerate(dependencies)]
    header, runner = '', RUNNER
    if dependencies:
        header = 'import Compiler.SolidityImport.ModelResponders\n'
        runner += RESPONDERS.format(models=', '.join(
            f'dependency{index}.model' for index in range(len(dependencies))))
    definition = 'def model : CompilationModel := tested.model'
    if mutant == 'drop-events':
        definition = '''def model : CompilationModel :=
  { tested.model with functions := tested.model.functions.map fun fn =>
      { fn with body := fn.body.filter fun statement =>
          match statement with
          | .emit _ _ => false
          | _ => true } }'''
    imported = '\n'.join(imports)
    return f'''import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
{header}open Compiler.CompilationModel
{imported}
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
  | ["constructor", output] =>
      -- Constructor parameters in order, each installing the immutable of its name,
      -- and every immutable the model reads.
      let params := (model.constructor.map (·.params)).getD []
      for (index, param) in (List.range params.length).zip params do
        let installs := model.immutables.any fun imm => imm.name == param.name &&
          match imm.init with
          | .constructorArg argument => argument == index
          | _ => false
        unless installs do
          throw (IO.userError s!"constructor parameter {{index}} installs no immutable")
      IO.FS.writeFile output (Lean.Json.compress (Lean.Json.arr
        #[Lean.toJson (params.map (·.name)), Lean.toJson (model.immutables.map (·.name))]))
      return 0
  | _ =>
      {runner}
'''


def word_hex(word):
    return '0x' + word.to_bytes(32, 'big').hex()


def storage_slot(layout, row, addresses):
    """Slot of a labelled full-slot state variable, or of one word-valued mapping entry."""
    matches = [entry for entry in layout['storage'] if entry['label'] == row['label']]
    if len(matches) != 1 or matches[0]['offset'] != 0:
        raise HarnessError(f'unexpected storage layout for {row["label"]}')
    slot, ty = int(matches[0]['slot']), matches[0]['type']
    keys = row.get('keys', [])
    if not isinstance(keys, list):
        raise HarnessError(f'{row["label"]}: mapping keys must be a list')
    for key in keys:
        entry = layout['types'][ty]
        if entry.get('encoding') != 'mapping':
            raise HarnessError(f'{row["label"]}: more keys than mapping levels')
        key_type = layout['types'][entry['key']]['label']
        if key_type not in WORD_TYPES:
            raise HarnessError(f'{row["label"]}: unsupported mapping key type {key_type}')
        value = resolve_value(key, key_type, addresses)
        payload = encode([key_type], [value])
        slot, ty = int.from_bytes(keccak(payload + slot.to_bytes(32, 'big')), 'big'), entry['value']
    if keys and (layout['types'][ty].get('encoding') != 'inplace'
                 or layout['types'][ty]['numberOfBytes'] != '32'):
        raise HarnessError(f'{row["label"]}: mapping entry is not one full word')
    return slot


def initial_storage(layout, rows, address, addresses=None):
    """Resolve labelled state variables (and mapping entries) to explicit storage triples."""
    storage = []
    for row in rows:
        slot = storage_slot(layout, row, addresses)
        value = resolve_value(row['value'], 'address' if isinstance(row['value'], str) else 'uint256',
                              addresses)
        word = int(value, 16) if isinstance(value, str) else value
        storage.append([address, word_hex(slot), word_hex(word)])
    if len({row[1] for row in storage}) != len(storage):
        raise HarnessError('duplicate initial storage slot')
    return storage


DEPENDENCY_KEYS = {'entry', 'contract', 'signatures', 'constructorArgs', 'initialStorage'}


def load_config(path):
    path = Path(path).resolve()
    config = json.loads(path.read_text())
    required = {'project', 'revision', 'entry', 'contract', 'settings', 'signatures',
                'initialStorage', 'prefix', 'arguments'}
    if not required <= config.keys():
        raise HarnessError(f'incomplete pinned-sequence configuration: {sorted(required - config.keys())}')
    unknown = set(config) - required - {'constructorArgs', 'dependencies'}
    if unknown:
        raise HarnessError(f'unknown pinned-sequence configuration keys: {sorted(unknown)}')
    if config['settings'].get('evmVersion', 'osaka') != 'osaka':
        raise HarnessError('only the osaka evmVersion is supported')
    for index, row in enumerate(config['prefix']):
        if row.get('expect', 'ok') not in ('ok', 'revert'):
            raise HarnessError(f'prefix step {index}: expect must be "ok" or "revert"')
    config['project'] = (path.parent / config['project']).resolve()
    config.setdefault('constructorArgs', [])
    config.setdefault('dependencies', [])
    for index, row in enumerate(config['dependencies']):
        if not isinstance(row, dict) or set(row) != DEPENDENCY_KEYS:
            raise HarnessError(f'dependency {index}: keys must be exactly {sorted(DEPENDENCY_KEYS)}')
        for signature in row['signatures']:
            argument_types(signature)
    for signature in config['signatures']:
        argument_types(signature)
    return config


def constructor_arguments(abi, values, addresses, name):
    """ABI-encoded source constructor arguments, typed by the compiled constructor."""
    constructors = [row for row in abi if row['type'] == 'constructor']
    types = [row['type'] for row in constructors[0]['inputs']] if constructors else []
    if len(types) != len(values):
        raise HarnessError(f'{name}: constructor takes {len(types)} arguments, {len(values)} configured')
    if any(ty not in WORD_TYPES for ty in types):
        raise HarnessError(f'{name}: unsupported constructor argument types {types}')
    return encode(types, [resolve_value(v, ty, addresses) for v, ty in zip(values, types)]).hex()


def compile_routes(config, sources, output, mutant):
    """Compile the pinned sources and the Verity model; return route artifacts."""
    repository = config['project']
    settings = {**config['settings'], 'outputSelection': {'*': {
        '*': ['abi', 'evm.bytecode.object', 'evm.methodIdentifiers', 'storageLayout',
              'evm.deployedBytecode.immutableReferences'], '': ['ast']}}}
    # Let solc follow each entry's import graph rather than compiling every file.
    entries = {config['entry'], *(row['entry'] for row in config['dependencies'])}
    contracts = solc_compile({'language': 'Solidity',
        'sources': {name: sources[name] for name in sorted(entries)}, 'settings': settings},
        repository, output / 'source-solc')
    entry = contracts['contracts'][config['entry']][config['contract']]
    dependencies = [contracts['contracts'][row['entry']][row['contract']]
                    for row in config['dependencies']]
    driver = output / 'Driver.lean'
    driver.write_text(driver_source(repository, config, mutant))
    methods = entry['evm']['methodIdentifiers']
    write_json(output / 'selectors.json', [int(methods[s], 16) for s in config['signatures']])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json',
             output / 'model.yul'], timeout=900, log=output / 'model-compile.log')
    command(['lake', 'env', 'lean', '--run', driver, 'constructor', output / 'constructor.json'],
            timeout=900, log=output / 'model-constructor.log')
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
    immutable_names = ast_variable_names(contracts['sources'])
    return entry, dependencies, driver, compiled, immutable_names


def ast_variable_names(sources):
    """Names of every variable declaration, by AST id."""
    names = {}

    def walk(node):
        if isinstance(node, dict):
            if node.get('nodeType') == 'VariableDeclaration':
                names[str(node['id'])] = node['name']
            for child in node.values():
                walk(child)
        elif isinstance(node, list):
            for child in node:
                walk(child)
    for source in sources.values():
        walk(source['ast'])
    return names


def deployed_immutables(runtime, references, names):
    """Immutable words the source constructor stored, read from the deployed runtime code."""
    code = bytes.fromhex(runtime[2:])
    values = {}
    for ident, places in references.items():
        words = {code[p['start']:p['start'] + p['length']] for p in places}
        if len(words) != 1 or any(p['length'] != 32 for p in places):
            raise HarnessError(f'immutable {ident} has inconsistent deployed words')
        name = names[ident]
        if name in values:
            raise HarnessError(f'immutable name {name} is ambiguous')
        values[name] = int.from_bytes(words.pop(), 'big')
    return values


def probe_deployment(directory, deployments, initial):
    """Deploy every contract once on an owned node and check its constructor world.

    Every storage word a constructor changes must equal the configured initial storage
    of the deployed account (the diff-mode trace omits writes that leave a word as it
    was, which the configured world then sets on every route anyway). No constructor
    may change another account in any way (storage, including a word set to zero,
    which the diff lists only under `pre`; code; nonce; balance), except that the
    deployer's nonce and balance and the block's fee recipient's balance move for
    the deployment and its fees. Returns the deployed runtime code of each account."""
    configured = {(account, slot): value for account, slot, value in initial}
    runtimes = []
    with Anvil(directory) as node:
        deployer = node.rpc('eth_accounts')[0]
        if deployer != SENDERS[0]:
            raise HarnessError('unexpected deployment account')
        for name, address, code in deployments:
            record = node.transact({'from': deployer, 'data': code, 'gas': hex(30000000)})
            if record['receipt']['status'] != '0x1' or record['receipt']['contractAddress'] != address:
                raise HarnessError(f'{name}: source deployment failed or moved')
            diff = node.rpc('debug_traceTransaction', record['receipt']['transactionHash'],
                            {'tracer': 'prestateTracer', 'tracerConfig': {'diffMode': True}})
            miner = node.rpc('eth_getBlockByNumber', record['receipt']['blockNumber'], False)['miner']
            allowed = {deployer: {'nonce', 'balance'}, miner.lower(): {'balance'}}
            for account in set(diff['pre']) | set(diff['post']):
                if account == address:
                    continue
                before, after = diff['pre'].get(account, {}), diff['post'].get(account, {})
                # A storage word set to zero appears only under `pre`.
                changed = set(after) | ({'storage'} if before.get('storage') else set())
                if changed - allowed.get(account, set()):
                    raise HarnessError(f'{name}: constructor writes foreign account {account}: '
                                       f'{sorted(changed)}')
            for account, state in diff['post'].items():
                if account != address:
                    continue
                for slot, value in state.get('storage', {}).items():
                    expected = configured.get((address, slot), word_hex(0))
                    if int(value, 16) != int(expected, 16):
                        raise HarnessError(f'{name}: constructor writes slot {slot} = {value}, '
                                           f'configured initial storage {expected}')
            runtimes.append(node.rpc('eth_getCode', address, 'latest'))
    return runtimes


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


def deployment_world(config, entry, dependencies, compiled, immutable_names, output):
    """Addresses, deployments, initial storage, immutables and dependency code of every route.

    The first sender deploys the dependencies at nonces 0.. and the tested contract
    after them, on every route. The source route runs the source constructor with the
    configured arguments; its immutables, read back from the deployed runtime, are
    installed in the model, and those bound to constructor arguments are passed to
    the compiled model's constructor."""
    count = len(dependencies)
    address = create_address(SENDERS[0], count)
    addresses = {'contract': address, **{f'dependency:{index}': create_address(SENDERS[0], index)
                                         for index in range(count)}}
    deployments, initial = [], []
    for index, (row, artifact) in enumerate(zip(config['dependencies'], dependencies)):
        account = addresses[f'dependency:{index}']
        deployments.append((row['contract'], account, '0x' + artifact['evm']['bytecode']['object']
                            + constructor_arguments(artifact['abi'], row['constructorArgs'],
                                                    addresses, row['contract'])))
        initial += initial_storage(artifact['storageLayout'], row['initialStorage'], account, addresses)
    source = ('0x' + entry['evm']['bytecode']['object']
              + constructor_arguments(entry['abi'], config['constructorArgs'], addresses,
                                      config['contract']))
    deployments.append((config['contract'], address, source))
    initial += initial_storage(entry['storageLayout'], config['initialStorage'], address, addresses)
    runtimes = probe_deployment(output / 'deployment', deployments, initial)
    observed = deployed_immutables(runtimes[-1], entry['evm']['deployedBytecode']['immutableReferences'],
                                   immutable_names)
    params, declared = json.loads((output / 'constructor.json').read_text())
    missing = sorted(set(declared) - set(observed))
    if missing:
        raise HarnessError(f'model immutables absent from the source deployment: {missing}')
    immutables = [(name, observed[name]) for name in declared]
    arguments = ''.join(observed[name].to_bytes(32, 'big').hex() for name in params)
    # The compiled model's constructor is held to the same storage rule as the source one.
    compiled_deployments = deployments[:-1] + [(config['contract'], address, compiled + arguments)]
    compiled_runtimes = probe_deployment(output / 'compiled-deployment', compiled_deployments, initial)
    accounts = [account for _, account, _ in deployments]
    return {'address': address, 'addresses': addresses, 'initial': initial,
            'immutables': immutables, 'dependencyCode': list(zip(accounts[:-1], runtimes[:-1])),
            'source': [code for _, _, code in deployments],
            'compiled': [code for _, _, code in compiled_deployments],
            # Every replay must reproduce the probed runtimes (and so the immutables read
            # from them): a constructor whose result differs between deployments fails.
            'sourceCode': list(zip(accounts, runtimes)),
            'compiledCode': list(zip(accounts, compiled_runtimes))}


def campaign(config_path, output, count, seed, shrink_attempts, mutant=None):
    config, output = load_config(config_path), Path(output).resolve()
    if not output.is_relative_to(Path.cwd().resolve()):
        raise HarnessError('generated Lean driver output must be inside Lake workspace')
    output.mkdir(parents=True, exist_ok=False)
    sources, files = pinned_sources(config['project'], config['revision'], config['entry'])
    if any(row['entry'] not in sources for row in config['dependencies']):
        raise HarnessError('pinned dependency source is absent')
    digest = compiler_checksum()
    entry, dependencies, driver, compiled, immutable_names = compile_routes(
        config, sources, output, mutant)
    world = deployment_world(config, entry, dependencies, compiled, immutable_names, output)
    address, initial = world['address'], world['initial']
    identity = ImplementationIdentity(driver, extra_inputs=files)
    revision = command(['git', 'rev-parse', 'HEAD']).strip()
    calls = transaction_sequence(config, count, seed, address, world['addresses'])
    write_json(output / 'transactions.json', calls)
    responders = {}
    if dependencies:
        responders = {'byte_call_environment': {
            'program': 'imported-model-static-v1', 'gas': str(RESPONDER_GAS),
            'accounts': [str(int(account, 16)) for account, _ in world['dependencyCode']]},
            'account_code': world['dependencyCode']}
    adapters = {
        'source': EVM(output / 'A', world['source'], initial, expected_code=world['sourceCode']),
        'model': Denote(output / 'B', driver, address, initial, identity=identity,
                        immutables=world['immutables'], **responders),
        'compiled': EVM(output / 'C', world['compiled'], initial,
                        expected_code=world['compiledCode']),
    }
    result = replay_three_routes(calls, adapters)
    check_prefix_expectations(config['prefix'], result['observations']['source'])
    if command(['git', 'rev-parse', 'HEAD']).strip() != revision:
        raise HarnessError('candidate HEAD changed during pinned-sequence campaign')
    pinned_sources(config['project'], config['revision'], config['entry'])
    write_json(output / 'campaign.json', {**result, 'revision': config['revision'],
        'verityHead': revision, 'seed': seed, 'transactions': calls,
        'signatures': config['signatures'], 'mutant': mutant,
        # No route compares constructors: the model route runs none. Both constructors'
        # storage changes are checked against the initial storage, and the model route's
        # immutables are copied from the source deployment, not computed by the model.
        'constructorValidated': False,
        'constructorWorld': 'storage-changes-checked; model-route-immutables-copied-from-source',
        'addresses': world['addresses'],
        'immutables': world['immutables'], 'initialStorage': initial,
        'compilerSha256': digest, 'implementation': identity.manifest,
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
