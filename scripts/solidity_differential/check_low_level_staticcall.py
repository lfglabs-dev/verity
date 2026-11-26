"""Contract-typed `this` as a value and Solidity low-level `<address>.staticcall(payload)`
through source EVM, Denote and compiled model, for solc 0.8.34 via-IR and legacy.

- `ThisValueSequence.sol`: `this` in `abi.encode` (an EIP-712 domain separator),
  `abi.encodePacked`, comparisons, an internal call argument, a local, a return value,
  event arguments and a storage write; each root has an `address(this)` twin or a
  directly comparable result.
- `LowLevelStaticcallSequence.sol` against calldata-folding responders
  (`InterfaceWordStaticCallOracle.sol` on the EVM side, `word-static-oracle-v1` in
  Denote): the ERC-1271 magic value, the magic value with dirty low bytes, another value,
  short (3 and 4 bytes), empty and long (96 bytes) answers, reverts with and without
  data, payload-dependent answers (the selector, every argument word and the calldata
  length are observable), one account without code and the sender EOA.
- The same fixture against the storage-recording responders
  (`ExternalCodeAndLowLevelCallResponder.sol`, `recording-call-responder-v1`), whose
  fallback writes storage: under STATICCALL every such call fails and the responders'
  storage is unchanged.

A divergence is shrunk to a deletion-minimal sequence.
"""
import argparse
import hashlib
from pathlib import Path
import random
import re
import sys
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

THIS_FIXTURE = Path('Contracts/SolidityImportSmoke/ThisValueSequence.sol')
THIS_DRIVER = Path('Contracts/SolidityImportSmoke/ThisValueSequenceModel.lean')
THIS_CONTRACT = 'ThisValueFixture'
THIS_ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "ThisValueSequence.sol"'
CALL_FIXTURE = Path('Contracts/SolidityImportSmoke/LowLevelStaticcallSequence.sol')
CALL_DRIVER = Path('Contracts/SolidityImportSmoke/LowLevelStaticcallSequenceModel.lean')
CALL_CONTRACT = 'LowLevelStaticcallFixture'
CALL_ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "LowLevelStaticcallSequence.sol"'
WORD_ORACLE = Path('Contracts/SolidityImportSmoke/InterfaceWordStaticCallOracle.sol')
RECORDING = Path('Contracts/SolidityImportSmoke/ExternalCodeAndLowLevelCallResponder.sol')
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
EMPTY = '0x' + '00' * 19 + '77'
WORD = (1 << 256) - 1
MAGIC = 0x1626ba7e << 224
# (value, failed, response length, mask) of `word-static-oracle-v1`.
WORD_ORACLES = [
    (MAGIC, False, 32, 0),
    (MAGIC | 1, False, 32, 0),
    (0xdeadbeef << 224, False, 32, 0),
    (MAGIC, False, 3, 0),
    (MAGIC, False, 4, 0),
    (MAGIC, False, 0, 0),
    (MAGIC, True, 32, 0),
    (0, True, 0, 0),
    (MAGIC, False, 96, 0),
    (0, False, 32, WORD),
    (MAGIC, False, 33, (1 << 224) - 1),
    (7, True, 65, WORD),
]
# (response word, failed, response length) of `recording-call-responder-v1`.
RECORDING_RESPONDERS = [
    (MAGIC, False, 32),
    (MAGIC, True, 32),
    (0, False, 0),
]
PIPELINES = {'via-ir': True, 'legacy': False}


def address(nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(SENDER[2:]), nonce]))[-20:].hex()


def roots(template):
    found = re.findall(r'^  function (\w+\([^)]*\))$', template, re.M)
    if not found:
        raise HarnessError('model driver lists no imported roots')
    return found


class Plan:
    def __init__(self, seed, block_offset):
        self.rng = random.Random(seed)
        self.block_offset = block_offset
        self.calls = []

    def add(self, caller, function, types, values):
        index = len(self.calls)
        selector = keccak(text=function)[:4].hex()
        name = function[:function.index('(')]
        encoded = encode(types, values)
        words = [int.from_bytes(encoded[i:i + 32], 'big') for i in range(0, len(encoded), 32)]
        self.calls.append({'id': str(index), 'function': name, 'args': words, 'sender': SENDER,
                           'target': caller, 'data': '0x' + selector + encoded.hex(),
                           'value': '0x0', 'timestamp': 1000000100 + index,
                           'blockNumber': self.block_offset + index})

    def word(self):
        return self.rng.choice([0, 1, 2, 31, 2**40 - 1, 2**40, self.rng.getrandbits(256), WORD])


def this_transactions(count, seed, caller, _responders):
    plan = Plan(seed, 2)
    accounts = [caller, SENDER, EMPTY, '0x' + '00' * 20]
    for function in ['domainSeparator()', 'domainSeparatorAddress()', 'viaLocal()', 'self()',
                     'recalled()', 'remember()', 'recalled()']:
        plan.add(caller, function, [], [])
    for tag in [0, 1, 2, 255, 256, WORD]:
        for function in ['packed(uint256)', 'packedAddress(uint256)', 'encoded(uint256)',
                         'viaArgument(uint256)', 'announce(uint256)']:
            plan.add(caller, function, ['uint256'], [tag])
    for account in accounts:
        plan.add(caller, 'isSelf(address)', ['address'], [account])
        plan.add(caller, 'isOther(address)', ['address'], [account])
    nullary = ['domainSeparator()', 'domainSeparatorAddress()', 'viaLocal()', 'self()',
               'remember()', 'recalled()']
    unary = ['packed(uint256)', 'packedAddress(uint256)', 'encoded(uint256)',
             'viaArgument(uint256)', 'announce(uint256)']
    while len(plan.calls) < count:
        choice = plan.rng.randrange(3)
        if choice == 0:
            plan.add(caller, plan.rng.choice(nullary), [], [])
        elif choice == 1:
            plan.add(caller, plan.rng.choice(unary), ['uint256'], [plan.word()])
        else:
            plan.add(caller, plan.rng.choice(['isSelf(address)', 'isOther(address)']), ['address'],
                     [plan.rng.choice(accounts)])
    return plan.calls


def call_transactions(count, seed, caller, responders):
    plan = Plan(seed, len(responders) + 2)
    targets = [*responders, EMPTY, SENDER]
    sigs = [b'', b'\x01\x02\x03', bytes(range(32)), bytes(range(65))]
    for index, target in enumerate(targets):
        digest = keccak(index.to_bytes(32, 'big'))
        sig = sigs[index % len(sigs)]
        plan.add(caller, 'isValid(address,bytes32)', ['address', 'bytes32'], [target, digest])
        plan.add(caller, 'observe(address,uint256,bytes32)', ['address', 'uint256', 'bytes32'],
                 [target, index, digest])
        plan.add(caller, 'isValidConstantSelector(address,bytes32)', ['address', 'bytes32'],
                 [target, digest])
        plan.add(caller, 'checkBytes(address,bytes32,bytes)', ['address', 'bytes32', 'bytes'],
                 [target, digest, sig])
        plan.add(caller, 'withSelector(address,bytes4,uint256)', ['address', 'bytes4', 'uint256'],
                 [target, digest[:4], index])
        plan.add(caller, 'fromLocal(address,uint256)', ['address', 'uint256'], [target, index])
        plan.add(caller, 'packed(address,uint256)', ['address', 'uint256'], [target, 2**40 + index])
        plan.add(caller, 'onlySuccess(address,bytes32)', ['address', 'bytes32'], [target, digest])
        plan.add(caller, 'onlyData(address,bytes32)', ['address', 'bytes32'], [target, digest])
        plan.add(caller, 'chained(address,bytes32)', ['address', 'bytes32'], [target, digest])
        plan.add(caller, 'record(address,bytes32)', ['address', 'bytes32'], [target, digest])
        plan.add(caller, 'stored()', [], [])
    while len(plan.calls) < count:
        choice = plan.rng.randrange(10)
        target = plan.rng.choice(targets)
        digest = plan.word().to_bytes(32, 'big')
        if choice == 0:
            plan.add(caller, 'isValid(address,bytes32)', ['address', 'bytes32'], [target, digest])
            plan.add(caller, 'withSelector(address,bytes4,uint256)',
                     ['address', 'bytes4', 'uint256'], [target, digest[:4], plan.word()])
        elif choice == 1:
            plan.add(caller, 'observe(address,uint256,bytes32)', ['address', 'uint256', 'bytes32'],
                     [target, plan.word(), digest])
        elif choice == 2:
            plan.add(caller, 'fromLocal(address,uint256)', ['address', 'uint256'],
                     [target, plan.word()])
        elif choice == 3:
            plan.add(caller, 'packed(address,uint256)', ['address', 'uint256'],
                     [target, plan.word()])
        elif choice == 4:
            plan.add(caller, 'onlySuccess(address,bytes32)', ['address', 'bytes32'],
                     [target, digest])
        elif choice == 5:
            plan.add(caller, 'onlyData(address,bytes32)', ['address', 'bytes32'], [target, digest])
        elif choice == 6:
            plan.add(caller, 'chained(address,bytes32)', ['address', 'bytes32'], [target, digest])
        elif choice == 7:
            plan.add(caller, 'record(address,bytes32)', ['address', 'bytes32'], [target, digest])
        elif choice == 8:
            plan.add(caller, 'checkBytes(address,bytes32,bytes)', ['address', 'bytes32', 'bytes'],
                     [target, digest, plan.rng.choice(sigs)])
        else:
            plan.add(caller, 'stored()', [], [])
    return plan.calls


def campaign(directory, source, template, transactions, seed, shrink_attempts, *, contract, anchor,
             plan, via_ir, responder=None, responder_contract=None, parameters=(),
             constructor_types=(), program=None, account_code=False, solc=SOLC):
    """Run one imported fixture under one solc pipeline; returns (exit code, report)."""
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    root = Path.cwd()
    settings = {'evmVersion': 'osaka', 'viaIR': via_ir, 'optimizer': {'enabled': True, 'runs': 466},
                'metadata': {'bytecodeHash': 'none'}}
    (directory / 'Sequence.sol').write_text(source)
    if template.count(anchor) != 1 or template.count('viaIR := true') != 1:
        raise HarnessError('nonunique imported source anchor or pipeline setting')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"')
                      .replace('viaIR := true', f'viaIR := {"true" if via_ir else "false"}'))
    sources = {'Sequence.sol': {'content': source}}
    if responder is not None:
        sources[responder.name] = {'content': (root / responder).read_text()}
    compiled = solc_compile({
        'language': 'Solidity', 'sources': sources,
        'settings': {**settings, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    caller_contract = compiled['Sequence.sol'][contract]
    identifiers = caller_contract['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in roots(template)])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    caller_a = '0x' + caller_contract['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(parameters))]
    deployed, initial, environment, code = [], [], None, []
    if responder is not None:
        mock = compiled[responder.name][responder_contract]['evm']
        deployed = ['0x' + mock['bytecode']['object']
                    + encode(list(constructor_types), list(p)).hex()
                    for p in parameters]
        initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(),
                    '0x' + int(value).to_bytes(32, 'big').hex())
                   for account, words in zip(accounts, parameters, strict=True)
                   for slot, value in enumerate(words)]
        environment = {'program': program, 'accounts': [str(int(a, 16)) for a in accounts],
                       # The sender is an EOA: a call that reaches it succeeds with no data.
                       'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))],
                       'gas': '1000000'}
        if account_code:
            code = [(account, '0x' + mock['deployedBytecode']['object']) for account in accounts]
    calls = plan(transactions, seed, caller, accounts)
    write_json(directory / 'transactions.json', calls)
    adapters = {
        'source': EVM(directory / 'A', [caller_a, *deployed], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment,
                        account_code=code),
        'compiled': EVM(directory / 'C', [caller_c, *deployed], initial)}
    result = replay_three_routes(calls, adapters)
    report = {'transactions': calls, 'observations': result['observations'],
              'divergences': result['divergences'], 'seed': seed, 'viaIR': via_ir,
              'parameters': [[str(v) for v in p] for p in parameters],
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()}
    if result['divergences']:
        reduced = shrink_sequence(
            calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
            max_attempts=shrink_attempts)
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    write_json(directory / 'campaign.json', report)
    return 0, report


def results(report):
    return [(row['status'], row['data']) for row in report['observations']['source']]


def check_this(report, caller):
    """Every `this` root succeeds, equals its `address(this)` twin on the same arguments, and
    `self()` / `viaLocal()` return the caller's address word."""
    by_function = {}
    for call, row in zip(report['transactions'], report['observations']['source'], strict=True):
        if row['status'] != 'ok':
            raise HarnessError(f'this root {call["function"]} reverted')
        by_function.setdefault((call['function'], tuple(call['args'])), set()).add(row['data'])
    self_word = '0x' + int(caller, 16).to_bytes(32, 'big').hex()
    twins = 0
    for (function, args), values in by_function.items():
        if function in ('self', 'viaLocal') and values != {self_word}:
            raise HarnessError(f'{function} is not the address of this contract')
        if function in ('domainSeparator', 'packed'):
            twin = by_function.get((function + 'Address', args))
            if twin is None:  # a random-phase call without a twin on the same arguments
                continue
            if twin != values:
                raise HarnessError(f'{function} differs from its address(this) twin')
            twins += 1
    if twins == 0:
        raise HarnessError('campaign compared no address(this) twins')


def check_staticcall(report, recording):
    statuses = {row['status'] for row in report['observations']['source']}
    if recording:
        # STATICCALL into a fallback that writes storage fails; no responder storage changes.
        for call, row in zip(report['transactions'], report['observations']['source'], strict=True):
            if call['function'] == 'onlySuccess' and row['status'] == 'ok' and \
                    int(call['data'][10:74], 16) not in (int(EMPTY, 16), int(SENDER, 16)):
                if int(row['data'][-64:], 16) != 0:
                    raise HarnessError('a storage-writing callee succeeded under staticcall')
    elif 'ok' not in statuses:
        raise HarnessError('campaign must exercise successful calls')


def run_part(part, where, via_ir, args):
    """One campaign of `part` under one pipeline into `where`, with its post-checks."""
    common = dict(transactions=args.transactions, seed=args.seed,
                  shrink_attempts=args.shrink_attempts, via_ir=via_ir)
    if part == 'this':
        code, report = campaign(where, THIS_FIXTURE.read_text(), THIS_DRIVER.read_text(),
                                contract=THIS_CONTRACT, anchor=THIS_ANCHOR,
                                plan=this_transactions, **common)
        if not code:
            check_this(report, address(0))
    elif part == 'word':
        code, report = campaign(where, CALL_FIXTURE.read_text(), CALL_DRIVER.read_text(),
                                contract=CALL_CONTRACT, anchor=CALL_ANCHOR,
                                plan=call_transactions, responder=WORD_ORACLE,
                                responder_contract='WordStaticOracle', parameters=WORD_ORACLES,
                                constructor_types=('uint256', 'bool', 'uint256', 'uint256'),
                                program='word-static-oracle-v1', **common)
        if not code:
            check_staticcall(report, False)
    else:
        code, report = campaign(where, CALL_FIXTURE.read_text(), CALL_DRIVER.read_text(),
                                contract=CALL_CONTRACT, anchor=CALL_ANCHOR,
                                plan=call_transactions, responder=RECORDING,
                                responder_contract='RecordingCallResponder',
                                parameters=RECORDING_RESPONDERS,
                                constructor_types=('uint256', 'bool', 'uint256'),
                                program='recording-call-responder-v1', account_code=True,
                                **{**common, 'transactions': max(64, 12 * 5)})
        if not code:
            check_staticcall(report, True)
    return code, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=180)
    parser.add_argument('--seed', type=int, default=2948)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--pipeline', action='append', choices=sorted(PIPELINES))
    parser.add_argument('--part', action='append', choices=('this', 'word', 'recording'))
    parser.add_argument('--single', action='store_true',
                        help='one campaign (--pipeline, --part) into --output; exit 1 on mismatch')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    parts = args.part or ['this', 'word', 'recording']
    minimum = (12 * (len(WORD_ORACLES) + 2) if 'word' in parts else
               (60 if 'recording' in parts else 45))
    if args.transactions < minimum:
        parser.error(f'at least {minimum} transactions cover every target and root')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='low-level-staticcall-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=True)
    if args.single:
        if len(args.pipeline or []) != 1 or len(parts) != 1 or args.output is None:
            parser.error('--single takes one --pipeline, one --part and --output')
        code, _ = run_part(parts[0], output, PIPELINES[args.pipeline[0]], args)
        return code
    completed = []
    for pipeline in args.pipeline or sorted(PIPELINES):
        via_ir = PIPELINES[pipeline]
        for part in parts:
            where = output / pipeline / part
            code, _ = run_part(part, where, via_ir, args)
            if code:
                raise SystemExit(f'{part} divergence under {pipeline}: {where}')
            completed.append(f'{pipeline}/{part}')
        write_json(output / 'completed.json', completed)
    write_json(output / 'summary.json', {'passed': True, 'completed': completed,
        'transactions': args.transactions, 'seed': args.seed,
        'scope': 'contract-typed this as a value and low-level staticcall: '
                 'source EVM / Denote / compiled model, solc 0.8.34 via-IR and legacy'})
    print(f'this value and low-level staticcall A/B/C agree: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
