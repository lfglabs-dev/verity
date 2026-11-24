"""Zero tests of `address(this).code.length` through source EVM, Denote and compiled model.

The imported fixture quotes OpenZeppelin's `Initializable.initializer` guard, whose
`construction` branch reads `address(this).code.length == 0`. The executing
account's code differs between the source and compiled routes, so only a
comparison with zero is admitted; it agrees between routes because both have
code exactly when the account was deployed.

Two contexts are replayed:

* runtime: each EVM route deploys its contract and receives real transactions;
  Denote's account world holds the source runtime code for the executing
  account (any nonempty code answers the same zero tests). `initialize` must
  succeed once and revert the second time.
* construction: each EVM route deploys its contract as an implementation, then
  a probe whose constructor delegatecalls every call of the sequence into it, so
  the executing account (the probe) has no code yet. Denote replays the same
  sequence from an empty world at the probe's address with no code for it.
  `initialize` must succeed twice (OpenZeppelin's `construction` branch).

Per call status and return or revert data, the events and the final storage of
the executing account must agree on the three routes.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from eth_abi import decode, encode
from eth_utils import keccak
import rlp

from .anvil import Anvil, SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/SelfCodeLengthSequence.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/SelfCodeLengthSequenceModel.lean')
CONTRACT = 'SelfCodeLengthFixture'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
SETTINGS = {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
            'metadata': {'bytecodeHash': 'none'}}
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "SelfCodeLengthSequence.sol"'
# OpenZeppelin's ERC-7201 slot of `InitializableStorage`, and the fixture's two words.
INITIALIZABLE = '0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00'
SLOTS = [INITIALIZABLE, '0x' + '00' * 32, '0x' + '00' * 31 + '01']
SIGNATURES = {'initialize': 'initialize(uint256)', 'hasCode': 'hasCode()', 'noCode': 'noCode()',
              'orientations': 'orientations()', 'mark': 'mark(uint256)',
              'requireCode': 'requireCode()', 'state': 'state()'}
# The probe's constructor delegatecalls each call into the implementation while the probe
# has no code, then returns the outcomes as its runtime code (leading byte zero).
PROBE = '''// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract ConstructionProbe {
    constructor(address implementation, bytes[] memory calls) {
        bool[] memory oks = new bool[](calls.length);
        bytes[] memory results = new bytes[](calls.length);
        for (uint256 i = 0; i < calls.length; i++) {
            (oks[i], results[i]) = implementation.delegatecall(calls[i]);
        }
        bytes memory encoded = abi.encode(oks, results);
        assembly {
            return(add(encoded, 32), mload(encoded))
        }
    }
}
'''
# Construction context: the second `initialize` is admitted by the `construction` branch.
CONSTRUCTION_CALLS = [('state', []), ('noCode', []), ('hasCode', []), ('orientations', []),
                      ('requireCode', []), ('mark', [3]), ('initialize', [7]), ('state', []),
                      ('initialize', [9]), ('mark', [5]), ('state', [])]


class Divergence(HarnessError):
    """The routes disagree: a finding, not a tool failure."""


def address(sender, nonce):
    return '0x' + keccak(rlp.encode([bytes.fromhex(sender[2:]), nonce]))[-20:].hex()


def calldata(function, args):
    signature = SIGNATURES[function]
    types = ['uint256'] * len(args)
    return '0x' + keccak(text=signature)[:4].hex() + encode(types, args).hex()


def transactions_for(count, seed, target, first_block):
    rng = random.Random(seed)
    calls = []

    def add(function, args):
        index = len(calls)
        calls.append({'id': str(index), 'function': function, 'args': args, 'sender': SENDER,
                      'target': target, 'data': calldata(function, args), 'value': '0x0',
                      'timestamp': 1000000100 + index, 'blockNumber': first_block + index})

    # Deterministic prefix: every view before and after initialization, then the second
    # `initialize`, which must revert at runtime.
    for function, args in [('state', []), ('noCode', []), ('hasCode', []), ('orientations', []),
                           ('requireCode', []), ('mark', [3]), ('initialize', [7]), ('state', []),
                           ('initialize', [9]), ('requireCode', []), ('mark', [5]), ('state', [])]:
        add(function, args)
    while len(calls) < count:
        function = rng.choice(sorted(SIGNATURES))
        args = [rng.choice([0, 1, 2 ** 255, rng.randrange(1, 1000)])] if function in (
            'initialize', 'mark') else []
        if function == 'mark':
            args = [rng.randrange(0, 1000)]
        add(function, args)
    return calls


def compile_routes(directory, source, template, solc):
    (directory / 'Sequence.sol').write_text(source)
    if template.count(ANCHOR) != 1:
        raise HarnessError('nonunique imported self-code-length source anchor')
    driver = directory / 'Driver.lean'
    driver.write_text(template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"'))
    compiled = solc_compile({
        'language': 'Solidity', 'sources': {'Sequence.sol': {'content': source},
                                            'Probe.sol': {'content': PROBE}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers']}}},
    }, directory, directory / 'solc', solc=solc)['contracts']
    fixture = compiled['Sequence.sol'][CONTRACT]
    identifiers = fixture['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in SIGNATURES.values()])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    return {'driver': driver, 'source': '0x' + fixture['evm']['bytecode']['object'],
            'runtime': '0x' + fixture['evm']['deployedBytecode']['object'],
            'compiled': '0x' + next(iter(generated.values()))['evm']['bytecode']['object'],
            'probe': '0x' + compiled['Probe.sol']['ConstructionProbe']['evm']['bytecode']['object']}


def runtime_campaign(directory, routes, transactions, seed, shrink_attempts):
    target = address(SENDER, 0)
    calls = transactions_for(transactions, seed, target, 2)
    write_json(directory / 'runtime-transactions.json', calls)
    adapters = {
        'source': EVM(directory / 'runtime-A', [routes['source']]),
        'model': Denote(directory / 'runtime-B', routes['driver'], target, self_code=routes['runtime']),
        'compiled': EVM(directory / 'runtime-C', [routes['compiled']])}
    result = replay_three_routes(calls, adapters)
    if result['divergences']:
        reduced = shrink_sequence(calls, lambda txs: replay_three_routes(txs, adapters)['divergences'],
                                  max_attempts=shrink_attempts)
        write_json(directory / 'runtime-reduced.json', reduced)
        write_json(directory / 'runtime.json', result)
        raise Divergence(f'runtime divergence: {directory}')
    rows = result['observations']['source']
    initialized = [row['status'] for call, row in zip(calls, rows, strict=True)
                   if call['function'] == 'initialize']
    if initialized[:2] != ['ok', 'revert'] or 'ok' in initialized[1:]:
        raise HarnessError(f'runtime initialize must succeed once, then revert: {initialized}')
    no_code = {row['data'] for call, row in zip(calls, rows, strict=True) if call['function'] == 'noCode'}
    if no_code != {'0x' + '00' * 32}:
        raise HarnessError(f'deployed account must have code: {sorted(no_code)}')
    write_json(directory / 'runtime.json', result)
    return result


def probe_route(directory, implementation, probe, calls):
    """Delegatecall `calls` from a constructor; return per-call rows, events and storage."""
    with Anvil(directory) as node:
        deployer = node.rpc('eth_accounts')[0]
        if node.transact({'from': deployer, 'data': implementation, 'gas': hex(10000000)}
                         )['receipt']['status'] != '0x1':
            raise HarnessError('implementation deployment failed')
        arguments = encode(['address', 'bytes[]'], [address(SENDER, 0),
                                                    [bytes.fromhex(calldata(f, a)[2:]) for f, a in calls]])
        record = node.transact({'from': deployer, 'data': probe + arguments.hex(), 'gas': hex(10000000)})
        receipt = record['receipt']
        if receipt['status'] != '0x1':
            raise HarnessError('construction probe deployment failed')
        account = receipt['contractAddress']
        if account != address(SENDER, 1):
            raise HarnessError('unexpected probe address')
        oks, results = decode(['bool[]', 'bytes[]'],
                              bytes.fromhex(node.rpc('eth_getCode', account, 'latest')[2:]))
        storage = [[account, slot, node.rpc('eth_getStorageAt', account, slot, 'latest')]
                   for slot in SLOTS]
        events = [{'address': log['address'], 'topics': log['topics'], 'data': log['data']}
                  for log in receipt['logs']]
    rows = [{'status': 'ok' if ok else 'revert', 'data': '0x' + result.hex()}
            for ok, result in zip(oks, results, strict=True)]
    return {'calls': rows, 'events': events, 'storage': storage}


def construction_campaign(directory, routes):
    account = address(SENDER, 1)
    calls = [{'id': str(i), 'function': f, 'args': a, 'sender': SENDER, 'target': account,
              'data': calldata(f, a), 'value': '0x0', 'timestamp': 1000000100 + i,
              'blockNumber': 3 + i} for i, (f, a) in enumerate(CONSTRUCTION_CALLS)]
    observed = {
        'source': probe_route(directory / 'construction-A', routes['source'], routes['probe'],
                              CONSTRUCTION_CALLS),
        'compiled': probe_route(directory / 'construction-C', routes['compiled'], routes['probe'],
                                CONSTRUCTION_CALLS)}
    # No `self_code`: the executing account has no code while its constructor runs.
    rows = Denote(directory / 'construction-B', routes['driver'], account)(
        calls, [[[account, slot] for slot in SLOTS] for _ in calls])
    observed['model'] = {
        'calls': [{'status': row['status'], 'data': row['data']} for row in rows],
        'events': [event for row in rows for event in row['events']],
        'storage': sorted(rows[-1]['storage'])}
    observed['source']['storage'] = sorted(observed['source']['storage'])
    observed['compiled']['storage'] = sorted(observed['compiled']['storage'])
    write_json(directory / 'construction.json', {'transactions': calls, 'observations': observed})
    canonical = {route: {'calls': value['calls'],
                         'events': [{k: (v.lower() if isinstance(v, str) else [t.lower() for t in v])
                                     for k, v in e.items()} for e in value['events']],
                         'storage': [[a.lower(), int(s, 16), int(v, 16)] for a, s, v in value['storage']]}
                 for route, value in observed.items()}
    if not canonical['source'] == canonical['model'] == canonical['compiled']:
        raise Divergence(f'construction divergence: {directory / "construction.json"}')
    initialized = [row['status'] for (f, _), row in zip(CONSTRUCTION_CALLS, canonical['source']['calls'],
                                                         strict=True) if f == 'initialize']
    if initialized != ['ok', 'ok']:
        raise HarnessError(f'construction initialize must succeed twice: {initialized}')
    no_code = [row['data'] for (f, _), row in zip(CONSTRUCTION_CALLS, canonical['source']['calls'],
                                                  strict=True) if f == 'noCode']
    if no_code != ['0x' + '00' * 31 + '01']:
        raise HarnessError(f'constructing account must have no code: {no_code}')
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=48)
    parser.add_argument('--seed', type=int, default=2919)
    parser.add_argument('--shrink-attempts', type=int, default=200)
    parser.add_argument('--source-fixture', type=Path, default=FIXTURE,
                        help='fixture to import in place of the pinned one (mutation checks)')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.transactions < 12:
        parser.error('at least 12 transactions cover the deterministic prefix')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='self-code-length-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=True)
    source = args.source_fixture.read_text()
    routes = compile_routes(output, source, DRIVER.read_text(), SOLC)
    try:
        runtime_campaign(output, routes, args.transactions, args.seed, args.shrink_attempts)
        construction_campaign(output, routes)
    except Divergence as divergence:
        write_json(output / 'divergence.json', {'divergence': str(divergence)})
        print(divergence, file=sys.stderr)
        return 1
    write_json(output / 'summary.json', {
        'passed': True, 'transactions': args.transactions, 'seed': args.seed,
        'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
        'scope': 'address(this).code.length zero tests, runtime and construction contexts: '
                 'source EVM / Denote / compiled model'})
    print(f'self code-length routes agree in runtime and construction contexts: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
