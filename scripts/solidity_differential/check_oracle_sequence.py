"""Whole-model oracle sequence validation; manual model, importer still pending."""
import argparse
import hashlib
import os
from pathlib import Path
import random
import tempfile

from eth_abi import encode
from eth_utils import keccak
import rlp

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--solc', type=Path, default=SOLC)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2461)
    args = parser.parse_args()
    if args.transactions < 5:
        parser.error('at least five transactions required to cover every target')
    root = Path.cwd()
    out = Path(tempfile.mkdtemp(prefix='oracle-sequence-', dir='.lake')).resolve()
    fixture = root / 'test/ByteExternalCall/RawStaticOracle.sol'
    driver = root / 'test/ByteExternalCall/OracleSequenceModel.lean'
    os.environ['LEAN_PATH'] = (root / '.lake/physical-lean-path').read_text()
    os.environ['LEAN_NUM_THREADS'] = '1'
    contracts = solc_compile({
        'language': 'Solidity', 'sources': {fixture.name: {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True,
                     'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}},
    }, fixture.parent, out / 'solc', solc=args.solc)['contracts'][fixture.name]
    selectors = contracts['OracleSequenceCaller']['evm']['methodIdentifiers']
    selector = selectors['read(address,uint256)']
    reject_selector = selectors['readAndReject(address,uint256,uint256)']
    write_json(out / 'selectors.json', [int(selector, 16), int(reject_selector, 16)])
    command(['lean', '-j', '1', '--run', driver, 'compile', out / 'selectors.json', out / 'model.yul'],
            log=out / 'compile.log')
    generated = solc_compile({
        'language': 'Yul', 'sources': {'Caller.yul': {'content': (out / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, out, out / 'compiled-solc', solc=args.solc)['contracts']['Caller.yul']
    if len(generated) != 1:
        raise RuntimeError('expected one compiled model')
    caller_a = '0x' + contracts['OracleSequenceCaller']['evm']['bytecode']['object']
    caller_c = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    sender = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'

    def address(nonce):
        return '0x' + keccak(rlp.encode([bytes.fromhex(sender[2:]), nonce]))[-20:].hex()

    caller = address(0)
    parameters = [(42, False, 32), (2**256-1, False, 31),
                  (2**256-1, False, 65), (42, True, 65)]
    accounts = [address(i+1) for i in range(len(parameters))]
    oracles = ['0x' + contracts['RawStaticOracle']['evm']['bytecode']['object'] +
               encode(['uint256', 'bool', 'uint256'], p).hex() for p in parameters]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(),
                '0x' + int(value).to_bytes(32, 'big').hex())
               for account, p in zip(accounts, parameters, strict=True)
               for slot, value in enumerate(p)]
    targets = [*accounts, '0x' + '00'*19 + '77']
    rng = random.Random(args.seed)
    transactions = []
    for i in range(args.transactions):
        target = targets[i] if i < len(targets) else rng.choice(targets)
        next_value = rng.getrandbits(256)
        reject_call = i % 2 == 0
        # The first successful target rejects with a nonempty live return buffer.
        rejected = 1 if i == 0 else rng.getrandbits(1)
        function = 'readAndReject' if reject_call else 'read'
        words = [int(target, 16), next_value] + ([rejected] if reject_call else [])
        types = ['address', 'uint256'] + (['uint256'] if reject_call else [])
        values = [target, next_value] + ([rejected] if reject_call else [])
        transactions.append({'id': str(i), 'function': function,
            'args': words, 'sender': sender, 'target': caller,
            'data': '0x' + (reject_selector if reject_call else selector) + encode(types, values).hex(),
            'value': '0x0', 'timestamp': 1000000100+i, 'blockNumber': len(oracles)+2+i})
    write_json(out / 'transactions.json', transactions)
    adapters = {
        'source': EVM(out / 'A', [caller_a, *oracles], initial),
        'model': Denote(out / 'B', driver, caller, initial,
                    byte_call_environment={'program': 'raw-static-oracle-v1',
                        'accounts': [str(int(a, 16)) for a in accounts],
                        'emptyAccounts': ['119'], 'gas': '100000'},
                    lean_command=('lean', '-j', '1', '--run')),
        'compiled': EVM(out / 'C', [caller_c, *oracles], initial)}
    write_json(out / 'identity.json', adapters['model'].identity.manifest)
    result = replay_three_routes(transactions, adapters)
    write_json(out / 'result.json', result)
    if result['divergences']:
        reduced = shrink_sequence(transactions, lambda txs: replay_three_routes(txs, adapters)['divergences'])
        write_json(out / 'minimal.json', reduced)
        raise RuntimeError(f'oracle sequence divergence: {out}')
    write_json(out / 'summary.json', {'passed': True, 'transactions': len(transactions),
        'seed': args.seed, 'scope': 'source EVM / independent Denote / whole compiled manual model',
        'fixtureSha256': hashlib.sha256(fixture.read_bytes()).hexdigest(),
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest()})
    print(f'{len(transactions)} whole-model oracle A/B/C transactions passed: {out}')


if __name__ == '__main__':
    main()
