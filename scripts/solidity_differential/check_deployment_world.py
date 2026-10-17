"""Real EVM versus threaded Lean account-world transition calibration.

No compiled-model route, imported CREATE2 or ABI/event equivalence is claimed.
The world protocol continuation is independently derived from fixture inputs.
"""
import argparse
import json
from pathlib import Path

from .anvil import Anvil
from .engine import MUTANT_BUILD_TIMEOUT, HarnessError, command, solc_compile, write_json

PREFIX = bytes.fromhex('600b380380600b5f395ff3')


def calldata(selector, salt, payload, fail, value, require):
    words = [salt, 160, int(fail), value, int(require), len(payload)]
    return '0x' + selector + ''.join(format(word, '064x') for word in words) + (
        payload + bytes((-len(payload)) % 32)).hex()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--parent-opcode', action='store_true', help='derive initcode and child gas in Lean from actual parent memory/gas')
    parser.add_argument('--nonce-max', action='store_true', help='start the creator at the EIP-2681 nonce limit')
    parser.add_argument('--case-ids', type=int, nargs='*', help='replay a subset from the unchanged initial world')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Verity.Core.Model.DenoteCreate2', 'Compiler.SolidityImport.Transactions'],
            timeout=MUTANT_BUILD_TIMEOUT, log=out / 'build.log')
    if args.parent_opcode:
        command(['lake', 'build', 'Contracts.SolidityImportSmoke.Create2OpcodeChecks'],
                log=out / 'opcode-build.log')
    fixture = Path(__file__).parent / 'fixtures/DeploymentWorld.sol'
    request = {'language': 'Solidity', 'sources': {'DeploymentWorld.sol': {'content': fixture.read_text()}},
               'settings': {'evmVersion': 'osaka', 'viaIR': True,
                            'optimizer': {'enabled': True, 'runs': 466},
                            'metadata': {'bytecodeHash': 'none'},
                            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    evm = solc_compile(request, fixture.parent, out / 'source')['contracts']['DeploymentWorld.sol']['DeploymentWorldFixture']['evm']
    selector = evm['methodIdentifiers']['deploy(bytes32,bytes,bool,uint256,bool)']
    # salt,payload,failAfter,value,requireSuccess,case
    cases = [(11, b'\x00\x01\x02', False, 11, True, 'prefunded-success'),
             (11, b'\x00\x01\x02', False, 11, False, 'collision-in-band'),
             (12, b'\x00', True, 5, True, 'parent-rollback'),
             (13, b'\xef\x01', False, 0, False, 'forbidden-prefix'),
             (14, b'\x00', False, 10000, False, 'insufficient-balance'),
             (15, b'\x00', False, 0, False, 'nonce-collision'),
             (16, b'\x00', False, 0, False, 'code-collision'),
             (17, b'\x00\x07\x08', False, 3, True, 'storage-only-creation'),
             (18, b'', False, 0, True, 'empty-runtime'),
             (18, b'', False, 0, False, 'empty-runtime-collision'),
             (19, bytes(range(65)), False, 0, True, 'multiword-payload')]
    selected = list(range(len(cases))) if args.case_ids is None else args.case_ids
    if len(set(selected)) != len(selected) or any(index not in range(len(cases)) for index in selected):
        parser.error('case ids must be unique valid indices')
    observations, steps = [], []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployment = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(10000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('deployment-world fixture failed to deploy')
        creator = deployment['receipt']['contractAddress']
        def candidate(salt, payload):
            digest = node.rpc('web3_sha3', '0x' + (PREFIX + payload).hex())
            return '0x' + node.rpc('web3_sha3', '0xff' + creator[2:] + format(salt, '064x') + digest[2:])[-40:]
        targets = [candidate(salt, payload) for salt, payload, *_ in cases]
        addresses = sorted({creator, *targets})
        slot = '0x' + format(7, '064x')
        node.rpc('anvil_setBalance', creator, hex(50))
        if args.nonce_max:
            node.rpc('anvil_setNonce', creator, hex((1 << 64) - 1))
        node.rpc('anvil_setBalance', targets[0], hex(7))
        node.rpc('anvil_setNonce', targets[5], '0x1')
        node.rpc('anvil_setCode', targets[6], '0x00')
        node.rpc('anvil_setStorageAt', targets[7], slot, '0x' + format(1, '064x'))
        def sample(block):
            return [{'address': str(int(addr, 16)),
                'nonce': str(int(node.rpc('eth_getTransactionCount', addr, block), 16)),
                'balance': str(int(node.rpc('eth_getBalance', addr, block), 16)),
                'code': list(bytes.fromhex(node.rpc('eth_getCode', addr, block)[2:])),
                'storage': [['7', str(int(node.rpc('eth_getStorageAt', addr, slot, block), 16))]]}
                for addr in addresses]
        initial = sample('latest')
        for index, (salt, payload, fail, value, require, kind) in enumerate(cases):
            if index not in selected:
                continue
            record = node.transact({'from': sender, 'to': creator, 'gas': hex(10000000),
                                   'data': calldata(selector, salt, payload, fail, value, require)})
            frames = [frame for frame in record['call'].get('calls', []) if frame.get('type') == 'CREATE2']
            if len(frames) > 1:
                raise HarnessError('unexpected multiple creation frames')
            # Geth's opcode gasCost includes the EIP-150 forwarded allowance,
            # even when prechecks prevent a child frame from being traced.
            # Recover it from actual stack/memory/gas, never supply a default.
            trace = node.rpc('debug_traceTransaction', record['receipt']['transactionHash'],
                             {'disableStorage': True, 'disableStack': False, 'enableMemory': True})
            write_json(out / 'node' / (record['receipt']['transactionHash'] + '.create2-gas.json'), trace)
            instructions = [step for step in trace['structLogs'] if step['op'] == 'CREATE2']
            if len(instructions) != 1:
                raise HarnessError('exactly one CREATE2 opcode context required')
            instruction = instructions[0]
            amount, offset, size, actual_salt = (int(word, 16) for word in reversed(instruction['stack'][-4:]))
            memory = bytes.fromhex(''.join(word.removeprefix('0x') for word in instruction['memory']))
            code = memory[offset:offset + size]
            code += bytes(size - len(code))
            if amount != value or actual_salt != salt or code != PREFIX + payload:
                raise HarnessError('CREATE2 opcode inputs differ from transaction fixture')
            old_words = len(instruction['memory'])
            new_words = max(old_words, (offset + size + 31) // 32) if size else old_words
            memory_cost = lambda words: 3 * words + words * words // 512
            opcode_cost = 32000 + 8 * ((size + 31) // 32) + memory_cost(new_words) - memory_cost(old_words)
            child_gas = instruction['gasCost'] - opcode_cost
            after_opcode = instruction['gas'] - opcode_cost
            if child_gas < 0 or child_gas != after_opcode - after_opcode // 64:
                raise HarnessError('CREATE2 opcode gas and EIP-150 allowance differ')
            if frames and int(frames[0]['gas'], 16) != child_gas:
                raise HarnessError('opcode and child-call gas allowance differ')
            steps.append({'id': str(index), 'salt': str(salt), 'value': str(value),
                          'code': list(PREFIX + payload), 'childGas': str(child_gas),
                          'failAfter': fail, 'requireSuccess': require,
                          'observations': [{'address': str(int(addr, 16)), 'slots': ['7']} for addr in addresses]})
            if args.parent_opcode:
                parent_index = trace['structLogs'].index(instruction)
                after = next((row for row in trace['structLogs'][parent_index + 1:]
                              if row['depth'] == instruction['depth']), None)
                if after is None:
                    raise HarnessError('CREATE2 parent continuation missing from opcode trace')
                steps[-1].pop('childGas')
                steps[-1].pop('code')
                steps[-1].update({'parentGas': str(instruction['gas']),
                    'offset': str(offset), 'size': str(size), 'memory': list(memory)})
                parent_expected = {'childGas': str(child_gas), 'parentGasLeft': str(after['gas']),
                                   'memoryWords': str(new_words)}
            observations.append({'id': str(index), 'case': kind,
                'status': 'ok' if record['receipt']['status'] == '0x1' else 'revert',
                'address': str(int(record['call'].get('output', '0x0'), 16)) if record['receipt']['status'] == '0x1' else None,
                'childGasLeft': str(int(frames[0]['gas'], 16) - int(frames[0]['gasUsed'], 16)) if frames else None,
                'accounts': sample(record['receipt']['blockNumber']),
                'transactionHash': record['receipt']['transactionHash']})
            if args.parent_opcode:
                observations[-1].update(parent_expected)
        write_json(out / 'node-provenance.json', node.provenance)
    write_json(out / 'input.json', {'creator': str(int(creator, 16)), 'initialAccounts': initial, 'steps': steps})
    write_json(out / 'source-observations.json', observations)
    driver = Path('Contracts/SolidityImportSmoke/Create2OpcodeDriver.lean' if args.parent_opcode
                  else 'Contracts/SolidityImportSmoke/DeploymentWorldDriver.lean')
    command(['lake', 'env', 'lean', '--run', driver, out / 'input.json', out / 'model-observations.json'],
            log=out / 'model.log')
    model = json.loads((out / 'model-observations.json').read_text())
    if len(model) != len(observations):
        raise HarnessError('account model omitted sequence results')
    for actual, expected in zip(model, observations):
        same = actual['id'] == expected['id'] and actual['status'] == expected['status'] and actual['accounts'] == expected['accounts']
        if expected['status'] == 'ok': same = same and actual['address'] == expected['address']
        if expected['childGasLeft'] is not None: same = same and actual['childGasLeft'] == expected['childGasLeft']
        if args.parent_opcode:
            same = same and all(actual[key] == expected[key]
                                for key in ['childGas', 'parentGasLeft', 'memoryWords'])
        if not same:
            write_json(out / 'divergence.json', {'actual': actual, 'expected': expected})
            raise HarnessError('EVM/Lean account-world divergence')
    write_json(out / 'complete.json', {'exit': 0, 'transactions': len(selected),
        'scope': 'threaded EVM/Lean account and child-gas calibration; no imported/full ABC/ABI-event claim'})
    if args.parent_opcode:
        write_json(out / 'opcode-complete.json', {'exit': 0, 'transactions': len(selected),
            'scope': 'live EVM versus Lean opcode/world/gas; no canonical Stmt/importer/C or ABI/events claim'})
    print(f'Deployment world agrees on {len(selected)} actual EVM calls')


if __name__ == '__main__':
    main()
