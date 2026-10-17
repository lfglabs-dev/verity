"""Compare functional Lean initcode execution with actual EVM runtime bytes.

This is an EVM/Lean foundation check, not a complete A/B/C deployment campaign:
code deposit, gas, collision and rollback are not part of the Lean transition.
"""
import argparse
import hashlib
import json
from pathlib import Path

from .anvil import Anvil
from .engine import HarnessError, command, write_json
from .programs import initcode_execution_programs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=2500)
    parser.add_argument('--random-cases', type=int, default=16)
    args = parser.parse_args()
    if not 0 <= args.random_cases <= 1000:
        parser.error('random case count must be between zero and 1000')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Verity.Core.Model.InitCodeExecution',
             'Contracts.SolidityImportSmoke.InitCodeExecutionChecks'], log=out / 'build.log')
    programs = initcode_execution_programs(args.seed, args.random_cases)
    write_json(out / 'programs.json', programs)
    inputs = [{key: row[key] for key in ('id', 'fuel', 'code')} for row in programs]
    write_json(out / 'input.json', inputs)
    driver = Path('Contracts/SolidityImportSmoke/InitCodeExecutionDriver.lean')
    command(['lake', 'env', 'lean', '--run', driver, out / 'input.json', out / 'lean.json'],
            log=out / 'lean.log')
    model = json.loads((out / 'lean.json').read_text())
    if len(model) != len(programs):
        raise HarnessError('initcode model omitted results')
    observations = []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        for program, result in zip(programs, model):
            if result.get('id') != program['id'] or result.get('status') != 'returned':
                raise HarnessError('valid initcode did not return or identity changed')
            deployed = node.transact({'from': sender, 'data': '0x' + bytes(program['code']).hex(),
                                      'gas': hex(10000000)})
            receipt = deployed['receipt']
            if receipt['status'] != '0x1':
                raise HarnessError('initcode EVM deployment failed')
            actual = node.rpc('eth_getCode', receipt['contractAddress'], receipt['blockNumber'])
            expected = '0x' + bytes(result['data']).hex()
            observation = {'id': program['id'], 'evm': actual, 'lean': expected,
                           'transactionHash': receipt['transactionHash']}
            observations.append(observation)
            if actual != expected or actual != '0x' + bytes(program['payload']).hex():
                write_json(out / 'divergence.json', {'program': program, 'observation': observation})
                raise HarnessError('EVM/Lean initcode execution divergence')
        write_json(out / 'provenance.json', {'scope': 'EVM/Lean functional execution; not full A/B/C deployment',
                   'node': node.provenance, 'seed': args.seed, 'files': {
                       str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in
                       [driver, Path('Verity/Core/Model/InitCodeExecution.lean'),
                        Path('scripts/solidity_differential/programs.py')]}})
    write_json(out / 'observations.json', observations)
    command(['python3', 'scripts/generate_print_axioms.py', '--check'], log=out / 'axiom-generator.log')
    write_json(out / 'complete.json', {'exit': 0, 'scope': 'functional initcode only; no importer/deployment claim',
                                      'programs': len(programs), 'variants': 2})
    print(f'Initcode EVM/Lean agree on {len(programs)} executions with two bytecode variants')


if __name__ == '__main__':
    main()
