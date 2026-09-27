"""Repository/CI entry point for the stateful differential instrument."""
from pathlib import Path
import sys

from .engine import HarnessError, command, write_json


def stateful_campaign(output, transactions, seed):
    if transactions < 3:
        raise HarnessError('stateful campaign requires at least three transactions')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    # Finish all compilation before taking executable snapshots in adapters.
    command(['lake', 'build', 'SolidityImportSmoke', 'Compiler.Codegen',
             'Compiler.Yul.PrettyPrint'], timeout=1800, log=output / 'build.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/Transactions.lean'],
            log=output / 'transaction-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/EventRejections.lean'],
            log=output / 'event-rejections.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/ErrorPayloads.lean'],
            log=output / 'error-payloads.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/StorageTraceChecks.lean'],
            log=output / 'storage-trace-checks.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/ExplicitAbiChecks.lean'],
            log=output / 'explicit-abi-checks.log')
    checks = [
        ('protocol', ['-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_solidity_stateful*.py']),
        ('anvil', ['-m', 'solidity_differential.check_anvil']),
        ('mocks', ['-m', 'solidity_differential.check_mocks']),
        ('emit-rejections', ['-m', 'solidity_differential.check_emit_rejections']),
        ('rejections', ['-m', 'solidity_differential.check_denote_rejections']),
        ('mutations', ['-m', 'solidity_differential.check_stateful_mutations']),
        ('event-mutations', ['-m', 'solidity_differential.check_event_mutations']),
    ]
    for variant in ('baseline', 'scoped', 'early-return'):
        checks.append((variant, ['-m', 'solidity_differential.check_stateful',
            '--transactions', str(transactions), '--seed', str(seed), '--variant', variant,
            '--output', str(output / variant)]))
    for variant in ('baseline', 'scoped', 'early-return'):
        checks.append(('events-' + variant, ['-m', 'solidity_differential.check_stateful',
            '--transactions', str(transactions), '--seed', str(seed), '--variant', variant,
            '--source-fixture', 'scripts/solidity_differential/fixtures/EventSequence.sol',
            '--model-driver', 'Contracts/SolidityImportSmoke/EventSequenceModel.lean',
            '--output', str(output / ('events-' + variant))]))
    checks.append(('environment', ['-m', 'solidity_differential.check_environment',
        '--transactions', str(transactions), '--seed', str(seed),
        '--output', str(output / 'environment')]))
    checks.append(('storage', ['-m', 'solidity_differential.check_storage',
        '--transactions', str(transactions), '--seed', str(seed),
        '--output', str(output / 'storage')]))
    for fixture in ('void', 'bytes', 'mapping', 'short-circuit', 'imported-event', 'narrow-event'):
        checks.append(('storage-' + fixture, ['-m', 'solidity_differential.check_storage',
            '--fixture', fixture, '--transactions', str(transactions), '--seed', str(seed),
            '--output', str(output / ('storage-' + fixture))]))
    checks.append(('mapping-dirty', ['-m', 'solidity_differential.check_stateful',
        '--dirty-mappings', '--transactions', str(max(5, transactions)), '--seed', str(seed),
        '--source-fixture', 'Contracts/SolidityImportSmoke/MappingDirtySequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/MappingDirtySequenceModel.lean',
        '--output', str(output / 'mapping-dirty')]))
    checks.append(('abi', ['-m', 'solidity_differential.check_abi_programs',
        '--output', str(output / 'abi')]))
    checks.append(('abi-rejections', ['-m', 'solidity_differential.check_abi_rejections']))
    checks.append(('struct-abi', ['-m', 'solidity_differential.check_struct_abi_programs',
        '--output', str(output / 'struct-abi')]))
    checks.append(('struct-abi-rejections', ['-m', 'solidity_differential.check_struct_abi_rejections']))

    for bits in (8, 16, 248):
        checks.append(('narrow-event-' + str(bits), ['-m', 'solidity_differential.check_storage',
            '--fixture', 'narrow-event', '--narrow-bits', str(bits),
            '--transactions', str(transactions), '--seed', str(seed),
            '--output', str(output / ('narrow-event-' + str(bits)))]))


    checks.append(('scalar-array-abi', ['-m', 'solidity_differential.check_scalar_array_abi_programs',
        '--output', str(output / 'scalar-array-abi')]))
    checks.append(('scalar-array-abi-rejections', ['-m', 'solidity_differential.check_scalar_array_abi_rejections',
        '--output', str(output / 'scalar-array-abi-rejections')]))
    checks.append(('market-abi', ['-m', 'solidity_differential.check_market_abi_programs',
        '--output', str(output / 'market-abi')]))
    checks.append(('market-abi-rejections', ['-m', 'solidity_differential.check_market_abi_rejections',
        '--output', str(output / 'market-abi-rejections')]))
    checks.append(('block-rejections', ['-m', 'solidity_differential.check_block_rejections',
        '--output', str(output / 'block-rejections')]))
    checks.append(('abi-event-composition', ['-m', 'solidity_differential.check_abi_event_composition',
        '--output', str(output / 'abi-event-composition')]))
    checks.append(('multiple-dynamic-abi', ['-m', 'solidity_differential.check_multiple_dynamic_abi_programs',
        '--output', str(output / 'multiple-dynamic-abi')]))
    completed = []
    checks.append(('errors', ['-m', 'solidity_differential.check_stateful',
        '--transactions', str(transactions), '--seed', str(seed),
        '--source-fixture', 'scripts/solidity_differential/fixtures/ErrorSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/ErrorSequenceModel.lean',
        '--output', str(output / 'errors')]))
    for name, args in checks:
        # The primary script installs scripts/ on sys.path, but subprocess modules
        # need it explicitly; use a small launcher without altering caller state.
        launcher = ('import os,runpy,sys; sys.path.insert(0,"scripts"); '
                    'os.environ["PYTHONPATH"]=os.path.abspath("scripts")+os.pathsep+os.environ.get("PYTHONPATH",""); '
                    'module=sys.argv.pop(1); runpy.run_module(module,run_name="__main__")')
        argv = [sys.executable, '-c', launcher, args[1], *args[2:]]
        command(argv, timeout=1800, log=output / f'{name}.log')
        completed.append(name)
        write_json(output / 'completed.json', completed)
    return {'checks': completed, 'transactionsPerVariant': transactions, 'seed': seed,
            'divergences': []}
