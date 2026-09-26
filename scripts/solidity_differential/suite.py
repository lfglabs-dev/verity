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
    checks = [
        ('protocol', ['-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_solidity_stateful*.py']),
        ('anvil', ['-m', 'solidity_differential.check_anvil']),
        ('mocks', ['-m', 'solidity_differential.check_mocks']),
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
    for fixture in ('void', 'bytes'):
        checks.append(('storage-' + fixture, ['-m', 'solidity_differential.check_storage',
            '--fixture', fixture, '--transactions', str(transactions), '--seed', str(seed),
            '--output', str(output / ('storage-' + fixture))]))
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
