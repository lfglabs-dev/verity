"""Repository/CI entry point for the stateful differential instrument."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import sys

from .engine import HarnessError, command, write_json


def stateful_campaign(output, transactions, seed, jobs=1):
    if transactions < 3:
        raise HarnessError('stateful campaign requires at least three transactions')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    # Finish all compilation before taking executable snapshots in adapters.
    command(['lake', 'build', 'SolidityImportSmoke', 'Compiler.Codegen',
             'Compiler.Yul.PrettyPrint', 'Compiler.SolidityImport.SequenceRunner',
             'Compiler.SolidityImport.StaticOracleMocks'], timeout=1800, log=output / 'build.log')
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
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/SelectorIdentityChecks.lean'],
            log=output / 'selector-identity-checks.log')
    checks = [
        ('protocol', ['-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_solidity_stateful*.py']),
        ('anvil', ['-m', 'solidity_differential.check_anvil']),
        ('mocks', ['-m', 'solidity_differential.check_mocks']),
        ('emit-rejections', ['-m', 'solidity_differential.check_emit_rejections']),
        ('rejections', ['-m', 'solidity_differential.check_denote_rejections']),
        ('mutations', ['-m', 'solidity_differential.check_stateful_mutations']),
        ('event-mutations', ['-m', 'solidity_differential.check_event_mutations']),
    ]
    checks.append(('pinned-sequence', ['-m', 'solidity_differential.check_pinned_sequence_fixture',
        '--transactions', str(max(64, transactions)), '--seed', str(seed),
        '--output', str(output / 'pinned-sequence')]))
    checks.append(('create2-parent-opcode', ['-m', 'solidity_differential.check_deployment_world',
        '--parent-opcode', '--output', str(output / 'create2-parent-opcode')]))
    checks.append(('hashing-programs', ['-m', 'solidity_differential.check_hashing_programs',
        '--output', str(output / 'hashing-programs')]))
    checks.append(('hashing-rejections', ['-m', 'solidity_differential.check_hashing_rejections',
        '--output', str(output / 'hashing-rejections')]))
    checks.append(('reference-arguments', ['-m', 'solidity_differential.check_reference_arguments',
        '--output', str(output / 'reference-arguments')]))
    checks.append(('reference-rejections', ['-m', 'solidity_differential.check_reference_argument_rejections',
        '--output', str(output / 'reference-rejections')]))
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
    checks.append(('storage-yul-numeric', ['-m', 'solidity_differential.check_storage',
        '--fixture', 'yul-numeric', '--transactions', str(max(64, transactions)),
        '--seed', str(seed), '--output', str(output / 'storage-yul-numeric')]))
    for fixture in ('void', 'bytes', 'mapping', 'short-circuit', 'imported-event', 'narrow-event', 'if-else', 'numeric-literals', 'constant-arrays', 'modulo', 'unchecked-blocks', 'tuple-destructuring'):
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
    checks.append(('nested-dynamic-struct-abi', ['-m', 'solidity_differential.check_nested_dynamic_struct_abi_programs',
        '--output', str(output / 'nested-dynamic-struct-abi')]))
    checks.append(('nested-dynamic-struct-abi-rejections', ['-m', 'solidity_differential.check_nested_dynamic_struct_abi_rejections',
        '--output', str(output / 'nested-dynamic-struct-abi-rejections')]))
    checks.append(('block-rejections', ['-m', 'solidity_differential.check_block_rejections',
        '--output', str(output / 'block-rejections')]))
    checks.append(('abi-event-composition', ['-m', 'solidity_differential.check_abi_event_composition',
        '--output', str(output / 'abi-event-composition')]))
    checks.append(('multiple-dynamic-abi', ['-m', 'solidity_differential.check_multiple_dynamic_abi_programs',
        '--output', str(output / 'multiple-dynamic-abi')]))
    checks.append(('errors', ['-m', 'solidity_differential.check_stateful',
        '--transactions', str(transactions), '--seed', str(seed),
        '--source-fixture', 'scripts/solidity_differential/fixtures/ErrorSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/ErrorSequenceModel.lean',
        '--output', str(output / 'errors')]))
    checks.append(('checked-oracle-mock', ['-m', 'solidity_differential.check_checked_static_oracle_mock']))
    checks.append(('interface-static-call', ['-m', 'solidity_differential.check_interface_static_call',
        '--transactions', str(max(64, transactions)), '--seed', str(seed),
        '--output', str(output / 'interface-static-call')]))
    checks.append(('interface-static-call-rejections', ['-m',
        'solidity_differential.check_interface_static_call_rejections',
        '--output', str(output / 'interface-static-call-rejections')]))
    checks.append(('create2-struct-emit', ['-m', 'solidity_differential.check_create2_struct_emit',
        '--transactions', str(max(32, min(transactions, 48))), '--seed', str(seed),
        '--output', str(output / 'create2-struct-emit')]))
    checks.append(('create2-struct-emit-rejections', ['-m',
        'solidity_differential.check_create2_struct_emit_rejections',
        '--output', str(output / 'create2-struct-emit-rejections')]))
    return run_checks(output, checks, transactions, seed, jobs)


def run_checks(output, checks, transactions, seed, jobs=1):
    """Run named checks, printing each one before it starts.

    ``command`` captures subprocess output until the process exits, so a
    multi-check campaign otherwise looks idle for its whole wall time.
    Checks write separate output directories and only read the shared Lake
    build (prepared up front by ``stateful_campaign``), so up to ``jobs`` of
    them run at once. Completion is still recorded in check order, and the
    first failure in that order is raised once every started check finished.
    """
    completed = []
    total = len(checks)
    # The primary script installs scripts/ on sys.path, but subprocess modules
    # need it explicitly; use a small launcher without altering caller state.
    launcher = ('import os,runpy,sys; sys.path.insert(0,"scripts"); '
                'os.environ["PYTHONPATH"]=os.path.abspath("scripts")+os.pathsep+os.environ.get("PYTHONPATH",""); '
                'module=sys.argv.pop(1); runpy.run_module(module,run_name="__main__")')

    def run(index, name, args):
        print(f'stateful check {index}/{total}: {name}', flush=True)
        argv = [sys.executable, '-c', launcher, args[1], *args[2:]]
        command(argv, timeout=1800, log=output / f'{name}.log')
        print(f'stateful check {index}/{total}: {name} done', flush=True)

    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        futures = [pool.submit(run, index, name, args)
                   for index, (name, args) in enumerate(checks, start=1)]
        try:
            for (name, _), future in zip(checks, futures):
                future.result()
                completed.append(name)
                write_json(output / 'completed.json', completed)
        finally:
            for future in futures:
                future.cancel()
    return {'checks': completed, 'transactionsPerVariant': transactions, 'seed': seed,
            'divergences': []}
