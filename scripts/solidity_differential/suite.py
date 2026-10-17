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
             'Contracts/SolidityImportSmoke/CallRefusal.lean'],
            log=output / 'call-refusal-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/IRCreationChecks.lean'],
            log=output / 'ir-creation-checks.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/TypedAccessChecks.lean'],
            log=output / 'typed-access-checks.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/SourceHelperRefusal.lean'],
            log=output / 'source-helper-refusal-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/SourceExpressionOutcomeChecks.lean'],
            log=output / 'source-expression-outcome-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/SourceExpressionEvaluationChecks.lean'],
            log=output / 'source-expression-evaluation-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/SourceStatementEvaluationChecks.lean'],
            log=output / 'source-statement-evaluation-smoke.log')
    command(['lake', 'env', 'lean', '--run',
             'Contracts/SolidityImportSmoke/NativeCreationBoundaryChecks.lean'],
            log=output / 'native-creation-boundary-smoke.log')
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
        ('account-inputs', ['-m', 'solidity_differential.check_account_inputs',
            '--output', str(output / 'account-inputs')]),
        ('mocks', ['-m', 'solidity_differential.check_mocks']),
        ('emit-rejections', ['-m', 'solidity_differential.check_emit_rejections']),
        ('rejections', ['-m', 'solidity_differential.check_denote_rejections']),
        ('mutations', ['-m', 'solidity_differential.check_stateful_mutations']),
        ('event-mutations', ['-m', 'solidity_differential.check_event_mutations']),
        ('call-refusal-mutations', ['-m', 'solidity_differential.check_call_refusal_mutations',
            '--output', str(output / 'call-refusal-mutations')]),
        ('source-creation-mutations', ['-m', 'solidity_differential.check_source_creation_mutations',
            '--output', str(output / 'source-creation-mutations')]),
        ('native-prepared-creation', ['-m', 'solidity_differential.check_native_prepared_creation',
            '--output', str(output / 'native-prepared-creation')]),
        ('revert-payload-programs', ['-m', 'solidity_differential.check_revert_payload_programs',
                                    '--output', str(output / 'revert-payload-programs')]),
        ('internal-return-memory-programs', ['-m', 'solidity_differential.check_internal_return_memory_programs',
            '--output', str(output / 'internal-return-memory-programs')]),
        ('ir-revert-programs', ['-m', 'solidity_differential.check_ir_revert_programs',
            '--output', str(output / 'ir-revert-programs')]),
        ('ir-memory-programs', ['-m', 'solidity_differential.check_ir_memory_programs',
            '--output', str(output / 'ir-memory-programs')]),
        ('ir-creation-mutations', ['-m', 'solidity_differential.check_ir_creation_mutations',
            '--output', str(output / 'ir-creation-mutations')]),
        ('typed-access-mutations', ['-m', 'solidity_differential.check_typed_access_mutations',
            '--output', str(output / 'typed-access-mutations')]),
        ('source-typed-evaluation-mutations', ['-m', 'solidity_differential.check_source_typed_evaluation_mutations',
            '--output', str(output / 'source-typed-evaluation-mutations')]),
        ('source-expression-mutations', ['-m', 'solidity_differential.check_source_expression_mutations',
            '--output', str(output / 'source-expression-mutations')]),
        ('source-helper-refusal-mutations', ['-m', 'solidity_differential.check_source_helper_refusal_mutations',
            '--output', str(output / 'source-helper-refusal-mutations')]),
        ('native-creation-mutations', ['-m', 'solidity_differential.check_native_creation_mutations',
            '--output', str(output / 'native-creation-mutations')]),
    ]
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
    for fixture in ('void', 'bytes', 'mapping', 'short-circuit', 'imported-event', 'narrow-event', 'if-else', 'numeric-literals', 'constant-arrays', 'modulo'):
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
    checks.append(('errors', ['-m', 'solidity_differential.check_stateful',
        '--transactions', str(transactions), '--seed', str(seed),
        '--source-fixture', 'scripts/solidity_differential/fixtures/ErrorSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/ErrorSequenceModel.lean',
        '--output', str(output / 'errors')]))
    return run_checks(output, checks, transactions, seed)


def run_checks(output, checks, transactions, seed):
    """Run named checks in order, printing each one before it starts.

    ``command`` captures subprocess output until the process exits, so a
    multi-check campaign otherwise looks idle for its whole wall time.
    """
    completed = []
    total = len(checks)
    for index, (name, args) in enumerate(checks, start=1):
        print(f'stateful check {index}/{total}: {name}', flush=True)
        # The primary script installs scripts/ on sys.path, but subprocess modules
        # need it explicitly; use a small launcher without altering caller state.
        launcher = ('import os,runpy,sys; sys.path.insert(0,"scripts"); '
                    'os.environ["PYTHONPATH"]=os.path.abspath("scripts")+os.pathsep+os.environ.get("PYTHONPATH",""); '
                    'module=sys.argv.pop(1); runpy.run_module(module,run_name="__main__")')
        argv = [sys.executable, '-c', launcher, args[1], *args[2:]]
        command(argv, timeout=1800, log=output / f'{name}.log')
        completed.append(name)
        write_json(output / 'completed.json', completed)
        print(f'stateful check {index}/{total}: {name} done', flush=True)
    return {'checks': completed, 'transactionsPerVariant': transactions, 'seed': seed,
            'divergences': []}
