"""Repository/CI entry point for the stateful differential instrument."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import sys

from .engine import HarnessError, command, write_json


# check_storage fixtures run with default arguments, one `storage-<fixture>` check each.
# One entry per line (in run order), so PRs adding different fixtures do not touch the same line.
STORAGE_FIXTURES = (
    'void',
    'bytes',
    'mapping',
    'short-circuit',
    'imported-event',
    'narrow-event',
    'if-else',
    'numeric-literals',
    'constant-arrays',
    'modulo',
    'signed-modulo',
    'signed-compound-assignment',
    'signed-struct-compound',
    'byte-constant-conversions',
    'narrow-for-counters',
    'predeclared-for-counters',
    'storage-array-length-bound',
    'helper-loop-break',
    'helper-loop-return',
    'fixed-bytes-conversions',
    'fixed-bytes-widths',
    'msg-sig',
    'yul-empty-revert',
    'yul-revert-memory',
    'yul-mcopy',
    'signed-struct-member-read',
    'packed-signed-int',
    'fixed-memory-arrays',
    'inline-array-literals',
    'helper-name-independence',
    'call-arg-side-effects',
    'struct-param-slot',
    'dynamic-memory-arrays',
    'unchecked-blocks',
    'tuple-destructuring',
    'event-nested-mapping-read',
    'storage-string-members',
    'nested-memory-struct-return',
    'struct-memory-array-helpers',
    'signed-narrow-values',
    'signed-custom-errors',
)

def stateful_campaign(output, transactions, seed, jobs=1):
    if transactions < 3:
        raise HarnessError('stateful campaign requires at least three transactions')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    # Finish all compilation before taking executable snapshots in adapters.
    command(['lake', 'build', 'SolidityImportSmoke', 'Compiler.Codegen',
             'Compiler.Yul.PrettyPrint', 'Compiler.SolidityImport.SequenceRunner',
             'Compiler.SolidityImport.StaticOracleMocks',
             'Compiler.SolidityImport.CallResponderMocks',
             'Compiler.SolidityImport.ReentrantCallResponderMocks',
             'Compiler.SolidityImport.ModelResponders'], timeout=1800, log=output / 'build.log')
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
             'Contracts/SolidityImportSmoke/TerminalErrorGuard.lean'],
            log=output / 'terminal-error-guard.log')
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
    checks.append(('pinned-sequence-corpus', ['-m', 'solidity_differential.check_pinned_sequence_corpus',
        '--transactions', str(max(128, transactions)), '--seed', str(seed), '--fetch',
        '--output', str(output / 'pinned-sequence-corpus')]))
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
    checks.append(('storage-bytes-named-return-slice-struct', ['-m', 'solidity_differential.check_storage',
        '--fixture', 'bytes-named-return-slice-struct', '--transactions', str(max(96, transactions)),
        '--seed', str(seed), '--output', str(output / 'storage-bytes-named-return-slice-struct')]))
    checks.append(('storage-bytes-named-return-stateless', ['-m', 'solidity_differential.check_storage',
        '--fixture', 'bytes-named-return-stateless', '--transactions', str(max(96, transactions)),
        '--seed', str(seed), '--output', str(output / 'storage-bytes-named-return-stateless')]))
    checks.append(('storage-named-string-return', ['-m', 'solidity_differential.check_storage',
        '--fixture', 'named-string-return', '--transactions', str(max(64, transactions)),
        '--seed', str(seed), '--output', str(output / 'storage-named-string-return')]))
    for fixture in ('struct-string-member-param', 'struct-array-param', 'bytes-array-param'):
        # Root ABI parameters: the full deterministic call list (well-formed
        # and malformed ABI inputs) runs before the random calls.
        checks.append(('storage-' + fixture, ['-m', 'solidity_differential.check_storage',
            '--fixture', fixture, '--transactions', str(max(200, transactions)),
            '--seed', str(seed), '--output', str(output / ('storage-' + fixture))]))
    for fixture in ('dynamic-array-root-returns', 'dynamic-array-root-returns-stateless'):
        checks.append(('storage-' + fixture, ['-m', 'solidity_differential.check_storage',
            '--fixture', fixture, '--transactions', str(max(64, transactions)),
            '--seed', str(seed), '--output', str(output / ('storage-' + fixture))]))
    for fixture in STORAGE_FIXTURES:
        checks.append(('storage-' + fixture, ['-m', 'solidity_differential.check_storage',
            '--fixture', fixture, '--transactions', str(transactions), '--seed', str(seed),
            '--output', str(output / ('storage-' + fixture))]))
    checks.append(('nested-storage-struct', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/NestedStorageStructSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/NestedStorageStructSequenceModel.lean',
        '--transactions', str(max(16, transactions)), '--seed', str(seed),
        '--output', str(output / 'nested-storage-struct')]))
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
        '--transactions', str(max(112, transactions)), '--seed', str(seed),
        '--output', str(output / 'interface-static-call')]))
    checks.append(('interface-static-call-rejections', ['-m',
        'solidity_differential.check_interface_static_call_rejections',
        '--output', str(output / 'interface-static-call-rejections')]))
    checks.append(('interface-word-static-call', ['-m', 'solidity_differential.check_interface_word_static_call',
        '--transactions', str(max(160, transactions)), '--seed', str(seed),
        '--output', str(output / 'interface-word-static-call')]))
    checks.append(('interface-word-static-call-rejections', ['-m',
        'solidity_differential.check_interface_word_static_call_rejections',
        '--output', str(output / 'interface-word-static-call-rejections')]))
    checks.append(('create2-struct-emit', ['-m', 'solidity_differential.check_create2_struct_emit',
        '--transactions', str(max(32, min(transactions, 48))), '--seed', str(seed),
        '--output', str(output / 'create2-struct-emit')]))
    checks.append(('create2-struct-emit-rejections', ['-m',
        'solidity_differential.check_create2_struct_emit_rejections',
        '--output', str(output / 'create2-struct-emit-rejections')]))
    checks.append(('external-code-low-level-call', ['-m',
        'solidity_differential.check_external_code_and_low_level_call',
        '--transactions', str(max(64, min(transactions, 96))), '--seed', str(seed),
        '--output', str(output / 'external-code-low-level-call')]))
    checks.append(('external-code-low-level-call-rejections', ['-m',
        'solidity_differential.check_external_code_and_low_level_call_rejections',
        '--output', str(output / 'external-code-low-level-call-rejections')]))
    checks.append(('extcodecopy-struct-decode', ['-m', 'solidity_differential.check_extcodecopy_struct_decode',
        '--transactions', str(max(96, min(transactions, 128))), '--seed', str(seed),
        '--output', str(output / 'extcodecopy-struct-decode')]))
    checks.append(('extcodecopy-struct-decode-rejections', ['-m',
        'solidity_differential.check_extcodecopy_struct_decode_rejections',
        '--output', str(output / 'extcodecopy-struct-decode-rejections')]))
    checks.append(('extcodehash', ['-m', 'solidity_differential.check_extcodehash',
        '--transactions', str(max(160, min(transactions, 192))), '--seed', str(seed),
        '--output', str(output / 'extcodehash')]))
    checks.append(('extcodehash-rejections', ['-m', 'solidity_differential.check_extcodehash_rejections',
        '--output', str(output / 'extcodehash-rejections')]))
    checks.append(('selector-responder', ['-m', 'solidity_differential.check_selector_responder',
        '--transactions', str(max(64, min(transactions, 96))), '--seed', str(seed),
        '--output', str(output / 'selector-responder')]))
    checks.append(('reentrant-callback', ['-m', 'solidity_differential.check_reentrant_callback',
        '--transactions', str(max(64, min(transactions, 96))), '--seed', str(seed),
        '--output', str(output / 'reentrant-callback')]))
    checks.append(('post-call-state-access', ['-m',
        'solidity_differential.check_post_call_state_access',
        '--transactions', str(max(64, min(transactions, 96))), '--seed', str(seed),
        '--output', str(output / 'post-call-state-access')]))
    checks.append(('reentrant-callback-rejections', ['-m',
        'solidity_differential.check_reentrant_callback_rejections',
        '--output', str(output / 'reentrant-callback-rejections')]))
    checks.append(('encoding-arg-super-override', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/EncodingArgSuperOverrideSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/EncodingArgSuperOverrideSequenceModel.lean',
        '--transactions', str(max(16, transactions)), '--seed', str(seed),
        '--change-prefix', '0', '1', '2', '3', str(2**256 - 1),
        '--output', str(output / 'encoding-arg-super-override')]))
    checks.append(('abi-encode-udvt', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AbiEncodeUdvtSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AbiEncodeUdvtSequenceModel.lean',
        '--transactions', str(max(16, transactions)), '--seed', str(seed),
        '--change-prefix', '0', '1', '2', '3', '8', '9', '10', '11', str(2**256 - 1),
        '--output', str(output / 'abi-encode-udvt')]))
    checks.append(('abi-encode-stateful', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AbiEncodeStatefulSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AbiEncodeStatefulSequenceModel.lean',
        '--transactions', str(max(16, transactions)), '--seed', str(seed),
        '--change-prefix', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10', '11', str(2**256 - 1),
        '--output', str(output / 'abi-encode-stateful')]))
    checks.append(('abi-encode-string-helper', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AbiEncodeStringHelperSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AbiEncodeStringHelperSequenceModel.lean',
        '--transactions', str(max(64, transactions)), '--seed', str(seed),
        '--change-prefix', '306', '61', '74', '62', '64', '77', '63', '180', '61', '74', '62', '64',
        '77', '63', '42', '61', '74', '62', '64', '77', '63', '228', '61', '74', '62', '64', '77', '63',
        '402', '14337', '69', '14355', '61', '65', '108', '14355', '14337', '65', '384', '61', '63',
        str(2**256 - 1),
        '--output', str(output / 'abi-encode-string-helper')]))
    from .check_storage import ABI_DECODE_ENUM_STRUCT_PREFIX, ENUM_FLAT_STRUCT_PREFIX
    checks.append(('abi-decode-enum-struct', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AbiDecodeEnumStructSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AbiDecodeEnumStructSequenceModel.lean',
        '--transactions', str(max(48, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, ABI_DECODE_ENUM_STRUCT_PREFIX),
        '--output', str(output / 'abi-decode-enum-struct')]))
    checks.append(('enum-flat-struct', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/EnumFlatStructSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/EnumFlatStructSequenceModel.lean',
        '--transactions', str(max(64, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, ENUM_FLAT_STRUCT_PREFIX),
        '--output', str(output / 'enum-flat-struct')]))
    checks.append(('assignment-arguments', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AssignmentArgumentSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AssignmentArgumentSequenceModel.lean',
        '--transactions', str(max(32, transactions)), '--seed', str(seed),
        '--change-prefix', '2', '0', '3', '0', '1', '7', '4', '1', '25', '10', '5', '11', '8', '9',
        '6', '12', '13', '2', '14', str(2**256 - 1),
        '--output', str(output / 'assignment-arguments')]))
    checks.append(('named-arguments', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/NamedArgumentsSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/NamedArgumentsSequenceModel.lean',
        '--transactions', str(max(16, transactions)), '--seed', str(seed),
        '--change-prefix', '0', '1', '2', '7', '12', str(2**128 - 1), str(2**128),
        '--output', str(output / 'named-arguments')]))
    # Assignment order (MappingWriteOrderSequence): x = 16 * y + c selects assignment c. The
    # prefix makes key and right-hand side revert together (y = 0), runs the key and
    # right-hand-side helper and `i++` index cases (y = 1, 2), in-range writes and an
    # out-of-range index.
    checks.append(('mapping-write-order', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/MappingWriteOrderSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/MappingWriteOrderSequenceModel.lean',
        '--transactions', str(max(32, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [0, 2, 5, 8, 10, 11, 13, 14, 15, 17, 19, 20, 22, 23, 25, 28, 29, 30, 31, 47, 49, 50, 60, 75, 62, 144, 2 ** 256 - 1]),
        '--output', str(output / 'mapping-write-order')]))
    # Modifiers whose `_;` sits in a branch or appears more than once (#2846), lowered by
    # substitution: ModifierPlaceholderSequence is via-IR (0.8.34), its twin
    # ModifierPlaceholderLegacySequence is legacy (0.8.10). The prefix makes the first copy of
    # the body skip `gate` (0), the second copy skip it (14, 8 after 8), both copies run it (2, 6),
    # takes every `split` branch (even; odd with x % 5 == 1; the skipping `else`), runs `again`'s
    # branch `_;` too (11, 31), reverts in the body (20) and overflows `gate`'s argument (2**256 - 1).
    for name, fixture, extra in (('modifier-placeholder', 'ModifierPlaceholderSequence', []),
                                 ('modifier-placeholder-legacy', 'ModifierPlaceholderLegacySequence',
                                  ['--solc-version', '0.8.10'])):
        checks.append((name, ['-m', 'solidity_differential.check_stateful',
            '--source-fixture', f'Contracts/SolidityImportSmoke/{fixture}.sol',
            '--model-driver', f'Contracts/SolidityImportSmoke/{fixture}Model.lean',
            '--transactions', str(max(32, transactions)), '--seed', str(seed), *extra,
            '--change-prefix', *map(str, [0, 2, 5, 3, 3, 9, 20, 14, 1, 8, 8, 4, 6, 11, 31, 2 ** 256 - 1]),
            '--output', str(output / name)]))
    # Modifiers on roots and helpers in forwarded `(bool, bytes memory)` tuple call trees (#2803),
    # across solc 0.8.34 via-IR and legacy (`--no-via-ir`).
    for name, driver, extra in (('forwarded-tuple-modifiers',
                                 'ForwardedTupleModifiersSequenceModel', []),
                                ('forwarded-tuple-modifiers-legacy',
                                 'ForwardedTupleModifiersLegacySequenceModel', ['--no-via-ir'])):
        checks.append((name, ['-m', 'solidity_differential.check_stateful',
            '--source-fixture', 'Contracts/SolidityImportSmoke/ForwardedTupleModifiersSequence.sol',
            '--model-driver', f'Contracts/SolidityImportSmoke/{driver}.lean',
            '--transactions', str(max(44, transactions)), '--seed', str(seed), *extra,
            '--change-prefix', *map(str, [0, 1, 0x12342, 0x56783, 0x9abc4, 11, 12, 13, 14, 15]),
            '--output', str(output / name)]))
    # `assert` and discarded expression statements (AssertStatementSequence): x = 8 * y + c
    # selects case c. The prefix runs each assert holding and failing (Panic(0x01)), the
    # state-changing condition until it fails, a panicking condition, every discarded-value
    # panic (0x11, 0x12, 0x21, 0x32) and its passing twin, and the helper assert.
    checks.append(('assert-statement', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/AssertStatementSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/AssertStatementSequenceModel.lean',
        '--transactions', str(max(32, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [0, 8, 1, 9, 17, 2, 26, 10, 3, 11, 4, 12, 5, 21, 6, 30, 7, 111, 1, 2 ** 256 - 1]),
        '--output', str(output / 'assert-statement')]))
    # Storage-pointer library helper on a mapping of structs (StoragePointerMappingHelperSequence):
    # x = 32 * v + 8 * k + c runs case c on key k with value v. The prefix lists keys 1-3, runs
    # every case on a listed key and on the never-listed key 0 (the custom-error reverts), with
    # packed values that fill the narrow members, deletes key 1, misses it, then relists it.
    checks.append(('storage-pointer-mapping-helper', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/StoragePointerMappingHelperSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/StoragePointerMappingHelperSequenceModel.lean',
        '--transactions', str(max(40, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [8, 16, 24, 1, 23612620949129, 10, 2, 171, 19, 251, 3, 12, 20, 4,
                                       14, 6, 16367, 1375, 7, 35184372088817, 18, 13, 105, 10, 12, 14,
                                       303, 8, 2473, 12, 2 ** 256 - 1]),
        '--output', str(output / 'storage-pointer-mapping-helper')]))
    # Struct copy and `string` write order (StructCopyWriteOrderSequence): x = 8 * y + c selects
    # case c. The prefix runs every case with y = 0 (key and source both revert), 1, 2 and 3.
    checks.append(('struct-copy-write-order', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/StructCopyWriteOrderSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/StructCopyWriteOrderSequenceModel.lean',
        '--transactions', str(max(40, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 2 ** 256 - 1]),
        '--output', str(output / 'struct-copy-write-order')]))
    # Encoding arguments (EncodingArgumentOrderSequence): x = 8 * y + c selects case c; y = 0
    # makes two arguments revert, an even y corrupts the storage `bytes` / `string` argument.
    # The prefix runs every case at y = 0, 1 and (for the corrupt cases) 2; case 6 also at
    # y = 5 and 6 (its event form without the overflow).
    checks.append(('encoding-argument-order', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/EncodingArgumentOrderSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/EncodingArgumentOrderSequenceModel.lean',
        '--transactions', str(max(32, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [0, 8, 24, 1, 9, 2, 10, 18, 3, 11, 4, 12, 20, 5, 13, 21, 6, 14,
            22, 46, 54, 7, 15, 2 ** 256 - 1]),
        '--output', str(output / 'encoding-argument-order')]))
    # String/bytes results among several helper results (MultiReturnBufferSequence):
    # x = 8 * n + c selects case c with length n. The prefix runs (bool, bytes) of length
    # 0, 31, 32, 33, 40 and the reverting 41, both (string, string) helpers (short and
    # 57-byte names), the twice-returned buffer, the returned parameter written after the
    # call, the storage snapshot, the tuple assignment and the forwarded helper.
    checks.append(('multi-return-buffers', ['-m', 'solidity_differential.check_stateful',
        '--source-fixture', 'Contracts/SolidityImportSmoke/MultiReturnBufferSequence.sol',
        '--model-driver', 'Contracts/SolidityImportSmoke/MultiReturnBufferSequenceModel.lean',
        '--transactions', str(max(32, transactions)), '--seed', str(seed),
        '--change-prefix', *map(str, [0, 248, 256, 264, 320, 328, 1, 2, 10, 3, 251, 331, 4, 260,
            332, 5, 6, 5, 7, 263, 335, 2 ** 256 - 1]),
        '--output', str(output / 'multi-return-buffers')]))
    # Narrow `T[] calldata` arrays copied to memory (returned as `T[] memory`, passed to a memory
    # helper) with clean and out-of-range elements (check_stateful's NARROW_COPY_CALLS prefix).
    # The 0.8.34 fixture runs via-IR (the copy reverts); its solc 0.8.10 twin runs the legacy
    # pipeline (the copy cleans each element).
    for check, fixture, extra in (
            ('calldata-narrow-array-copy', 'CalldataNarrowArrayCopySequence', []),
            ('calldata-narrow-array-copy-solc0810', 'CalldataNarrowArrayCopySolc0810Sequence',
             ['--solc-version', '0.8.10'])):
        checks.append((check, ['-m', 'solidity_differential.check_stateful',
            '--source-fixture', f'Contracts/SolidityImportSmoke/{fixture}.sol',
            '--model-driver', f'Contracts/SolidityImportSmoke/{fixture}Model.lean',
            '--transactions', str(max(32, transactions)), '--seed', str(seed), *extra,
            '--change-prefix', '0', '1', '999', str(2 ** 256 - 1),
            '--output', str(output / check)]))
    # A stateful helper call beside a local / parameter `+` operand, as a helper's lone argument
    # and as a using-for receiver, with one state variable (StatefulCallOperand*Sequence):
    # x % 5 selects the case, x / 5 drives it. The prefix runs every case at x / 5 = 0, 1, 2 and
    # with the largest inputs (checked overflow in or after the call). The 0.8.34 fixture runs
    # via-IR (left operand first); its solc 0.8.10 twin runs the legacy pipeline (right first).
    # StatefulCallConstantOperand*Sequence: the same beside a contract or file-level `constant`
    # or an `immutable` operand (x % 3 selects it, x / 3 drives it).
    for check, fixture, extra in (
            ('stateful-call-operand', 'StatefulCallOperandSequence', []),
            ('stateful-call-operand-solc0810', 'StatefulCallOperandSolc0810Sequence',
             ['--solc-version', '0.8.10']),
            ('stateful-call-constant-operand', 'StatefulCallConstantOperandSequence', []),
            ('stateful-call-constant-operand-solc0810', 'StatefulCallConstantOperandSolc0810Sequence',
             ['--solc-version', '0.8.10'])):
        checks.append((check, ['-m', 'solidity_differential.check_stateful',
            '--source-fixture', f'Contracts/SolidityImportSmoke/{fixture}.sol',
            '--model-driver', f'Contracts/SolidityImportSmoke/{fixture}Model.lean',
            '--transactions', str(max(32, transactions)), '--seed', str(seed), *extra,
            '--change-prefix', *map(str, [*range(15), *(2 ** 256 - k for k in range(1, 6))]),
            '--output', str(output / check)]))
    checks.append(('immutable-lowering', ['-m', 'solidity_differential.check_immutable_lowering',
        '--output', str(output / 'immutable-lowering')]))
    checks.append(('yul-memory-call', ['-m', 'solidity_differential.check_yul_memory_call',
        '--transactions', str(max(64, min(transactions, 96))), '--seed', str(seed),
        '--output', str(output / 'yul-memory-call')]))
    checks.append(('ecrecover', ['-m', 'solidity_differential.check_ecrecover',
        '--transactions', str(max(200, min(transactions, 240))), '--seed', str(seed),
        '--output', str(output / 'ecrecover')]))
    checks.append(('ecrecover-rejections', ['-m', 'solidity_differential.check_ecrecover_rejections',
        '--output', str(output / 'ecrecover-rejections')]))
    checks.append(('linked-library-call', ['-m', 'solidity_differential.check_linked_library_call',
        '--transactions', str(max(200, min(transactions, 240))), '--seed', str(seed),
        '--output', str(output / 'linked-library-call')]))
    checks.append(('linked-library-call-negative', ['-m',
        'solidity_differential.check_linked_library_call', '--negative-control',
        '--transactions', '60', '--seed', str(seed),
        '--output', str(output / 'linked-library-call-negative')]))
    checks.append(('signature-calldata', ['-m', 'solidity_differential.check_signature_calldata',
        '--transactions', str(max(200, min(transactions, 240))), '--seed', str(seed),
        '--output', str(output / 'signature-calldata')]))
    checks.append(('signature-calldata-rejections', ['-m',
        'solidity_differential.check_signature_calldata_rejections',
        '--output', str(output / 'signature-calldata-rejections')]))
    checks.append(('interface-void-call', ['-m', 'solidity_differential.check_interface_void_call',
        '--transactions', str(max(160, min(transactions, 192))), '--seed', str(seed),
        '--output', str(output / 'interface-void-call')]))
    checks.append(('yul-memory-call-rejections', ['-m',
        'solidity_differential.check_yul_memory_call_rejections',
        '--output', str(output / 'yul-memory-call-rejections')]))
    checks.append(('yul-narrow-result', ['-m', 'solidity_differential.check_yul_narrow_result',
        '--transactions', str(max(120, min(transactions, 160))), '--seed', str(seed),
        '--output', str(output / 'yul-narrow-result')]))
    checks.append(('state-count-invariance', ['-m', 'solidity_differential.check_state_count_invariance',
        '--output', str(output / 'state-count-invariance')]))
    # Schedule the longest multi-variant campaigns first (LPT order) so ~30-45 min
    # checks start at t=0 on a 6-wide pool instead of straggling past the step cap.
    heavy_first = (
        'extcodecopy-struct-decode',
        'create2-struct-emit',
        'hashing-programs',
        'nested-dynamic-struct-abi',
        'multiple-dynamic-abi',
        'scalar-array-abi',
        'event-mutations',
        'mutations',
        'pinned-sequence',
        'pinned-sequence-corpus',
        'struct-abi',
        'abi',
        'interface-static-call',
        'abi-event-composition',
        'reference-arguments',
        'external-code-low-level-call',
        'interface-word-static-call',
    )
    priority = {name: rank for rank, name in enumerate(heavy_first)}
    checks.sort(key=lambda item: priority.get(item[0], len(heavy_first)))
    return run_checks(output, checks, transactions, seed, jobs)


def run_checks(output, checks, transactions, seed, jobs=1):
    """Run named checks, printing each one before it starts.

    ``command`` captures subprocess output until the process exits, so a
    multi-check campaign otherwise looks idle for its whole wall time.
    Checks write separate output directories and only read the shared Lake
    build (prepared up front by ``stateful_campaign``), so up to ``jobs`` of
    them run at once. Completion is still recorded in check order. A failing
    check does not cancel the others: every check runs, and all failures are
    raised together, so one CI run reports every stale control at once.
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
        # Per-check guard against hangs. Checks run `jobs` wide on one runner, so
        # the slowest (extcodecopy-struct-decode, ~45 min under load) needs headroom.
        try:
            command(argv, timeout=3600, log=output / f'{name}.log')
        except BaseException:
            print(f'stateful check {index}/{total}: {name} FAILED', flush=True)
            raise
        print(f'stateful check {index}/{total}: {name} done', flush=True)

    failures = []
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        futures = [pool.submit(run, index, name, args)
                   for index, (name, args) in enumerate(checks, start=1)]
        for (name, _), future in zip(checks, futures):
            try:
                future.result()
            except Exception as error:  # noqa: BLE001 - reported below, by name
                failures.append((name, error))
                continue
            completed.append(name)
            write_json(output / 'completed.json', completed)
    if failures:
        if len(failures) == 1:
            raise failures[0][1]
        details = '\n'.join(f'- {name}: {error}' for name, error in failures)
        raise HarnessError(f'{len(failures)} stateful checks failed:\n{details}')
    return {'checks': completed, 'transactionsPerVariant': transactions, 'seed': seed,
            'divergences': []}
