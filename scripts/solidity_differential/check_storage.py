"""Run actual imported packed storage variants through all three stateful routes."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

from .engine import command, write_json
from .programs import call_arg_source
from .programs import (
    ROOT_PARAM_RENAMES,
    stateful_abi_decode_and_verifier_source,
    stateful_access_manager_target_role_source,
    stateful_array_string_params_and_context_source,
    stateful_array_write_order_source,
    stateful_byte_constant_conversions_source,
    stateful_bytes_and_string_storage_source,
    stateful_bytes_memory_and_abi_encode_call_source,
    stateful_bytes_named_return_slice_struct_source,
    stateful_bytes_named_return_stateless_source,
    stateful_checkpoints_and_struct_arrays_source,
    stateful_constant_array_source,
    stateful_create2_clones_msgdata_deque_source,
    stateful_custom_error_fixed_bytes_source,
    stateful_default_local_source,
    stateful_discarded_helper_source,
    stateful_dynamic_array_root_return_source,
    stateful_dynamic_bytes_and_string_return_source,
    stateful_dynamic_memory_array_source,
    stateful_dynamic_revert_string_source,
    stateful_ecdsa_merkle_checkpoints_storage_slot_source,
    stateful_ecrecover_authorizer_arrays_map_source,
    stateful_empty_array_bytes_calldata_source,
    stateful_empty_revert_source,
    stateful_encoded_byte_local_source,
    stateful_enumerable_set_map_storage_arrays_source,
    stateful_erc2981_holders_arrays_msghash_source,
    stateful_event_nested_mapping_read_source,
    stateful_exp_and_bitwise_shift_source,
    stateful_fixed_array_source,
    stateful_fixed_bytes_conversions_source,
    stateful_fixed_memory_array_source,
    stateful_fn_ptr_struct_delete_modifier_source,
    stateful_governor_slice_proposer_delay_source,
    stateful_helper_effect_source,
    stateful_helper_loop_source,
    stateful_helper_name_independence_source,
    stateful_if_else_source,
    stateful_imported_event_source,
    stateful_inheritance_source,
    stateful_inline_array_literal_source,
    stateful_int256_contract_type_source,
    stateful_invariant_for_source,
    stateful_local_write_source,
    stateful_mapping_source,
    stateful_merkle_and_nonces_source,
    stateful_modifier_unchecked_compound_source,
    stateful_modulo_source,
    stateful_msg_data_and_enum_source,
    stateful_msg_sig_source,
    stateful_multiproof_mapping_keys_verifiers_source,
    stateful_named_helper_return_source,
    stateful_named_string_return_source,
    stateful_narrow_for_counters_source,
    stateful_numeric_literal_source,
    stateful_overload_const_error_cond_tuple_tload_source,
    stateful_packed_member_write_source,
    stateful_packed_signed_int_source,
    stateful_packed_struct_mapping_ternary_tuple_source,
    stateful_public_getters_and_builtins_source,
    stateful_root_param_source,
    stateful_short_circuit_source,
    stateful_signed_compound_assignment_source,
    stateful_signed_modulo_source,
    stateful_signed_struct_compound_source,
    stateful_signed_struct_member_read_source,
    stateful_storage_string_member_source,
    stateful_solc_0810_source,
    stateful_storage_source,
    stateful_storage_word_source,
    stateful_string_bytes_mappings_uri_storage_strings_source,
    stateful_string_event_param_source,
    stateful_strings_hex_arrays_bitmaps_source,
    stateful_struct_fixed_array_and_fixed_return_source,
    stateful_struct_hash_and_domain_separator_source,
    stateful_struct_mapping_and_bytes4_interface_source,
    stateful_struct_params_and_balances_source,
    stateful_timelock_and_bytes4_cast_source,
    stateful_tuple_destructuring_source,
    stateful_tuple_helper_source,
    stateful_udvt_param_assign_struct_hash_source,
    stateful_unchecked_blocks_source,
    stateful_void_helper_guard_source,
    stateful_votes_checkpoints_arrays_bitmaps_source,
    stateful_wad_exp_and_three_key_mapping_source,
    stateful_while_clz_and_struct_loc_source,
    stateful_yul_block_mulmod_tstore_source,
    stateful_yul_builtins_and_encode_selector_source,
    stateful_yul_empty_revert_source,
    stateful_yul_revert_memory_source,
    stateful_yul_numeric_source,
)



from .stateful import validate_observation


# 25 hits the out-of-range small[small.length] += 1 (x % 13 == 12, Panic(0x32));
# 65334 overflows the uint8 small[1] += x % 64 (Panic(0x11)).
DYNAMIC_MEMORY_ARRAY_PREFIX = [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 13, 21, 25, 65334, 0x01020304050607,
                               (0xffff << 16) | 4, (1 << 256) - 1]
INLINE_ARRAY_LITERAL_PREFIX = [0, 1, 2, 3, 4, 7, 8, 16, 17, 0xffff, 0x10000,
                               (0xabcd << 240) | 5, (1 << 256) - 1]
FIXED_MEMORY_ARRAY_PREFIX = [0, 1, 2, 3, 6, 7, 11, 13, 34, 41, 0x5a00000003,
                             (3 << 40) | 0x01020304, (1 << 256) - 1]
# check_stateful first runs change(7) (cell 0, most negative inputs), fail() and read(). Then
# k = x % length: 0 pushes cell 1 and rewrites cell 0; the second value pushes cell 2 and writes
# the largest positive inputs into it (x % 3 == 2); the third writes -5 / -5 / 5 - 2^31 into
# cell 1 (x % 3 == 1), so the state-variable struct also holds negative values. Both have an
# unsigned tag >= 128. Bit 64 skips the writes, so the next calls only read cells 0, 1, 2.
# int24 accumulator at both ends of its range (checked overflow panics), int8 `+= 1` at 127 and
# `--` at -128, `acc++` at the maximum, high words; the unchecked wraps of `w += d` (0x80000000),
# `w++` (0x808000f2) and `w -= ..` (the 1 << 248 value), each in a call that does not revert; and
# dirty high bits in the Yul-assigned int24 local (`shr(64, x)` is dirty for the 255 << 248 value,
# the 1 << 248 value and the last value; also for 2^256 - 1, which reverts earlier at `a += d`).
SIGNED_COMPOUND_PREFIX = [0x800000, 0, 0xffffff, (1 << 40) | 0xffffff, (1 << 40) | 0x800000,
                          (255 << 24) | 0x800000, (1 << 32) | 0x800000, (255 << 248) | 0x800000,
                          (1 << 256) - 1, 0x80000000, 0x800000fa, 0x808000f2,
                          (1 << 248) | 0x80800000, (0x123 << 88) | (5 << 64) | (128 << 24) | 0x800000]
# After change(7), fail(), read(): bit 16 stores t = -5, s = -5, u = -300 (negative members, a
# narrower signed right-hand side); bit 17 puts t near type(int24).max, so `+= d` overflows for
# d > 100 (Panic(0x11)); bit 18 wraps u in an unchecked block; k = x % length visits every cell.
SIGNED_STRUCT_COMPOUND_PREFIX = [(1 << 16) | (128 << 8) | 1, (1 << 16) | (128 << 8) | 2,
                                 (1 << 16) | (127 << 24) | (130 << 8) | 3,
                                 (1 << 16) | (1 << 18) | (128 << 8) | 4, (1 << 17) | (127 << 8) | 5,
                                 (1 << 17) | (255 << 8) | 6, (1 << 16) | (1 << 17) | (128 << 8) | 7,
                                 (255 << 8) | 8, (1 << 16) | 9, (1 << 256) - 1]
SIGNED_STRUCT_MEMBER_READ_PREFIX = [0, 128 | (0xffff << 8) | (0xff << 24) | (0xffffffff << 32),
                                    128 | (32763 << 8) | (123 << 24) | (5 << 32),
                                    (1 << 64) | 2, 1 << 64, (1 << 64) | 1, (1 << 256) - 1]
# int8 / int24 / int128 at their minimum (0) and maximum (2^256 - 1), at -1 / -5 / -2 with a
# nonzero address, just above zero (1 / 1 / 1), and a single high bit (int128 at its minimum).
PACKED_SIGNED_INT_PREFIX = [0, (1 << 256) - 1,
                            127 | (8388603 << 8) | ((2 ** 127 - 2) << 32) | (0xdead << 160),
                            129 | (8388609 << 8) | ((2 ** 127 + 1) << 32), 1 << 255]

STORAGE_STRING_MEMBER_PREFIX = [0, 1, 2, 255, 256, 257, (0xab << 200) | (0x1234 << 136) | (0xff << 8) | 3,
                                (1 << 255) | (1 << 136) | 4, (1 << 256) - 1, (1 << 256) - 2]


def canonical_observations(observations):
    """Slot order is not observable; retain every key/value and ordered event."""
    result = {}
    for route, rows in observations.items():
        result[route] = []
        for row in rows:
            touched, storage = validate_observation(row)
            result[route].append({**row,
                'touched': [list(key) for key in sorted(touched)],
                'storage': [[*key, storage[key]] for key in sorted(storage)]})
    return result


# One call per Yul revert shape (x % 8 in 0..5) with small arguments, the argument shapes with
# high-bit payload words (selector + argument, two words with `add(x, 1)` near 2^256,
# `mul(x, 3)` wrapping), and calls that store (x % 8 in 6, 7).
YUL_REVERT_MEMORY_PREFIX = [16, 17, 18, 19, 20, 21, 22, 23, 2 ** 255 + 2, 2 ** 255 + 3,
                            2 ** 256 - 5, 2 ** 255 + 4, 2 ** 255 + 5, 2 ** 256 - 1, 2 ** 255 + 6]

# Fixture name -> Contracts/SolidityImportSmoke/<contract>.sol. One entry per line,
# sorted, so PRs adding different fixtures do not touch the same line.
FIXTURE_CONTRACTS = {
    'abi-decode-and-verifier': 'AbiDecodeAndVerifierSequence',
    'access-manager-target-role': 'AccessManagerTargetRoleSequence',
    'array-string-params-and-context': 'ArrayStringParamsAndContextSequence',
    'array-write-order': 'FixedArrayWriteOrderSequence',
    'byte-constant-conversions': 'ByteConstantConversionSequence',
    'bytes': 'StorageBytesSequence',
    'bytes-and-string-storage': 'BytesAndStringStorageSequence',
    'bytes-array-param': 'BytesArrayParamSequence',
    'bytes-memory-and-abi-encode-call': 'BytesMemoryAndAbiEncodeCallSequence',
    'bytes-named-return-slice-struct': 'BytesNamedReturnSliceStructSequence',
    'bytes-named-return-stateless': 'BytesNamedReturnStatelessSequence',
    'checkpoints-and-struct-arrays': 'CheckpointsAndStructArraysSequence',
    'constant-arrays': 'ConstantArraySequence',
    'create2-clones-msgdata-deque': 'Create2ClonesMsgDataDequeSequence',
    'custom-error-fixed-bytes': 'CustomErrorFixedBytesSequence',
    'default-locals': 'DefaultLocalSequence',
    'discarded-helper': 'DiscardedHelperSequence',
    'dynamic-array-root-returns': 'DynamicArrayRootReturnSequence',
    'dynamic-array-root-returns-stateless': 'DynamicArrayRootReturnStatelessSequence',
    'dynamic-bytes-and-string-return': 'DynamicBytesAndStringReturnSequence',
    'dynamic-memory-arrays': 'DynamicMemoryArraySequence',
    'dynamic-revert-string': 'DynamicRevertStringSequence',
    'ecdsa-merkle-checkpoints-storage-slot': 'EcdsaMerkleCheckpointsStorageSlotSequence',
    'ecrecover-authorizer-arrays-map': 'EcrecoverAuthorizerArraysMapSequence',
    'empty-array-bytes-calldata': 'EmptyArrayReturnBytesCalldataSequence',
    'empty-revert': 'EmptyRevertSequence',
    'encoded-byte-locals': 'EncodedByteLocalSequence',
    'enumerable-set-map-storage-arrays': 'EnumerableSetMapSequence',
    'erc2981-holders-arrays-msghash': 'ERC2981HoldersArraysMsgHashSequence',
    'event-nested-mapping-read': 'EventNestedMappingReadSequence',
    'exp-and-bitwise-shifts': 'ExpAndBitwiseShiftSequence',
    'fixed-arrays': 'MappingFixedArraySequence',
    'fixed-bytes-conversions': 'FixedBytesConversionSequence',
    'fixed-memory-arrays': 'FixedMemoryArraySequence',
    'fn-ptr-struct-delete-modifier': 'FnPtrStructDeleteModifierSequence',
    'governor-slice-proposer-delay': 'GovernorSliceProposerDelaySequence',
    'helper-effects': 'HelperEffectSequence',
    'helper-loops': 'HelperLoopSequence',
    'helper-name-independence': 'HelperNameIndependenceSequence',
    'if-else': 'IfElseSequence',
    'imported-event': 'ImportedEventSequence',
    'inheritance': 'InheritanceSequence',
    'inline-array-literals': 'InlineArrayLiteralSequence',
    'int256-contract-types': 'Int256ContractTypeSequence',
    'invariant-for': 'InvariantForSequence',
    'local-writes': 'LocalWriteSequence',
    'mapping': 'MappingSequence',
    'merkle-and-nonces': 'MerkleAndNoncesSequence',
    'modifier-unchecked-compound': 'ModifierUncheckedCompoundSequence',
    'modulo': 'ModuloSequence',
    'msg-data-and-enum': 'MsgDataAndEnumSequence',
    'msg-sig': 'MsgSigSequence',
    'multiproof-mapping-keys-verifiers': 'MultiProofMappingKeysVerifiersSequence',
    'named-helper-returns': 'NamedHelperReturnSequence',
    'named-string-return': 'NamedStringReturnSequence',
    'narrow-event': 'NarrowEventSequence',
    'narrow-for-counters': 'NarrowForCounterSequence',
    'call-arg-side-effects': 'CallArgSideEffectSequence',
    'numeric-literals': 'NumericLiteralSequence',
    'overload-const-error-cond-tuple-tload': 'OverloadConstErrorCondTupleTloadSequence',
    'packed': 'StorageSequence',
    'packed-member-writes': 'PackedMemberWriteSequence',
    'packed-signed-int': 'PackedSignedIntSequence',
    'packed-struct-mapping-ternary-tuple': 'PackedStructMappingAndTernaryTupleSequence',
    'public-getters-and-builtins': 'PublicGettersAndBuiltinsSequence',
    'short-circuit': 'ShortCircuitSequence',
    'signed-compound-assignment': 'SignedCompoundAssignmentSequence',
    'signed-modulo': 'SignedModuloSequence',
    'signed-struct-compound': 'SignedStructCompoundSequence',
    'signed-struct-member-read': 'SignedStructMemberReadSequence',
    'solc-0810': 'Solc0810Sequence',
    'storage-string-members': 'StorageStringMemberSequence',
    'string-bytes-mappings-uri-storage-strings': 'StringBytesMappingsUriStorageStringsSequence',
    'string-event-param': 'StringEventParamSequence',
    'strings-hex-arrays-bitmaps': 'StringsHexArraysBitmapsSequence',
    'struct-array-param': 'StructArrayParamSequence',
    'struct-fixed-array-and-fixed-return': 'StructFixedArrayAndFixedReturnSequence',
    'struct-hash-and-domain-separator': 'StructHashAndDomainSeparatorSequence',
    'struct-mapping-and-bytes4-interface': 'StructMappingAndBytes4InterfaceSequence',
    'struct-params-and-balances': 'StructParamsAndBalancesSequence',
    'struct-string-member-param': 'StructStringMemberParamSequence',
    'timelock-and-bytes4-cast': 'TimelockAndBytes4CastSequence',
    'tuple-destructuring': 'TupleSequence',
    'tuple-helper': 'TupleHelperSequence',
    'udvt-param-assign-struct-hash': 'UdvtParamAssignStructHashSequence',
    'unchecked-blocks': 'UncheckedSequence',
    'void': 'StorageVoidSequence',
    'void-helper-guards': 'VoidHelperGuardSequence',
    'votes-checkpoints-arrays-bitmaps': 'VotesCheckpointsArraysBitMapsSequence',
    'wad-exp-and-three-key-mapping': 'WadExpAndThreeKeyMappingSequence',
    'while-clz-and-struct-loc': 'WhileClzAndStructLocSequence',
    'yul-block-mulmod-tstore': 'YulBlockMulmodTstoreSequence',
    'yul-builtins-and-encode-selector': 'YulBuiltinsAndEncodeSelectorSequence',
    'yul-empty-revert': 'YulEmptyRevertSequence',
    'yul-revert-memory': 'YulRevertMemorySequence',
    'yul-numeric': 'YulNumericSequence',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', choices=tuple(FIXTURE_CONTRACTS), default='packed')



    parser.add_argument('--narrow-bits', type=int, choices=range(8, 257, 8), default=128)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--seed', type=int, default=2453)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='storage-', dir='.lake')).resolve()
    output.mkdir(parents=True, exist_ok=args.output is None)
    name = FIXTURE_CONTRACTS[args.fixture]



    fixture = Path(f'Contracts/SolidityImportSmoke/{name}.sol').read_text()
    template = Path(f'Contracts/SolidityImportSmoke/{name}Model.lean').read_text()
    if args.fixture == 'narrow-event':
        fixture = fixture.replace('uint128', f'uint{args.narrow_bits}')
        template = template.replace('change(uint128)', f'change(uint{args.narrow_bits})')
    anchor = f'from "Contracts/SolidityImportSmoke" entry "{name}.sol"'
    if template.count(anchor) != 1:
        raise RuntimeError('nonunique imported storage source anchor')
    completed = []
    baseline = None
    variants = ('baseline', 'bindings', 'reordered' if args.fixture in ('packed', 'mapping') else 'expression')
    if args.fixture == 'empty-revert':
        variants = ('baseline', 'renamed', 'expression')
    if args.fixture == 'event-nested-mapping-read':
        variants = ('baseline', 'renamed', 'expanded')
    if args.fixture == 'dynamic-revert-string':
        variants = ('baseline', 'renamed', 'expanded')
    if args.fixture == 'custom-error-fixed-bytes':
        variants = ('baseline', 'renamed', 'expanded')
    if args.fixture == 'string-event-param':
        variants = ('baseline', 'renamed', 'expanded')
    if args.fixture == 'short-circuit':
        variants = ('baseline', 'conditional', 'de-morgan')
    if args.fixture in ('numeric-literals', 'constant-arrays'):
        variants = ('baseline', 'renamed', 'normalized')
    if args.fixture in ('invariant-for', 'helper-loops'):
        variants = ('baseline', 'renamed', 'assignment-step')
    if args.fixture in ('packed-member-writes', 'helper-effects', 'fixed-arrays'):
        variants = ('baseline', 'renamed', 'explicit-delete')
    if args.fixture == 'access-manager-target-role':
        variants = ('baseline', 'renamed', 'expanded-access-manager-target-role')
    if args.fixture == 'governor-slice-proposer-delay':
        variants = ('baseline', 'renamed', 'expanded-governor-slice-proposer-delay')
    if args.fixture == 'unchecked-blocks':
        variants = ('baseline', 'split', 'explicit')
    if args.fixture == 'tuple-destructuring':
        variants = ('baseline', 'expanded', 'inline')
    if args.fixture == 'create2-clones-msgdata-deque':
        variants = ('baseline', 'renamed', 'expanded-create2-clones-msgdata-deque')
    if args.fixture == 'ecdsa-merkle-checkpoints-storage-slot':
        variants = ('baseline', 'renamed', 'expanded-ecdsa-merkle-checkpoints-storage-slot')
    if args.fixture == 'strings-hex-arrays-bitmaps':
        variants = ('baseline', 'renamed', 'expanded-strings-hex-arrays-bitmaps')
    if args.fixture == 'string-bytes-mappings-uri-storage-strings':
        variants = ('baseline', 'renamed', 'expanded-string-bytes-mappings-uri-storage-strings')
    if args.fixture == 'timelock-and-bytes4-cast':
        variants = ('baseline', 'renamed', 'expanded-timelock-and-bytes4-cast')
    if args.fixture == 'packed-struct-mapping-ternary-tuple':
        variants = ('baseline', 'renamed', 'expanded-packed-struct-mapping-ternary-tuple')
    if args.fixture == 'struct-params-and-balances':
        variants = ('baseline', 'renamed', 'expanded-struct-params-and-balances')
    if args.fixture == 'ecrecover-authorizer-arrays-map':
        variants = ('baseline', 'renamed', 'expanded-ecrecover-authorizer-arrays-map')
    if args.fixture == 'public-getters-and-builtins':
        variants = ('baseline', 'renamed', 'expanded-public-getters-and-builtins')
    if args.fixture == 'votes-checkpoints-arrays-bitmaps':
        variants = ('baseline', 'renamed', 'expanded-votes-checkpoints-arrays-bitmaps')
    if args.fixture == 'abi-decode-and-verifier':
        variants = ('baseline', 'renamed', 'expanded-abi-decode-and-verifier')
    if args.fixture == 'struct-hash-and-domain-separator':
        variants = ('baseline', 'renamed', 'expanded-struct-hash-and-domain-separator')
    if args.fixture == 'wad-exp-and-three-key-mapping':
        variants = ('baseline', 'renamed', 'expanded-wad-exp-and-three-key-mapping')
    if args.fixture == 'checkpoints-and-struct-arrays':
        variants = ('baseline', 'renamed', 'expanded-checkpoints-and-struct-arrays')
    if args.fixture == 'enumerable-set-map-storage-arrays':
        variants = ('baseline', 'renamed', 'expanded-enumerable-set-map-storage-arrays')
    if args.fixture == 'erc2981-holders-arrays-msghash':
        variants = ('baseline', 'renamed', 'expanded-erc2981-holders-arrays-msghash')
    if args.fixture == 'struct-mapping-and-bytes4-interface':
        variants = ('baseline', 'renamed', 'expanded-struct-mapping-bytes4')
    if args.fixture == 'udvt-param-assign-struct-hash':
        variants = ('baseline', 'renamed', 'expanded-udvt-param-struct-hash')
    if args.fixture == 'multiproof-mapping-keys-verifiers':
        variants = ('baseline', 'renamed', 'expanded-multiproof-verifiers')
    if args.fixture == 'merkle-and-nonces':
        variants = ('baseline', 'renamed', 'expanded-merkle-and-nonces')
    if args.fixture == 'yul-block-mulmod-tstore':
        variants = ('baseline', 'renamed', 'expanded-yul-mulmod-tstore')
    if args.fixture == 'bytes-and-string-storage':
        variants = ('baseline', 'renamed', 'expanded-bytes-string-storage')
    if args.fixture == 'dynamic-bytes-and-string-return':
        variants = ('baseline', 'renamed', 'expanded-dynamic-return')
    if args.fixture == 'bytes-memory-and-abi-encode-call':
        variants = ('baseline', 'renamed', 'expanded-bytes-memory-encode-call')
    if args.fixture == 'array-string-params-and-context':
        variants = ('baseline', 'renamed', 'expanded-array-string-context')
    if args.fixture == 'yul-builtins-and-encode-selector':
        variants = ('baseline', 'renamed', 'expanded-selector-and-yul')
    if args.fixture == 'while-clz-and-struct-loc':
        variants = ('baseline', 'renamed', 'expanded-while-and-struct-loc')
    if args.fixture == 'exp-and-bitwise-shifts':
        variants = ('baseline', 'renamed', 'expanded-exp-and-bitwise')
    if args.fixture == 'msg-data-and-enum':
        variants = ('baseline', 'renamed', 'expanded-enum-and-msgdata')
    if args.fixture == 'struct-fixed-array-and-fixed-return':
        variants = ('baseline', 'renamed', 'expanded-array-and-return')
    if args.fixture == 'overload-const-error-cond-tuple-tload':
        variants = ('baseline', 'renamed', 'expanded-error-and-accum')
    if args.fixture == 'empty-array-bytes-calldata':
        variants = ('baseline', 'renamed', 'expanded-length-and-accum')
    if args.fixture == 'fn-ptr-struct-delete-modifier':
        variants = ('baseline', 'renamed', 'expanded-delete-and-modifier')
    if args.fixture == 'int256-contract-types':
        variants = ('baseline', 'renamed', 'expanded-signed-and-cast')
    if args.fixture == 'tuple-helper':
        variants = ('baseline', 'renamed', 'explicit-return-and-literal')
    if args.fixture == 'modifier-unchecked-compound':
        variants = ('baseline', 'renamed', 'expanded-compound')
    if args.fixture == 'void-helper-guards':
        variants = ('baseline', 'renamed', 'explicit-else-and-return')
    if args.fixture == 'inheritance':
        variants = ('baseline', 'renamed', 'qualified-super')
    if args.fixture == 'solc-0810':
        variants = ('baseline', 'renamed', 'double-quoted')
    if args.fixture == 'yul-numeric':
        variants = ('baseline', 'renamed', 'normalized')
    if args.fixture == 'named-helper-returns':
        variants = ('baseline', 'renamed', 'explicit-fallthrough')
    if args.fixture == 'encoded-byte-locals':
        variants = ('baseline', 'renamed', 'copy-alias')
    if args.fixture == 'discarded-helper':
        variants = ('baseline', 'renamed', 'explicit-result')
    if args.fixture == 'array-write-order':
        variants = ('baseline', 'renamed', 'captured-rhs')
    if args.fixture == 'local-writes':
        variants = ('baseline', 'renamed', 'explicit-zero')
    if args.fixture == 'default-locals':
        variants = ('baseline', 'renamed', 'explicit')
    if args.fixture == 'msg-sig':
        variants = ('baseline', 'renamed', 'selector-constants')
    if args.fixture == 'modulo':
        variants = ('baseline', 'renamed', 'quotient')
    if args.fixture == 'fixed-memory-arrays':
        variants = ('baseline', 'renamed', 'unrolled')
    if args.fixture == 'narrow-for-counters':
        variants = ('baseline', 'renamed', 'checked-increment')
    if args.fixture == 'inline-array-literals':
        variants = ('baseline', 'renamed', 'element-writes')
    if args.fixture == 'helper-name-independence':
        variants = ('baseline', 'renamed', 'inlined')
    if args.fixture == 'fixed-bytes-conversions':
        variants = ('baseline', 'renamed', 'hex-literals')
    if args.fixture == 'call-arg-side-effects':
        variants = ('baseline', 'renamed', 'explicit')
    if args.fixture == 'dynamic-memory-arrays':
        variants = ('baseline', 'renamed', 'explicit')
    if args.fixture == 'signed-modulo':
        variants = ('baseline', 'renamed', 'truncated-quotient')
    if args.fixture in ('signed-compound-assignment', 'signed-struct-compound'):
        variants = ('baseline', 'renamed', 'explicit')
    if args.fixture == 'byte-constant-conversions':
        variants = ('baseline', 'renamed', 'literal-initializers')
    if args.fixture == 'yul-empty-revert':
        variants = ('baseline', 'renamed', 'offsets')
    if args.fixture == 'yul-revert-memory':
        variants = ('baseline', 'renamed', 'reordered')
    if args.fixture == 'signed-struct-member-read':
        variants = ('baseline', 'renamed', 'local-reads')
    if args.fixture == 'storage-string-members':
        variants = ('baseline', 'renamed', 'direct-members')
    if args.fixture == 'packed-signed-int':
        variants = ('baseline', 'renamed', 'split-buffer')
    if args.fixture in ('bytes-named-return-slice-struct', 'bytes-named-return-stateless', 'named-string-return',
                        'dynamic-array-root-returns', 'dynamic-array-root-returns-stateless'):
        variants = ('baseline', 'renamed', 'unnamed-returns')
    if args.fixture == 'if-else':
        variants = ('baseline', 'inverted', 'ternary')
    if args.fixture in ROOT_PARAM_RENAMES:
        variants = ('baseline', 'renamed', 'members-renamed')
    if args.fixture in ('imported-event', 'narrow-event'):
        variants = ('baseline', 'renamed', 'reordered' if args.fixture == 'narrow-event' else 'bindings')
    for variant in variants:
        directory = output / variant
        directory.mkdir()
        if args.fixture == 'solc-0810':
            (directory / 'Solc0810Imported.sol').write_text(
                Path('Contracts/SolidityImportSmoke/Solc0810Imported.sol').read_text())
        if args.fixture == 'inheritance':
            (directory / 'InheritanceBase.sol').write_text(
                Path('Contracts/SolidityImportSmoke/InheritanceBase.sol').read_text())
        source = directory / 'Sequence.sol'
        source.write_text(stateful_imported_event_source(fixture, variant, args.fixture == "narrow-event") if args.fixture in ("imported-event", "narrow-event")
                          else stateful_empty_revert_source(fixture, variant) if args.fixture == "empty-revert"
                          else stateful_event_nested_mapping_read_source(fixture, variant) if args.fixture == "event-nested-mapping-read"
                          else stateful_dynamic_revert_string_source(fixture, variant) if args.fixture == "dynamic-revert-string"
                          else stateful_custom_error_fixed_bytes_source(fixture, variant) if args.fixture == "custom-error-fixed-bytes"
                          else stateful_string_event_param_source(fixture, variant) if args.fixture == "string-event-param"
                          else stateful_access_manager_target_role_source(fixture, variant) if args.fixture == "access-manager-target-role"
                          else stateful_governor_slice_proposer_delay_source(fixture, variant) if args.fixture == "governor-slice-proposer-delay"
                          else stateful_unchecked_blocks_source(fixture, variant) if args.fixture == "unchecked-blocks"
                          else stateful_msg_sig_source(fixture, variant) if args.fixture == "msg-sig"
                          else stateful_tuple_destructuring_source(fixture, variant) if args.fixture == "tuple-destructuring"
                          else stateful_create2_clones_msgdata_deque_source(fixture, variant) if args.fixture == "create2-clones-msgdata-deque"
                          else stateful_narrow_for_counters_source(fixture, variant) if args.fixture == "narrow-for-counters"
                          else stateful_ecdsa_merkle_checkpoints_storage_slot_source(fixture, variant) if args.fixture == "ecdsa-merkle-checkpoints-storage-slot"
                          else stateful_strings_hex_arrays_bitmaps_source(fixture, variant) if args.fixture == "strings-hex-arrays-bitmaps"
                          else stateful_string_bytes_mappings_uri_storage_strings_source(fixture, variant) if args.fixture == "string-bytes-mappings-uri-storage-strings"
                          else stateful_timelock_and_bytes4_cast_source(fixture, variant) if args.fixture == "timelock-and-bytes4-cast"
                          else stateful_fixed_bytes_conversions_source(fixture, variant) if args.fixture == "fixed-bytes-conversions"
                          else stateful_packed_struct_mapping_ternary_tuple_source(fixture, variant) if args.fixture == "packed-struct-mapping-ternary-tuple"
                          else stateful_struct_params_and_balances_source(fixture, variant) if args.fixture == "struct-params-and-balances"
                          else stateful_ecrecover_authorizer_arrays_map_source(fixture, variant) if args.fixture == "ecrecover-authorizer-arrays-map"
                          else stateful_public_getters_and_builtins_source(fixture, variant) if args.fixture == "public-getters-and-builtins"
                          else stateful_votes_checkpoints_arrays_bitmaps_source(fixture, variant) if args.fixture == "votes-checkpoints-arrays-bitmaps"
                          else stateful_abi_decode_and_verifier_source(fixture, variant) if args.fixture == "abi-decode-and-verifier"
                          else stateful_struct_hash_and_domain_separator_source(fixture, variant) if args.fixture == "struct-hash-and-domain-separator"
                          else stateful_wad_exp_and_three_key_mapping_source(fixture, variant) if args.fixture == "wad-exp-and-three-key-mapping"
                          else stateful_checkpoints_and_struct_arrays_source(fixture, variant) if args.fixture == "checkpoints-and-struct-arrays"
                          else stateful_enumerable_set_map_storage_arrays_source(fixture, variant) if args.fixture == "enumerable-set-map-storage-arrays"
                          else stateful_erc2981_holders_arrays_msghash_source(fixture, variant) if args.fixture == "erc2981-holders-arrays-msghash"
                          else stateful_struct_mapping_and_bytes4_interface_source(fixture, variant) if args.fixture == "struct-mapping-and-bytes4-interface"
                          else stateful_udvt_param_assign_struct_hash_source(fixture, variant) if args.fixture == "udvt-param-assign-struct-hash"
                          else stateful_multiproof_mapping_keys_verifiers_source(fixture, variant) if args.fixture == "multiproof-mapping-keys-verifiers"
                          else stateful_merkle_and_nonces_source(fixture, variant) if args.fixture == "merkle-and-nonces"
                          else stateful_yul_block_mulmod_tstore_source(fixture, variant) if args.fixture == "yul-block-mulmod-tstore"
                          else stateful_bytes_and_string_storage_source(fixture, variant) if args.fixture == "bytes-and-string-storage"
                          else stateful_dynamic_bytes_and_string_return_source(fixture, variant) if args.fixture == "dynamic-bytes-and-string-return"
                          else stateful_bytes_memory_and_abi_encode_call_source(fixture, variant) if args.fixture == "bytes-memory-and-abi-encode-call"
                          else stateful_array_string_params_and_context_source(fixture, variant) if args.fixture == "array-string-params-and-context"
                          else stateful_yul_builtins_and_encode_selector_source(fixture, variant) if args.fixture == "yul-builtins-and-encode-selector"
                          else stateful_while_clz_and_struct_loc_source(fixture, variant) if args.fixture == "while-clz-and-struct-loc"
                          else stateful_exp_and_bitwise_shift_source(fixture, variant) if args.fixture == "exp-and-bitwise-shifts"
                          else stateful_msg_data_and_enum_source(fixture, variant) if args.fixture == "msg-data-and-enum"
                          else stateful_struct_fixed_array_and_fixed_return_source(fixture, variant) if args.fixture == "struct-fixed-array-and-fixed-return"
                          else stateful_overload_const_error_cond_tuple_tload_source(fixture, variant) if args.fixture == "overload-const-error-cond-tuple-tload"
                          else stateful_empty_array_bytes_calldata_source(fixture, variant) if args.fixture == "empty-array-bytes-calldata"
                          else stateful_fn_ptr_struct_delete_modifier_source(fixture, variant) if args.fixture == "fn-ptr-struct-delete-modifier"
                          else stateful_int256_contract_type_source(fixture, variant) if args.fixture == "int256-contract-types"
                          else stateful_tuple_helper_source(fixture, variant) if args.fixture == "tuple-helper"
                          else stateful_modifier_unchecked_compound_source(fixture, variant) if args.fixture == "modifier-unchecked-compound"
                          else stateful_void_helper_guard_source(fixture, variant) if args.fixture == "void-helper-guards"
                          else stateful_inheritance_source(fixture, variant) if args.fixture == "inheritance"
                          else stateful_solc_0810_source(fixture, variant) if args.fixture == "solc-0810"
                          else stateful_yul_numeric_source(fixture, variant) if args.fixture == "yul-numeric"
                          else stateful_named_helper_return_source(fixture, variant) if args.fixture == "named-helper-returns"
                          else stateful_encoded_byte_local_source(fixture, variant) if args.fixture == "encoded-byte-locals"
                          else stateful_discarded_helper_source(fixture, variant) if args.fixture == "discarded-helper"
                          else call_arg_source(fixture, variant) if args.fixture == 'call-arg-side-effects'
                          else stateful_array_write_order_source(fixture, variant) if args.fixture == "array-write-order"
                          else stateful_fixed_array_source(fixture, variant) if args.fixture == "fixed-arrays"
                          else stateful_helper_effect_source(fixture, variant) if args.fixture == "helper-effects"
                          else stateful_packed_member_write_source(fixture, variant) if args.fixture == "packed-member-writes"
                          else stateful_helper_loop_source(fixture, variant) if args.fixture == "helper-loops"
                          else stateful_invariant_for_source(fixture, variant) if args.fixture == "invariant-for"
                          else stateful_local_write_source(fixture, variant) if args.fixture == "local-writes"
                          else stateful_default_local_source(fixture, variant) if args.fixture == "default-locals"
                          else stateful_modulo_source(fixture, variant) if args.fixture == "modulo"
                          else stateful_fixed_memory_array_source(fixture, variant) if args.fixture == "fixed-memory-arrays"
                          else stateful_inline_array_literal_source(fixture, variant) if args.fixture == "inline-array-literals"
                          else stateful_helper_name_independence_source(fixture, variant) if args.fixture == "helper-name-independence"
                          else stateful_dynamic_memory_array_source(fixture, variant) if args.fixture == "dynamic-memory-arrays"
                          else stateful_signed_modulo_source(fixture, variant) if args.fixture == "signed-modulo"
                          else stateful_signed_compound_assignment_source(fixture, variant) if args.fixture == "signed-compound-assignment"
                          else stateful_signed_struct_compound_source(fixture, variant) if args.fixture == "signed-struct-compound"
                          else stateful_byte_constant_conversions_source(fixture, variant) if args.fixture == "byte-constant-conversions"
                          else stateful_yul_empty_revert_source(fixture, variant) if args.fixture == "yul-empty-revert"
                          else stateful_yul_revert_memory_source(fixture, variant) if args.fixture == "yul-revert-memory"
                          else stateful_signed_struct_member_read_source(fixture, variant) if args.fixture == "signed-struct-member-read"
                          else stateful_storage_string_member_source(fixture, variant) if args.fixture == "storage-string-members"
                          else stateful_packed_signed_int_source(fixture, variant) if args.fixture == "packed-signed-int"
                          else stateful_bytes_named_return_slice_struct_source(fixture, variant) if args.fixture == "bytes-named-return-slice-struct"
                          else stateful_bytes_named_return_stateless_source(fixture, variant) if args.fixture == "bytes-named-return-stateless"
                          else stateful_named_string_return_source(fixture, variant) if args.fixture == "named-string-return"
                          else stateful_root_param_source(fixture, variant, args.fixture) if args.fixture in ROOT_PARAM_RENAMES
                          else stateful_dynamic_array_root_return_source(fixture, variant, args.fixture) if args.fixture.startswith("dynamic-array-root-returns")
                          else stateful_constant_array_source(fixture, variant) if args.fixture == "constant-arrays"
                          else stateful_numeric_literal_source(fixture, variant) if args.fixture == "numeric-literals"
                          else stateful_if_else_source(fixture, variant) if args.fixture == "if-else"
                          else stateful_short_circuit_source(fixture, variant) if args.fixture == "short-circuit"
                          else stateful_mapping_source(fixture, variant) if args.fixture == "mapping"
                          else stateful_storage_source(fixture, variant) if args.fixture == "packed"
                          else stateful_storage_word_source(fixture, variant, args.fixture))
        driver = directory / 'Driver.lean'
        driver.write_text(template.replace(anchor, f'from "{directory}" entry "Sequence.sol"'))
        extra = ['--change-prefix', *map(str, list(range(9)) + [65535, 65536, (1 << 256) - 1])] if args.fixture == 'fixed-arrays' else []
        if args.fixture == 'empty-array-bytes-calldata':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 16, 17, 18, (1 << 256) - 1])]
        if args.fixture == 'custom-error-fixed-bytes':
            # Each `next % 4` arm with nonzero `bytesN` contents, and `next * 3` overflow.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 0xdeadbeef * 2 ** 224 + 1,
                                                   0x0123456789abcdef * 2 ** 192 + 0x7e,
                                                   2 ** 200 + 3, 2 ** 256 - 1, 2 ** 256 - 4])]
        if args.fixture in ('inheritance', 'void-helper-guards', 'modifier-unchecked-compound', 'tuple-helper', 'int256-contract-types', 'fn-ptr-struct-delete-modifier', 'overload-const-error-cond-tuple-tload', 'struct-fixed-array-and-fixed-return', 'msg-data-and-enum', 'exp-and-bitwise-shifts', 'while-clz-and-struct-loc', 'yul-builtins-and-encode-selector', 'array-string-params-and-context', 'bytes-memory-and-abi-encode-call', 'dynamic-bytes-and-string-return', 'bytes-and-string-storage', 'yul-block-mulmod-tstore', 'merkle-and-nonces', 'multiproof-mapping-keys-verifiers', 'udvt-param-assign-struct-hash', 'struct-mapping-and-bytes4-interface', 'erc2981-holders-arrays-msghash', 'enumerable-set-map-storage-arrays', 'checkpoints-and-struct-arrays', 'wad-exp-and-three-key-mapping', 'struct-hash-and-domain-separator', 'abi-decode-and-verifier', 'votes-checkpoints-arrays-bitmaps', 'public-getters-and-builtins', 'ecrecover-authorizer-arrays-map', 'struct-params-and-balances', 'packed-struct-mapping-ternary-tuple', 'timelock-and-bytes4-cast', 'string-bytes-mappings-uri-storage-strings', 'strings-hex-arrays-bitmaps', 'ecdsa-merkle-checkpoints-storage-slot', 'create2-clones-msgdata-deque', 'governor-slice-proposer-delay', 'access-manager-target-role'):

            extra = ['--change-prefix', *map(str, list(range(9)) + [19, 20, 21, 96, 97, 98, 99999, 100000, (1 << 256) - 1])]
        if args.fixture == 'yul-empty-revert':
            # Both zero-size revert branches (x % 5 == 0 and 1) and a call that stores.
            extra = ['--change-prefix', '10', '11', '12', '15', '16', '17']
        if args.fixture == 'yul-revert-memory':
            # Every revert shape (x % 8 in 0..5), with small and high-bit payload words, and
            # calls that store (x % 8 in 6, 7).
            extra = ['--change-prefix', *map(str, YUL_REVERT_MEMORY_PREFIX)]
        if args.fixture == 'signed-struct-member-read':
            # Negative, positive-extreme and read-only calls on every cell and both struct paths.
            extra = ['--change-prefix', *map(str, SIGNED_STRUCT_MEMBER_READ_PREFIX)]
        if args.fixture == 'storage-string-members':
            # Ids 0/1/255 (uint8 truncation, both `active` parities), high-word bitmap, tail and
            # flag bytes, the two-key mapping's three outer keys, and the all-ones word.
            extra = ['--change-prefix', *map(str, STORAGE_STRING_MEMBER_PREFIX)]
        if args.fixture == 'signed-compound-assignment':
            extra = ['--change-prefix', *map(str, SIGNED_COMPOUND_PREFIX)]
        if args.fixture == 'signed-struct-compound':
            extra = ['--change-prefix', *map(str, SIGNED_STRUCT_COMPOUND_PREFIX)]
        if args.fixture == 'packed-signed-int':
            # Both ends of every signed width, small negatives, and high-word operands.
            extra = ['--change-prefix', *map(str, PACKED_SIGNED_INT_PREFIX)]
        if args.fixture == 'signed-modulo':
            # Centered-reduction boundaries (ALPHA / 2, ALPHA, the 8380417
            # reduction), the narrow int8 range, and both min % -1 parities.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 127, 128, 255, 256,
                     261888, 261889, 523775, 523776, 8380416, 8380417, (1 << 256) - 1])]
        if args.fixture == 'byte-constant-conversions':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 5, 6, 15, 30, 99, 100])]
        if args.fixture == 'bytes-named-return-slice-struct':
            # Every `x % 3` arm of the named-return helper (unassigned, early
            # `return out`, assigned) and the uint8 truncation boundary.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 255, 256, 257, (1 << 256) - 1])]
        if args.fixture == 'bytes-named-return-stateless':
            # Both arms of the named-return `change` and the uint8 domain truncation.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 255, 256, 257, (1 << 256) - 1])]
        if args.fixture == 'named-string-return':
            # Every `x % 5` arm of the named-string `change` (unassigned,
            # literal, storage copy, early literal return, encoded bytes32).
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, (1 << 256) - 1])]
        if args.fixture.startswith('dynamic-array-root-returns'):
            # Every `x % 4` / `x % 5` length or arm, the `x % 7 == 6` storage
            # tuple return, and high bytes for the pushed addresses.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 7, 13, 20, 27, 255,
                     0x0102030405060708, (1 << 256) - 1])]
        if args.fixture == 'dynamic-memory-arrays':
            # Every length n = x % 5, the scaled alias (x % 3 == 0), the
            # out-of-range c[n] (x % 7 == 6) and v[2][0] (x % 11 == 10) panics.
            extra = ['--change-prefix', *map(str, DYNAMIC_MEMORY_ARRAY_PREFIX)]
        if args.fixture == 'helper-name-independence':
            # Negative and positive tick ranges, zero and high-word owners.
            extra = ['--change-prefix', *map(str, [0, 1, 499, 500, 999, 1000, 1 << 10, 99 << 10,
                     (1 << 96) | 7, (1 << 256) - 1])]
        if args.fixture == 'inline-array-literals':
            # Every mixed / small / table slot, the x % 9 == 8 out-of-range
            # table read (Panic(0x32): 8, 17), high words for x >> 240.
            extra = ['--change-prefix', *map(str, INLINE_ARRAY_LITERAL_PREFIX)]
        if args.fixture == 'fixed-memory-arrays':
            # Every pick offset (x % 4, including the aliasing k == 3 return),
            # every narrow slot, the x % 7 == 6 probe in range (6, 13) and out
            # of range (34, 41: Panic(0x32)), and high-byte selectors.
            extra = ['--change-prefix', *map(str, FIXED_MEMORY_ARRAY_PREFIX)]
        if args.fixture == 'msg-sig':
            # change(2^256 - 1) fills the 28 argument bytes that the msg.sig mask clears.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 10, 17, 999, 1000, (1 << 256) - 1])]
        if args.fixture == 'timelock-and-bytes4-cast':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 20, 21, 22])]
        if args.fixture == 'string-bytes-mappings-uri-storage-strings':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 4, 8, 20, 21])]
        if args.fixture == 'strings-hex-arrays-bitmaps':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 20, 21])]
        if args.fixture == 'ecdsa-merkle-checkpoints-storage-slot':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 20])]
        if args.fixture == 'create2-clones-msgdata-deque':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 20])]
        if args.fixture == 'narrow-for-counters':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 19, 20, 255, 256, 257, 299, 300, 555, 556, 999, 255000, 256000, (1 << 256) - 1])]
        if args.fixture == 'governor-slice-proposer-delay':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 20])]
        if args.fixture == 'access-manager-target-role':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 20])]
        if args.fixture == 'unchecked-blocks':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 9, 10, 100, 101, 129, 130, 255, 256, 262, 263, (1 << 256) - 1])]
        if args.fixture == 'dynamic-revert-string':
            # Every `next % 5` arm, the always-evaluated hex message helper
            # (its own revert for next > 65535 with a holding condition), and the
            # `bounded` failure.
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 10, 999, 1000, 1005, 65535, 65536, 70000])]
        if args.fixture == 'tuple-destructuring':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 15, 31, 86399, 86400, 86401, 604799, 604800, 691199])]

        if args.fixture == 'solc-0810':
            extra = ['--solc-version', '0.8.10', '--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 100, 1000, 50000, 100000, 999999, (1 << 256) - 1])]
        if args.fixture == 'fixed-bytes-conversions':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 4, 5, 6, 13, 4294967295, 4294967296, (1 << 256) - 1])]
        if args.fixture == 'yul-numeric':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 32, 33, 255, 256, (1 << 255) - 1, 1 << 255, (1 << 256) - 2, (1 << 256) - 1])]
        if args.fixture == 'named-helper-returns':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 40, 50, 60, 70, 255, 256, 257, (1 << 160) - 1, 1 << 160, (1 << 160) + 1, (1 << 256) - 1])]
        if args.fixture == 'encoded-byte-locals':
            extra = ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 31, 32, 33, 255, 256, (1 << 256) - 1])]
        if args.fixture in ('array-write-order', 'discarded-helper'):
            extra = ['--change-prefix', *map(str, list(range(9)) + [19, 20, 25, 30, 40, (1 << 256) - 1])]
        command([sys.executable, '-m', 'solidity_differential.check_stateful',
                 '--model-driver', driver, '--source-fixture', source,
                 '--argument-bits', str(args.narrow_bits) if args.fixture == 'narrow-event' else '256',
                 '--senders', '3', '--transactions', str(args.transactions), '--seed', str(args.seed),
                 '--output', directory / 'campaign'] + extra, timeout=1800, log=directory / 'check.log')
        result = json.loads((directory / 'campaign' / 'campaign.json').read_text())
        observable = {'transactions': result['transactions'],
                      'observations': canonical_observations(result['observations'])}
        if baseline is None:
            baseline = observable
        elif observable != baseline:
            write_json(output / 'metamorphic-divergence.json',
                       {'variant': variant, 'baseline': baseline, 'actual': observable})
            raise RuntimeError(f'storage variant {variant} changed observable behavior')
        completed.append(variant)
        write_json(output / 'completed.json', completed)
    print(f'Imported storage variants agree: {output}')


if __name__ == '__main__':
    main()
