"""Run actual imported packed storage variants through all three stateful routes."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

from .engine import command, write_json
from .programs import stateful_storage_source, stateful_storage_word_source, stateful_mapping_source, stateful_short_circuit_source, stateful_imported_event_source, stateful_if_else_source, stateful_numeric_literal_source, stateful_constant_array_source, stateful_modulo_source, stateful_default_local_source, stateful_local_write_source, stateful_invariant_for_source, stateful_helper_loop_source, stateful_packed_member_write_source, stateful_helper_effect_source, stateful_fixed_array_source, stateful_array_write_order_source, stateful_discarded_helper_source, stateful_encoded_byte_local_source, stateful_named_helper_return_source, stateful_yul_numeric_source, stateful_solc_0810_source, stateful_inheritance_source, stateful_void_helper_guard_source, stateful_modifier_unchecked_compound_source, stateful_tuple_helper_source
from .stateful import validate_observation


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', choices=('packed', 'void', 'bytes', 'mapping', 'short-circuit', 'imported-event', 'narrow-event', 'if-else', 'numeric-literals', 'constant-arrays', 'modulo', 'default-locals', 'local-writes', 'invariant-for', 'helper-loops', 'packed-member-writes', 'helper-effects', 'fixed-arrays', 'array-write-order', 'discarded-helper', 'encoded-byte-locals', 'named-helper-returns', 'yul-numeric', 'solc-0810', 'inheritance', 'void-helper-guards', 'modifier-unchecked-compound', 'tuple-helper'), default='packed')
    parser.add_argument('--narrow-bits', type=int, choices=range(8, 257, 8), default=128)
    parser.add_argument('--transactions', type=int, default=32)
    parser.add_argument('--seed', type=int, default=2453)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='storage-', dir='.lake')).resolve()
    output.mkdir(parents=True, exist_ok=args.output is None)
    name = {'packed': 'StorageSequence', 'void': 'StorageVoidSequence', 'bytes': 'StorageBytesSequence', 'mapping': 'MappingSequence', 'short-circuit': 'ShortCircuitSequence', 'imported-event': 'ImportedEventSequence', 'narrow-event': 'NarrowEventSequence', 'if-else': 'IfElseSequence', 'numeric-literals': 'NumericLiteralSequence', 'constant-arrays': 'ConstantArraySequence', 'modulo': 'ModuloSequence', 'default-locals': 'DefaultLocalSequence', 'local-writes': 'LocalWriteSequence', 'invariant-for': 'InvariantForSequence', 'helper-loops': 'HelperLoopSequence', 'packed-member-writes': 'PackedMemberWriteSequence', 'helper-effects': 'HelperEffectSequence', 'fixed-arrays': 'MappingFixedArraySequence', 'array-write-order': 'FixedArrayWriteOrderSequence', 'discarded-helper': 'DiscardedHelperSequence', 'encoded-byte-locals': 'EncodedByteLocalSequence', 'named-helper-returns': 'NamedHelperReturnSequence', 'yul-numeric': 'YulNumericSequence', 'solc-0810': 'Solc0810Sequence', 'inheritance': 'InheritanceSequence', 'void-helper-guards': 'VoidHelperGuardSequence', 'modifier-unchecked-compound': 'ModifierUncheckedCompoundSequence', 'tuple-helper': 'TupleHelperSequence'}[args.fixture]
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
    if args.fixture == 'short-circuit':
        variants = ('baseline', 'conditional', 'de-morgan')
    if args.fixture in ('numeric-literals', 'constant-arrays'):
        variants = ('baseline', 'renamed', 'normalized')
    if args.fixture in ('invariant-for', 'helper-loops'):
        variants = ('baseline', 'renamed', 'assignment-step')
    if args.fixture in ('packed-member-writes', 'helper-effects', 'fixed-arrays'):
        variants = ('baseline', 'renamed', 'explicit-delete')
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
    if args.fixture == 'modulo':
        variants = ('baseline', 'renamed', 'quotient')
    if args.fixture == 'if-else':
        variants = ('baseline', 'inverted', 'ternary')
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
                          else stateful_tuple_helper_source(fixture, variant) if args.fixture == "tuple-helper"
                          else stateful_modifier_unchecked_compound_source(fixture, variant) if args.fixture == "modifier-unchecked-compound"
                          else stateful_void_helper_guard_source(fixture, variant) if args.fixture == "void-helper-guards"
                          else stateful_inheritance_source(fixture, variant) if args.fixture == "inheritance"
                          else stateful_solc_0810_source(fixture, variant) if args.fixture == "solc-0810"
                          else stateful_yul_numeric_source(fixture, variant) if args.fixture == "yul-numeric"
                          else stateful_named_helper_return_source(fixture, variant) if args.fixture == "named-helper-returns"
                          else stateful_encoded_byte_local_source(fixture, variant) if args.fixture == "encoded-byte-locals"
                          else stateful_discarded_helper_source(fixture, variant) if args.fixture == "discarded-helper"
                          else stateful_array_write_order_source(fixture, variant) if args.fixture == "array-write-order"
                          else stateful_fixed_array_source(fixture, variant) if args.fixture == "fixed-arrays"
                          else stateful_helper_effect_source(fixture, variant) if args.fixture == "helper-effects"
                          else stateful_packed_member_write_source(fixture, variant) if args.fixture == "packed-member-writes"
                          else stateful_helper_loop_source(fixture, variant) if args.fixture == "helper-loops"
                          else stateful_invariant_for_source(fixture, variant) if args.fixture == "invariant-for"
                          else stateful_local_write_source(fixture, variant) if args.fixture == "local-writes"
                          else stateful_default_local_source(fixture, variant) if args.fixture == "default-locals"
                          else stateful_modulo_source(fixture, variant) if args.fixture == "modulo"
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
        if args.fixture in ('inheritance', 'void-helper-guards', 'modifier-unchecked-compound', 'tuple-helper'):
            extra = ['--change-prefix', *map(str, list(range(9)) + [19, 20, 21, 96, 97, 98, 99999, 100000, (1 << 256) - 1])]
        if args.fixture == 'solc-0810':
            extra = ['--solc-version', '0.8.10', '--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 100, 1000, 50000, 100000, 999999, (1 << 256) - 1])]
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
