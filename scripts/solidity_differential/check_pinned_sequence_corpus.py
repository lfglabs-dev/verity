"""Pinned-sequence A/B/C campaigns over contracts pinned in the import corpus.

A corpus project's `sequences` are pinned-sequence configurations without
`project` and `revision`: both come from the project's checkout at its full
commit SHA (`solidity_import_coverage.checkout`, which rejects a wrong revision
or a dirty tree). Each prefix step states its documented source outcome
(`expect`), and every imported signature must succeed at least once in the
prefix before seeded calls start. Before any campaign, a solc-only compile
requires the imported signatures to be exactly the contract's function entry
points, and rejects a `receive` or `fallback` entry point, which the instrument
cannot call. A function the importer rejects is listed under `rejected` with
its located rejection; the compile counts it as an entry point, and a separate
import of exactly that function must fail with exactly that first error line.
A sequence may pass `constructorArgs` and deploy `dependencies` first: each names
another sequence of the same project (same settings), whose own campaign in this
check validates the imported model that answers the tested contract's static
calls on the model route. The positive campaign must agree across A/B/C; the
`drop-events` model mutant must diverge and shrink to a reproduced
deletion-minimal witness.
"""
import argparse
import json
from pathlib import Path
import re

from .engine import ROOT, HarnessError, command, run_bounded, solc_compile, write_json
from .pinned_sequence import (argument_types, campaign, compiler_checksum, import_command,
                              load_config, pinned_sources)

MANIFEST = ROOT / 'scripts/solidity_import_corpus/manifest.json'
SEQUENCE_KEYS = {'entry', 'contract', 'settings', 'signatures', 'initialStorage',
                 'prefix', 'arguments'}
OPTIONAL_KEYS = {'constructorArgs', 'dependencies', 'rejected'}
DEPENDENCY_KEYS = {'contract', 'constructorArgs', 'initialStorage'}


def corpus_sequences(manifest, selected=None):
    """Validated (project, sequence) pairs, in manifest order."""
    pairs = []
    for project in manifest['projects']:
        if selected is not None and project['id'] not in selected:
            continue
        contracts = [sequence.get('contract') for sequence in project.get('sequences', [])]
        if len(set(contracts)) != len(contracts):
            raise HarnessError('corpus sequences must name distinct contracts per project')
        for sequence in project.get('sequences', []):
            name = f'{project["id"]}:{sequence.get("contract")}'
            if not SEQUENCE_KEYS <= set(sequence) <= SEQUENCE_KEYS | OPTIONAL_KEYS:
                raise HarnessError(f'{name}: sequence keys must be {sorted(SEQUENCE_KEYS)} '
                                   f'plus optional {sorted(OPTIONAL_KEYS)}')
            rejected = [row.get('signature') for row in sequence.get('rejected', [])]
            if any(set(row) != {'signature', 'rejection'} or not row['rejection']
                   for row in sequence.get('rejected', [])):
                raise HarnessError(f'{name}: each rejected function needs a signature and its rejection')
            if len(set(rejected)) != len(rejected) or set(rejected) & set(sequence['signatures']):
                raise HarnessError(f'{name}: rejected functions must be distinct and not imported')
            for signature in rejected:
                argument_types(signature)
            for row in sequence.get('dependencies', []):
                if set(row) != DEPENDENCY_KEYS:
                    raise HarnessError(f'{name}: dependency keys must be exactly {sorted(DEPENDENCY_KEYS)}')
                validated = [s for s in project['sequences'] if s.get('contract') == row['contract']]
                if row['contract'] == sequence['contract'] or len(validated) != 1:
                    raise HarnessError(f'{name}: dependency {row["contract"]} must be another '
                                       f'sequence of the project')
                if validated[0]['settings'] != sequence['settings'] or validated[0].get('dependencies'):
                    raise HarnessError(f'{name}: dependency {row["contract"]} must share the settings '
                                       f'and deploy no dependency of its own')
            if len(set(sequence['signatures'])) != len(sequence['signatures']):
                raise HarnessError(f'{name}: duplicate imported signatures')
            missing = [index for index, row in enumerate(sequence['prefix']) if 'expect' not in row]
            if missing:
                raise HarnessError(f'{name}: prefix steps {missing} lack a documented expect')
            succeeding = {row['signature'] for row in sequence['prefix'] if row['expect'] == 'ok'}
            absent = [s for s in sequence['signatures'] if s not in succeeding]
            if absent:
                raise HarnessError(f'{name}: no succeeding prefix step for {absent}')
            pairs.append((project, sequence))
    names = [(p['id'], s['contract']) for p, s in pairs]
    if len(set(names)) != len(names):
        raise HarnessError('corpus sequences must name distinct contracts per project')
    if selected is not None and {p['id'] for p, _ in pairs} != set(selected):
        raise HarnessError('selected project has no corpus sequence')
    return pairs


def check_entry_points(sequence, solc_output):
    """Imported and rejected signatures equal the compiled contract's entry points."""
    contract = solc_output['contracts'][sequence['entry']][sequence['contract']]
    special = sorted({row['type'] for row in contract['abi']} & {'receive', 'fallback'})
    if special:
        raise HarnessError(f'{sequence["contract"]}: unsupported {special} entry point')
    methods = contract['evm']['methodIdentifiers']
    listed = set(sequence['signatures']) | {row['signature'] for row in sequence.get('rejected', [])}
    missing = sorted(set(methods) - listed)
    extra = sorted(listed - set(methods))
    if missing or extra:
        raise HarnessError(f'{sequence["contract"]}: signatures differ from compiled entry points: '
                           f'missing {missing}, unknown {extra}')


def compiled_entry_points(config_path, output):
    """solc-only compile of the pinned entry: ABI and method identifiers."""
    config = load_config(config_path)
    sources, _ = pinned_sources(config['project'], config['revision'], config['entry'])
    compiler_checksum()
    settings = {**config['settings'], 'outputSelection': {'*': {'*': ['abi', 'evm.methodIdentifiers']}}}
    return solc_compile({'language': 'Solidity', 'sources': {config['entry']: sources[config['entry']]},
                         'settings': settings}, config['project'], output / 'entry-points')


ERROR_LINE = re.compile(r'^(?P<file>[^\n]*?):(?P<line>[0-9]+):[0-9]+: error: (?P<message>[^\n]*)$',
                        re.MULTILINE)


def rejection_source(config, rejected):
    """One `solidity_import` of exactly one rejected function per command; first lines."""
    commands, lines, line = ['import Compiler.SolidityImport.Import'], [], 2
    for index, row in enumerate(rejected):
        text = import_command(f'rejected{index}', config['project'], config, config['entry'],
                              config['contract'], [row['signature']])
        commands.append(text)
        lines.append(line)
        line += text.count('\n') + 1
    return '\n'.join(commands) + '\n', lines


def check_rejections(config_path, rejected, output, lean=('lake', 'env', 'lean')):
    """Each rejected function alone fails to import with exactly its located rejection."""
    if not rejected:
        return
    config = load_config(config_path)
    pinned_sources(config['project'], config['revision'], config['entry'])
    source, lines = rejection_source(config, rejected)
    path = output / 'Rejections.lean'
    path.write_text(source)
    result = run_bounded([*lean, path], timeout=1800)
    log = result.stdout + result.stderr
    (output / 'rejections.log').write_text(log)
    errors = {}
    for match in ERROR_LINE.finditer(log):
        if Path(match['file']).name == path.name:
            errors.setdefault(int(match['line']), []).append(match['message'])
    if result.returncode == 0 or set(errors) != set(lines):
        raise HarnessError(f'rejected functions: errors at lines {sorted(errors)}, expected {lines}')
    for line, row in zip(lines, rejected):
        if errors[line] != [row['rejection']]:
            raise HarnessError(f'{row["signature"]}: rejection differs: {errors[line]}')


RESPONDER_DOMAIN = 'test/ByteExternalCall/ModelResponderDomain.lean'


def check_responder_domain(output):
    """The dependency responder answers in domain and rejects every out-of-domain request."""
    stdout = command(['lake', 'env', 'lean', '--run', RESPONDER_DOMAIN], timeout=900,
                     log=output / 'model-responder-domain.log')
    if stdout.strip().splitlines()[-1:] != ['model responder domain checks passed']:
        raise HarnessError('model responder domain checks did not pass')


def run_sequence(project, sequence, config, root, transactions, seed,
                 entry_points=compiled_entry_points, run=campaign, rejections=check_rejections):
    """Entry points, located rejections, then the positive campaign, then the mutant."""
    name = f'{project["id"]}:{sequence["contract"]}'
    check_entry_points(sequence, entry_points(config, root))
    rejections(config, sequence.get('rejected', []), root)
    if run(config, root / 'positive', transactions, seed, 200) != 0:
        raise HarnessError(f'{name}: pinned A/B/C campaign diverged; '
                           f'witness in {root / "positive/reduced.json"}')
    if run(config, root / 'drop-events', transactions, seed, 200, mutant='drop-events') != 1:
        raise HarnessError(f'{name}: event-deletion mutant escaped')
    reduced = json.loads((root / 'drop-events/reduced.json').read_text())
    if not reduced['deletion_minimal'] or not reduced['transactions']:
        raise HarnessError(f'{name}: mutant lacks a minimal witness')
    return {'project': project['id'], 'revision': project['commit'],
            'contract': sequence['contract'], 'transactions': transactions,
            'seed': seed, 'mutantWitness': len(reduced['transactions']),
            'rejected': [row['signature'] for row in sequence.get('rejected', [])],
            'dependencies': [row['contract'] for row in sequence.get('dependencies', [])]}


def materialize(project, sequence, checkout, output):
    """Write the complete instrument configuration for one corpus sequence.

    A dependency takes its entry and imported signatures from its own sequence."""
    path = output / 'config.json'
    config = {key: value for key, value in sequence.items() if key != 'rejected'}
    dependencies = []
    for row in sequence.get('dependencies', []):
        validated = next(s for s in project['sequences'] if s['contract'] == row['contract'])
        dependencies.append({'entry': validated['entry'], 'contract': row['contract'],
                             'signatures': validated['signatures'],
                             'constructorArgs': row['constructorArgs'],
                             'initialStorage': row['initialStorage']})
    if dependencies:
        config['dependencies'] = dependencies
    write_json(path, {'project': str(Path(checkout).resolve()), 'revision': project['commit'],
                      **config})
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--transactions', type=int, default=128)
    parser.add_argument('--seed', type=int, default=2514)
    parser.add_argument('--manifest', type=Path, default=MANIFEST)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/pinned-sequence-corpus')
    parser.add_argument('--fetch', action='store_true')
    parser.add_argument('--project', action='append')
    args = parser.parse_args()
    # Loaded here: the corpus checkout helper lives with the coverage script.
    from solidity_import_coverage import checkout
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    pairs = corpus_sequences(json.loads(args.manifest.read_text()), args.project)
    if not pairs:
        raise HarnessError('no corpus sequences configured')
    if any(sequence.get('dependencies') for _, sequence in pairs):
        check_responder_domain(output)
    summary = []
    for project, sequence in pairs:
        root = output / f'{project["id"]}-{sequence["contract"]}'
        root.mkdir()
        config = materialize(project, sequence, checkout(project, args.cache.resolve(), args.fetch), root)
        summary.append(run_sequence(project, sequence, config, root, args.transactions, args.seed))
    write_json(output / 'complete.json', {'exit': 0, 'sequences': summary})
    print(f'pinned corpus sequences: {len(summary)} positive A/B/C campaigns agree, '
          f'mutants detected: {output}')


if __name__ == '__main__':
    main()
