"""Pinned-sequence A/B/C campaigns over contracts pinned in the import corpus.

A corpus project's `sequences` are pinned-sequence configurations without
`project` and `revision`: both come from the project's checkout at its full
commit SHA (`solidity_import_coverage.checkout`, which rejects a wrong revision
or a dirty tree). Each prefix step states its documented source outcome
(`expect`), and every imported signature must succeed at least once in the
prefix before seeded calls start. Before any campaign, a solc-only compile
requires the imported signatures to be exactly the contract's function entry
points, and rejects a `receive` or `fallback` entry point, which the instrument
cannot call. The positive campaign must agree across
A/B/C; the `drop-events` model mutant must diverge and shrink to a reproduced
deletion-minimal witness.
"""
import argparse
import json
from pathlib import Path

from .engine import ROOT, HarnessError, solc_compile, write_json
from .pinned_sequence import campaign, compiler_checksum, load_config, pinned_sources

MANIFEST = ROOT / 'scripts/solidity_import_corpus/manifest.json'
SEQUENCE_KEYS = {'entry', 'contract', 'settings', 'signatures', 'initialStorage',
                 'prefix', 'arguments'}


def corpus_sequences(manifest, selected=None):
    """Validated (project, sequence) pairs, in manifest order."""
    pairs = []
    for project in manifest['projects']:
        if selected is not None and project['id'] not in selected:
            continue
        for sequence in project.get('sequences', []):
            name = f'{project["id"]}:{sequence.get("contract")}'
            if set(sequence) != SEQUENCE_KEYS:
                raise HarnessError(f'{name}: sequence keys must be exactly {sorted(SEQUENCE_KEYS)}')
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
    """Imported signatures equal the compiled contract's entry points, none left out."""
    contract = solc_output['contracts'][sequence['entry']][sequence['contract']]
    special = sorted({row['type'] for row in contract['abi']} & {'receive', 'fallback'})
    if special:
        raise HarnessError(f'{sequence["contract"]}: unsupported {special} entry point')
    methods = contract['evm']['methodIdentifiers']
    missing = sorted(set(methods) - set(sequence['signatures']))
    extra = sorted(set(sequence['signatures']) - set(methods))
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


def run_sequence(project, sequence, config, root, transactions, seed,
                 entry_points=compiled_entry_points, run=campaign):
    """Entry-point completeness, then the positive campaign, then the mutant."""
    name = f'{project["id"]}:{sequence["contract"]}'
    check_entry_points(sequence, entry_points(config, root))
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
            'seed': seed, 'mutantWitness': len(reduced['transactions'])}


def materialize(project, sequence, checkout, output):
    """Write the complete instrument configuration for one corpus sequence."""
    path = output / 'config.json'
    write_json(path, {'project': str(Path(checkout).resolve()), 'revision': project['commit'],
                      **sequence})
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
