"""Pinned-sequence A/B/C campaigns over contracts pinned in the import corpus.

A corpus project's `sequences` are pinned-sequence configurations without
`project` and `revision`: both come from the project's checkout at its full
commit SHA (`solidity_import_coverage.checkout`, which rejects a wrong revision
or a dirty tree). Each prefix step states its documented source outcome
(`expect`), and every imported signature must succeed at least once in the
prefix before seeded calls start, and the imported signatures must be exactly
the compiled contract's external entry points. The positive campaign must agree across
A/B/C; the `drop-events` model mutant must diverge and shrink to a reproduced
deletion-minimal witness.
"""
import argparse
import json
from pathlib import Path

from .engine import ROOT, HarnessError, write_json
from .pinned_sequence import campaign

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
    methods = solc_output['contracts'][sequence['entry']][sequence['contract']]['evm']['methodIdentifiers']
    missing = sorted(set(methods) - set(sequence['signatures']))
    extra = sorted(set(sequence['signatures']) - set(methods))
    if missing or extra:
        raise HarnessError(f'{sequence["contract"]}: signatures differ from compiled entry points: '
                           f'missing {missing}, unknown {extra}')


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
        if campaign(config, root / 'positive', args.transactions, args.seed, 200) != 0:
            raise HarnessError(f'{project["id"]}:{sequence["contract"]}: pinned A/B/C campaign diverged; '
                               f'witness in {root / "positive/reduced.json"}')
        check_entry_points(sequence, json.loads((root / 'positive/source-solc.output.json').read_text()))
        if campaign(config, root / 'drop-events', args.transactions, args.seed, 200,
                    mutant='drop-events') != 1:
            raise HarnessError(f'{project["id"]}:{sequence["contract"]}: event-deletion mutant escaped')
        reduced = json.loads((root / 'drop-events/reduced.json').read_text())
        if not reduced['deletion_minimal'] or not reduced['transactions']:
            raise HarnessError(f'{project["id"]}:{sequence["contract"]}: mutant lacks a minimal witness')
        summary.append({'project': project['id'], 'revision': project['commit'],
                        'contract': sequence['contract'], 'transactions': args.transactions,
                        'seed': args.seed, 'mutantWitness': len(reduced['transactions'])})
    write_json(output / 'complete.json', {'exit': 0, 'sequences': summary})
    print(f'pinned corpus sequences: {len(summary)} positive A/B/C campaigns agree, '
          f'mutants detected: {output}')


if __name__ == '__main__':
    main()
