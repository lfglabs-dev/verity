"""Execute Denote creation mutants against real EVM, with minimal replays.

These calibrate the world primitive (A/B), not a compiled-model C route.
Build/resource failures are never mutation detection. Only a completed
comparison with an archived semantic divergence is accepted.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json
from .mutations import release, snapshot

MUTANTS = {
    'denote-create2-drop-nonce': (
        '{ creator with nonce := ⟨creator.nonce.val + 1, h⟩ }', 'creator', [0]),
    'denote-create2-empty-code': (
        'commitRuntime incremented context.creator target context.value runtime',
        'commitRuntime incremented context.creator target context.value []', [0]),
    'denote-create2-drop-value': (
        'commitRuntime incremented context.creator target context.value runtime',
        'commitRuntime incremented context.creator target 0 runtime', [0]),
    'denote-create2-drop-deposit': (
        'let totalCost := executionCost + 200 * runtime.length',
        'let totalCost := executionCost', [0]),
    'denote-create2-ignore-collision': (
        'if (incremented.accountWorld target).collidesOsaka then', 'if false then', [0, 1]),
}


def signature(divergence):
    actual, expected = divergence['actual'], divergence['expected']
    if actual['id'] != expected['id']:
        raise HarnessError('creation witness identity differs')
    categories = []
    if actual['status'] != expected['status']: categories.append('status')
    if expected['status'] == 'ok' and actual['address'] != expected['address']: categories.append('address')
    if expected['childGasLeft'] is not None and actual['childGasLeft'] != expected['childGasLeft']:
        categories.append('child-gas')
    aa = {row['address']: row for row in actual['accounts']}
    ea = {row['address']: row for row in expected['accounts']}
    if len(aa) != len(actual['accounts']) or len(ea) != len(expected['accounts']) or set(aa) != set(ea):
        raise HarnessError('creation witness omits or duplicates account observations')
    for field in ('nonce', 'balance', 'code', 'storage'):
        if any(aa[address][field] != ea[address][field] for address in aa):
            categories.append('account-' + field)
    if not categories:
        raise HarnessError('creation witness contains no semantic mismatch')
    return categories


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    head = command(['git', 'rev-parse', 'HEAD']).strip()
    if command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('creation mutations require a clean exact checkout')
    # Mutate a private snapshot: concurrent campaigns read the parent checkout.
    repo = out / 'snapshot'
    snapshot(repo)
    env = dict(os.environ, PYTHONPATH=str(repo / 'scripts'))
    source = repo / 'Verity/Core/Model/DenoteCreate2.lean'
    original = source.read_text()
    original_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    def run(directory, ids=None, require_divergence=False):
        argv = [sys.executable, '-m', 'solidity_differential.check_deployment_world', '--output', directory]
        if ids is not None: argv += ['--case-ids', *map(str, ids)]
        with (directory.parent / (directory.name + '.log')).open('x') as log:
            result = subprocess.run(list(map(str, argv)), cwd=repo, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=MUTANT_BUILD_TIMEOUT + 300)
        source_rows = json.loads((directory / 'source-observations.json').read_text())
        model_rows = json.loads((directory / 'model-observations.json').read_text())
        if len(source_rows) != len(model_rows):
            raise HarnessError('mutation did not complete model execution')
        if require_divergence:
            divergence = json.loads((directory / 'divergence.json').read_text())
            if result.returncode == 0 or not divergence or divergence['actual'] == divergence['expected']:
                raise HarnessError('creation mutant survived or failed without a semantic witness')
            signature(divergence)
        else:
            if result.returncode != 0 or json.loads((directory / 'complete.json').read_text())['exit'] != 0:
                raise HarnessError('baseline or deletion control failed')
        write_json(directory / 'implementation.json', {'head': head,
            'moduleSha256': hashlib.sha256(source.read_bytes()).hexdigest()})
    baseline = out / 'baseline'
    run(baseline)
    baseline_input = json.loads((baseline / 'input.json').read_text())
    results = []
    try:
        for name, (before, after, witness) in MUTANTS.items():
            if original.count(before) != 1:
                raise HarnessError('nonunique creation mutation anchor: ' + name)
            mutant = original.replace(before, after)
            source.write_text(mutant)
            directory = out / name
            directory.mkdir()
            run(directory / 'full', require_divergence=True)
            full_input = json.loads((directory / 'full/input.json').read_text())
            if full_input != baseline_input:
                raise HarnessError('baseline and mutant creation environments differ')
            run(directory / 'witness', witness, require_divergence=True)
            full_signature = signature(json.loads((directory / 'full/divergence.json').read_text()))
            witness_signature = signature(json.loads((directory / 'witness/divergence.json').read_text()))
            if full_signature != witness_signature:
                raise HarnessError('minimal creation witness changed divergence categories')
            actual_input = json.loads((directory / 'witness/input.json').read_text())
            if actual_input['initialAccounts'] != baseline_input['initialAccounts']:
                raise HarnessError('minimal witness changed the initial world')
            # Reexecute every single-deletion candidate from identical prestate.
            for index in range(len(witness)):
                run(directory / ('delete-' + str(index)), witness[:index] + witness[index + 1:])
            mutant_hash = hashlib.sha256(mutant.encode()).hexdigest()
            for phase in ('full', 'witness'):
                manifest = json.loads((directory / phase / 'implementation.json').read_text())
                if manifest != {'head': head, 'moduleSha256': mutant_hash}:
                    raise HarnessError('creation mutation implementation provenance differs')
            results.append({'mutant': name, 'detected': True, 'baselinePassed': True,
                            'witnessCaseIds': witness, 'deletion_minimal': True,
                            'signature': witness_signature,
                            'moduleSha256': mutant_hash, 'scope': 'real EVM/Lean world primitive, no C route'})
            write_json(out / 'mutation-results.json', results)
    finally:
        source.write_text(original)
        if hashlib.sha256(source.read_bytes()).hexdigest() != original_hash:
            raise HarnessError('creation mutation failed to restore implementation')
        release(repo)
    if command(['git', 'rev-parse', 'HEAD']).strip() != head or command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('creation mutation checkout identity changed')
    write_json(out / 'complete.json', {'head': head, 'exit': 0, 'mutants': len(results),
                                      'scope': 'world primitive mutation checks only'})
    print(f'Detected {len(results)} actual creation mutants with deletion-minimal EVM/Lean witnesses')


if __name__ == '__main__':
    main()
