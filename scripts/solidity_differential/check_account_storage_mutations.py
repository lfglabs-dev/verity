"""Valid model mutations rejected by the production storage-coherence proofs.

Each mutant must first compile Verity.Core, then fail the unchanged coherence
theorems. Parse, name-resolution, resource or dependency failures are not
detection. These are kernel conformance controls, not runtime A/B/C witnesses.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from .engine import MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json


MUTANTS = {
    'denote-physical-slot-account': (
        '((s.accountWorld s.thisAddress).writeStorage slot value)',
        '((s.accountWorld s.thisAddress).writeStorage (slot + 1) value)'),
    'denote-physical-batch-account': (
        '((s.accountWorld s.thisAddress).writeStorageValues targets (fun _ => value))',
        '((s.accountWorld s.thisAddress).writeStorageValues (targets.map (fun slot => slot + 1)) (fun _ => value))'),
    'denote-physical-modify-account': (
        '(fun slot => f (s.storageWords (.slot slot))))',
        '(fun slot => f (s.storageWords (.slot (slot + 1)))))'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo = Path.cwd()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('storage conformance mutations require a clean exact checkout')
    head = command(['git', 'rev-parse', 'HEAD']).strip()
    work = out / 'work'
    command(['git', 'clone', '--shared', '--no-hardlinks', repo, work])
    command(['git', '-C', work, 'checkout', '--detach', head])
    (work / '.lake').mkdir()
    command(['cp', '-a', '--reflink=auto', repo / '.lake/build', work / '.lake/build'])
    (work / '.lake/packages').symlink_to((repo / '.lake/packages').resolve(), target_is_directory=True)
    source = work / 'Verity/Core.lean'
    proof = work / 'Verity/Core/Model/AccountStorageBridge.lean'
    original = source.read_text()
    proof_sha = hashlib.sha256(proof.read_bytes()).hexdigest()

    def build(directory, target):
        directory.mkdir(parents=True, exist_ok=False)
        with (directory / 'build.log').open('x') as log:
            result = subprocess.run(['lake', 'build', target], cwd=work,
                                    stdout=log, stderr=subprocess.STDOUT,
                                    timeout=MUTANT_BUILD_TIMEOUT)
        write_json(directory / 'receipt.json', {'head': head, 'exit': result.returncode,
            'target': target, 'coreSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'proofSha256': hashlib.sha256(proof.read_bytes()).hexdigest()})
        if hashlib.sha256(proof.read_bytes()).hexdigest() != proof_sha:
            raise HarnessError('production coherence assertions changed during mutation')
        return result.returncode, (directory / 'build.log').read_text()

    code, _ = build(out / 'baseline', 'Verity.Core.Model.AccountStorageBridge')
    if code:
        raise HarnessError('storage conformance baseline failed')
    rows = []
    try:
        for name, (before, after) in MUTANTS.items():
            if original.count(before) != 1:
                raise HarnessError('nonunique storage conformance anchor: ' + name)
            mutated = original.replace(before, after)
            source.write_text(mutated)
            code, _ = build(out / name / 'implementation', 'Verity.Core')
            if code:
                raise HarnessError('mutated implementation did not compile; not a detection')
            code, log = build(out / name / 'proof', 'Verity.Core.Model.AccountStorageBridge')
            if (code != 1 or 'error: Verity/Core/Model/AccountStorageBridge.lean:' not in log
                    or 'unsolved goals' not in log
                    or any(marker in log for marker in ['Unknown identifier', 'unexpected token',
                                                       'out of memory', 'stack overflow'])):
                raise HarnessError('mutant was not rejected by unchanged semantic coherence assertions')
            sha = hashlib.sha256(mutated.encode()).hexdigest()
            for phase in ['implementation', 'proof']:
                receipt = json.loads((out / name / phase / 'receipt.json').read_text())
                if receipt['coreSha256'] != sha or receipt['proofSha256'] != proof_sha:
                    raise HarnessError('executed storage mutation provenance differs')
            rows.append({'mutant': name, 'detected': True, 'baselinePassed': True,
                         'implementationCompiles': True, 'kind': 'kernel-conformance-rejection',
                         'coreSha256': sha, 'proofSha256': proof_sha})
            write_json(out / 'mutation-results.json', rows)
            source.write_text(original)
    finally:
        source.write_text(original)
    if command(['git', 'rev-parse', 'HEAD']).strip() != head or command(['git', 'status', '--porcelain']).strip():
        raise HarnessError('source checkout changed during storage conformance mutations')
    write_json(out / 'complete.json', {'head': head, 'exit': 0, 'mutants': len(rows),
                                      'scope': 'kernel conformance controls only; no runtime witness claim'})
    print(f'Detected {len(rows)} valid storage mutations through unchanged kernel assertions')


if __name__ == '__main__':
    main()
