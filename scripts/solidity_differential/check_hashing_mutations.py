"""Semantic ABI/packed encoding mutants with positive controls and minimal witnesses."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot

IMPORT = 'Compiler/SolidityImport/Import.lean'
ENCODING = 'Compiler/SolidityImport/AbiEncoding.lean'
MUTANTS = {
    'hash-word-stride': (ENCODING, '.literal (32 * index)', '.literal (64 * index)', [1]),
    'hash-root-offset': (IMPORT, 'pre := pre.push (.mstore base (.literal 32))',
                         'pre := pre.push (.mstore base (.literal 64))', [16]),
    'hash-root-field': (IMPORT, 'pre := pre.push (.mstore destination value.expr)',
                        'pre := pre.push (.mstore destination (.literal 0))', [16]),
    'hash-static-root-field': (IMPORT, 'values := values ++ [value.expr]\n    unless values.length',
                               'values := values ++ [.literal 0]\n    unless values.length', [50]),
    'hash-array-length': (IMPORT, '.mstore (.localVar tail) (.localVar length)',
                          '.mstore (.localVar tail) (.literal 0)', [38]),
    'hash-array-destination-stride': (IMPORT,
        '(.mul (.localVar index) (.literal (32 * kinds.length)))\n          body := body',
        '(.mul (.localVar index) (.literal (32 * (kinds.length + 1))))\n          body := body', [38]),
    'hash-literal-value': (IMPORT, 'word := word * 16 + digit', 'word := word * 16 + (digit + 1)', [90]),
    'hash-literal-length': (IMPORT, 'size := .literal (hex.length / 2)',
                           'size := .literal (hex.length / 2 + 1)', [90]),
    'hash-packed-address-width': (IMPORT, 'let size := if ty == "bool" then 1 else',
                                 'let size := if ty == "address" then 21 else if ty == "bool" then 1 else', [69]),
    'hash-packed-scalar-value': (IMPORT, 'AbiEncoding.staticWords pointer finish [padded]',
                                 'AbiEncoding.staticWords pointer finish [.literal 0]', [69]),
    'hash-copy-byte-shift': (ENCODING, '.shr (shift index) sourceWord',
                            '.shr (.add (shift index) (.literal 8)) sourceWord', [90]),
    'hash-copy-zero-fill': (ENCODING, '(.literal 0)]]', '(.literal 1)]]', [90]),
    'hash-buffer-identity': (IMPORT, 'AbiEncoding.copyBytes buffer.pointer (.localVar pointer)',
                             'AbiEncoding.copyBytes (.localVar pointer) (.localVar pointer)', [90]),
    'hash-keccak-length': (IMPORT, '.keccak256 bytes.pointer bytes.size',
                           '.keccak256 bytes.pointer (.add bytes.size (.literal 1))', [1]),
    'hash-hex-number': (IMPORT, 'expr := .literal n }\n  | "TupleExpression"',
                         'expr := .literal (if raw.startsWith "0x" then n + 1 else n) }\n  | "TupleExpression"', [72]),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutant', choices=sorted(MUTANTS), action='append')
    args = parser.parse_args()
    output = args.output.resolve()
    directory = output / 'snapshot'
    snapshot(directory)
    env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))
    results = []
    for name in args.mutant or list(MUTANTS):
        filename, anchor, replacement, indices = MUTANTS[name]
        source = directory / filename
        original = source.read_text()
        if original.count(anchor) != 1:
            raise HarnessError(f'{name}: mutation anchor must be unique, found {original.count(anchor)}')
        record = output / name
        record.mkdir()

        def run(label):
            target = record / label
            argv = [sys.executable, '-m', 'solidity_differential.check_abi_hashing',
                    '--repo', str(directory), '--output', str(target)]
            for index in indices:
                argv += ['--case-index', str(index)]
            result = subprocess.run(argv, cwd=directory, env=env, capture_output=True,
                                    text=True, timeout=1200)
            (record / (label + '.log')).write_text(result.stdout + result.stderr)
            return result.returncode, target

        code, baseline = run('baseline')
        if code or not (baseline / 'complete.json').is_file():
            raise HarnessError(f'{name}: positive control failed')
        source.write_text(original.replace(anchor, replacement))
        command(['lake', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.Differential'],
                cwd=directory, timeout=600, log=record / 'build.log')
        code, campaign = run('mutated')
        if not (campaign / 'campaign.json').is_file():
            raise HarnessError(f'{name}: tool failure is not detection')
        report = json.loads((campaign / 'campaign.json').read_text())
        if code == 0 or not report['divergences']:
            raise HarnessError(f'{name}: mutation survived')
        witness = json.loads((campaign / 'reduced.json').read_text())
        if not witness['deletion_minimal'] or not witness['transactions']:
            raise HarnessError(f'{name}: missing minimal reproduced runtime witness')
        results.append({'mutant': name, 'detected': True, 'baselinePassed': True,
                        'indices': indices, 'witness': witness})
        write_json(record / 'complete.json', results[-1])
        write_json(output / 'results.json', results)
        source.write_text(original)
        command(['lake', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.Differential'],
                cwd=directory, timeout=600, log=record / 'restore.log')
        print(f'{name}: detected with positive control and reproduced minimal witness', flush=True)
    write_json(output / 'complete.json', {'exit': 0, 'results': results})


if __name__ == '__main__':
    main()
