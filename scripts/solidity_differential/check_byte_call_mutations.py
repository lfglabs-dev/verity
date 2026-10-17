"""Executable mutations of the canonical byte-call boundary (development gate).

Every mutant must compile, and must reach its specific semantic assertion.
Import admission and the full mutation-suite registration remain separate work.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import tempfile

DOMAIN_TEST = 'test/ByteExternalCall/OracleRequestDomain.lean'
DOMAIN_ARGS = ['1000', '119', '2', '99', '900', '256']

MUTANTS = {
    'request-domain': ('let observed ← ByteExternalCall.executeChecked adversary preparation.request prepared.world',
                       'let observed := ByteExternalCall.execute adversary preparation.request prepared.world',
                       'unmodeled mock target fabricated an EVM response'),
    'selector-shift': ('selector * 2^224', 'selector * 2^216', 'unaligned ABI scratch encoding differs'),
    'argument-offset': ('pointer + 4 + index * 32', 'pointer + 5 + index * 32', 'unaligned ABI scratch encoding differs'),
    'short-success': ('observed.returndata.length < 32', 'observed.returndata.length < 1', 'short success must revert empty'),
    'truncate-buffer': ('rawReturndata := some observed.returndata', 'rawReturndata := some (observed.returndata.take 32)', 'oversized response buffer truncated'),
    'drop-cancelled-access': ('return (.revertWithData observed.returndata, observed.touched)', 'return (.revertWithData observed.returndata, [])', 'cancelled foreign access lost'),
    'raw-copy-offset': ('(rawPhysicalByte bytes) dst src sz', '(rawPhysicalByte bytes) dst (src + 1) sz', 'unaligned raw copy differs'),
    'empty-revert': ('| _, .revertEmpty => .revertWithData []',
                     '| state, .revertEmpty => .revertWithData (state.rawReturndata.getD [])',
                     'empty revert propagated stale return bytes'),
}
MODULES = ['Verity/Core/Model/Denote', 'Compiler/SolidityImport/Transactions',
           'Compiler/SolidityImport/TransactionAccess', 'Verity/Core/Model/DenoteByteExternalCalls',
           'Compiler/SolidityImport/StaticOracleMocks']
TEST = 'test/ByteExternalCall/CanonicalBoundaryChecks.lean'


def run(command, root, env, log):
    result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True, timeout=180)
    log.write_text(result.stdout + result.stderr)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mutant', choices=tuple(MUTANTS), action='append')
    args = parser.parse_args()
    selected = args.mutant or list(MUTANTS)
    root = Path.cwd()
    lean_path = os.environ.get('LEAN_PATH')
    if not lean_path:
        lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    env = dict(os.environ, LEAN_PATH=lean_path, LEAN_NUM_THREADS='1')
    output = Path(tempfile.mkdtemp(prefix='canonical-byte-mutations-', dir=root / '.lake'))
    for test, message in [(TEST, 'canonical byte-call boundary checks passed'),
                          ('test/ByteExternalCall/EmptyRevert.lean', 'empty revert boundary checks passed'),
                          (DOMAIN_TEST, 'oracle request domain checks passed')]:
        baseline = run(['lean', '-j', '1', '-M', '4096', '--run', test] +
                       (DOMAIN_ARGS if test == DOMAIN_TEST else []), root, env,
                       output / (Path(test).stem + '-baseline.log'))
        if baseline.returncode or message not in baseline.stdout:
            raise RuntimeError('unmodified boundary fixture did not pass: ' + test)
    source = (root / 'Verity/Core/Model/Denote.lean').read_text()
    results = []
    for name in selected:
        old, new, message = MUTANTS[name]
        if source.count(old) != 1:
            raise RuntimeError(f'{name}: anchor must occur exactly once')
        case = output / name
        source_root = case / 'sources'
        lib = case / 'lib'
        # Lean resolves namespace roots before individual object files. Give
        # each mutant a complete private link tree; changed outputs are unlinked.
        for cached in (root / '.lake/build/lib/lean').rglob('*'):
            target = lib / cached.relative_to(root / '.lake/build/lib/lean')
            if cached.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            elif not target.exists() and not target.is_symlink():
                target.symlink_to(cached.resolve())
        mutant_env = dict(env, LEAN_PATH=str(lib) + ':' + lean_path)
        for module in MODULES:
            path = source_root / (module + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source.replace(old, new) if module == MODULES[0]
                            else (root / (module + '.lean')).read_text())
            target = lib / (module + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.is_symlink():
                target.unlink()
            build = run(['lean', '-j', '1', '--root=' + str(source_root), str(path), '-o', str(target)],
                        root, mutant_env, case / (module.replace('/', '-') + '.log'))
            if build.returncode:
                raise RuntimeError(f'{name}: mutant failed to compile; not detected')
        test_file = (DOMAIN_TEST if name == 'request-domain' else
                     'test/ByteExternalCall/EmptyRevert.lean' if name == 'empty-revert' else TEST)
        test = run(['lean', '-j', '1', '-M', '4096', '--run', test_file] +
                   (DOMAIN_ARGS if test_file == DOMAIN_TEST else []), root, mutant_env, case / 'test.log')
        if test.returncode == 0 or message not in test.stdout + test.stderr:
            raise RuntimeError(f'{name}: expected semantic assertion did not detect mutant')
        results.append(dict(mutant=name, compiled=True, detected=True, assertion=message))
        (output / 'report.json').write_text(json.dumps(dict(
            scope='canonical boundary executable assertions, not whole importer differential gate',
            baseline_passed=True, results=results,
            selected=selected, full_inventory=len(selected) == len(MUTANTS),
            source_sha256=hashlib.sha256(source.encode()).hexdigest()), indent=2))
        print(name, 'detected', flush=True)
    print('all canonical byte-call mutations detected:', output, flush=True)


if __name__ == '__main__':
    main()
