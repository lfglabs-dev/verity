"""Targeted mutants for typed external `(Scalar, bytes memory)` interface calls
in forwarded tuple call trees (Refs #2803, Refs #2842).

Runs each mutant in an isolated source/cache snapshot and verifies that the
A/B/C differential campaign detects a real runtime divergence (a build failure
is invalid, never detection).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from solidity_differential.engine import HarnessError, write_json
from solidity_differential.mutations import release, snapshot

IMPORT = 'Compiler/SolidityImport/Import.lean'
MUTANTS = {
    'import-forwarded-bytes-tuple-drop-scalar-guard': (
        IMPORT,
        '  if let some g := abiDecodeScalarGuard? scalarTy enumBound? (.localVar scalarWord) then\n    pre := pre.push g',
        '  if let some _ := abiDecodeScalarGuard? scalarTy enumBound? (.localVar scalarWord) then\n    pre := pre',
    ),
    'import-forwarded-bytes-tuple-drop-revert-passthrough': (
        IMPORT,
        '    .ite (.eq (.localVar success) (.literal 0)) [.revertReturndata] [],\n    .letVar rdSize .returndataSize,',
        '    .ite (.eq (.localVar success) (.literal 0)) [.revertEmpty] [],\n    .letVar rdSize .returndataSize,',
    ),
}


def run_mutant(root: Path, name: str, output: Path):
    rel_file, anchor, replacement = MUTANTS[name]
    case_dir = output / name
    case_dir.mkdir(parents=True, exist_ok=True)
    snap = case_dir / 'snap'
    snapshot(snap)
    try:
        target = snap / rel_file
        text = target.read_text()
        if text.count(anchor) != 1:
            raise HarnessError(f'mutant {name}: anchor count {text.count(anchor)} != 1')
        target.write_text(text.replace(anchor, replacement, 1))
        build = subprocess.run(
            ['lake', 'build', 'Compiler.SolidityImport.Import',
             'Contracts.SolidityImportSmoke.ForwardedBytesTupleCallModel'],
            cwd=snap, text=True, capture_output=True, timeout=1800,
        )
        (case_dir / 'build.log').write_text(build.stdout + build.stderr)
        if build.returncode != 0:
            raise HarnessError(f'mutant {name} failed to build (invalid, not detected): {case_dir / "build.log"}')
        env = dict(os.environ)
        env['PYTHONPATH'] = str(snap / 'scripts')
        py = str(snap / '.lake/slice-testing-venv/bin/python')
        if not Path(py).exists():
            py = str(root / '.lake/slice-testing-venv/bin/python')
        diff_out = case_dir / 'diff'
        res = subprocess.run(
            [py, '-m', 'solidity_differential.check_forwarded_bytes_tuple_call',
             '--output', str(diff_out)],
            cwd=snap, env=env, text=True, capture_output=True, timeout=900,
        )
        (case_dir / 'diff.log').write_text(res.stdout + res.stderr)
        report_path = diff_out / 'campaign.json'
        if not report_path.exists():
            raise HarnessError(f'mutant {name}: missing campaign.json (tool failure, not detection): {case_dir / "diff.log"}')
        report = json.loads(report_path.read_text())
        if res.returncode == 0 or not report.get('divergences'):
            raise HarnessError(f'mutant {name} SURVIVED differential campaign!')
        print(f'KILLED mutant {name} ({len(report["divergences"])} divergences)')
        return {'mutant': name, 'killed': True, 'divergences': len(report['divergences'])}
    finally:
        release(snap)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--mutant', action='append', default=[])
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='forwarded-bytes-tuple-mut-', dir=root / '.lake')).resolve()
    names = args.mutant or list(MUTANTS.keys())
    results = [run_mutant(root, name, output) for name in names]
    write_json(output / 'summary.json', {'results': results})
    print(f'All {len(results)}/{len(results)} mutants killed.')


if __name__ == '__main__':
    main()
