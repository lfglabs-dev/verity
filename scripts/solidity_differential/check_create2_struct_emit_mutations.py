"""CREATE2 code-storage and struct-event mutants in isolated source/cache snapshots.

Runtime mutants must survive an unmodified positive control and then produce an
A/B/C divergence with a reproduced deletion-minimal witness. Admission-guard
mutants must turn a pinned located rejection into a failure of the exact
near-miss check. A mutant that fails to build is invalid, never detected.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import release, snapshot

IMPORT = 'Compiler/SolidityImport/Import.lean'
DENOTE = 'Verity/Core/Model/Denote.lean'
# name: (file, anchor, replacement, kind, rejection case)
MUTANTS = {
    'import-create2-salt': (IMPORT,
        '[.literal 0, pointer.expr, size.expr, salt.expr]',
        '[.literal 0, pointer.expr, size.expr, .literal 0]', 'runtime', None),
    'import-create2-size': (IMPORT,
        '[.literal 0, pointer.expr, size.expr, salt.expr]',
        '[.literal 0, pointer.expr, .sub size.expr (.literal 1), salt.expr]', 'runtime', None),
    'import-create2-result': (IMPORT,
        'expr := .bitAnd (.localVar result) (.literal (2 ^ 160 - 1)) }',
        'expr := .bitAnd (.localVar result) (.literal (2 ^ 152 - 1)) }', 'runtime', None),
    'import-struct-emit-selector': (IMPORT,
        'let mut topics : Array Expr := #[.literal (digits.foldl (fun word d => word * 16 + d) 0)]',
        'let mut topics : Array Expr := #[.literal (digits.foldl (fun word d => word * 16 + d) 0 + 1)]',
        'runtime', None),
    'import-struct-emit-payload': (IMPORT,
        'let size ← atom { pre := #[], expr := payload.size }',
        'let size ← atom { pre := #[], expr := .sub payload.size (.literal 32) }', 'runtime', None),
    'import-struct-emit-topic-order': (IMPORT,
        '(topics.toList ++ [pointer.expr, size.expr])',
        '(topics.toList.take 1 ++ (topics.toList.drop 1).reverse ++ [pointer.expr, size.expr])',
        'runtime', None),
    'denote-create2-initcode-size': (DENOTE,
        '(.ofNat salt) (.ofNat offset) (.ofNat size)',
        '(.ofNat salt) (.ofNat offset) (.ofNat (size - 1))', 'runtime', None),
    'denote-create2-address': (DENOTE,
        '| .success address => address.val',
        '| .success address => address.val + 1', 'runtime', None),
    'denote-create2-commit': (DENOTE,
        'world := result.world.installPhysicalMemory result.memory',
        'world := state.world', 'runtime', None),
    'denote-log-payload': (DENOTE,
        'DenoteMemory.wordValue (memory.readWord (offset + 32 * index))',
        'DenoteMemory.wordValue (memory.readWord (offset + 32 * index + 1))', 'runtime', None),
    'import-create2-value-guard': (IMPORT,
        'unless (← yulNumber? args[0]!) == some 0 do',
        'unless true do', 'admission', 'nonzero-value'),
    'import-create2-template-guard': (IMPORT,
        'unless (← get).initcodeTemplates.contains declId do',
        'unless true do', 'admission', 'unchecked-template'),
    'import-create2-size-guard': (IMPORT,
        'unless ← yulBytesLength? args[2]! declId do',
        'unless true do', 'admission', 'short-size'),
    'import-struct-emit-indexed-guard': (IMPORT,
        'unless (Denote.errorScalarType modelType).isSome && !ty.startsWith "enum " do',
        'unless true do', 'admission', 'indexed-bytes4'),
}


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_create2_struct_emit', '--single',
            '--transactions', '24', '--seed', '2520', '--shrink-attempts', '40', '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'no differential report; tool failure is not detection: {output.with_suffix(".log")}')
    return result.returncode, json.loads(report_path.read_text())


def rejection(directory, case, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_create2_struct_emit_rejections',
            '--only', case, '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=1800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    return result.returncode, result.stdout + result.stderr


def mutation_campaign(output, selected=None):
    root = Path.cwd()
    for name in selected or MUTANTS:
        relative, before, _, _, _ = MUTANTS[name]
        if (root / relative).read_text().count(before) != 1:
            raise HarnessError(f'{name}: mutation anchor must occur exactly once in {relative}')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        relative, before, after, kind, case = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        try:
            modules = ['Compiler.SolidityImport.Import', 'Compiler.SolidityImport.Differential',
                       'Compiler.SolidityImport.SequenceRunner', 'Compiler.Codegen', 'Compiler.Yul.PrettyPrint']
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'baseline-build.log')
            if kind == 'runtime':
                code, baseline = runtime(directory, directory / '.lake/baseline')
                if code or baseline['divergences'] or not baseline['transactions']:
                    raise HarnessError(f'{name}: unmodified positive control failed')
            else:
                code, log = rejection(directory, case, directory / '.lake/baseline-rejection')
                if code:
                    raise HarnessError(f'{name}: unmodified located rejection failed\n{log[-2000:]}')
            source = directory / relative
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError(f'{name}: nonunique mutation anchor')
            source.write_text(text.replace(before, after))
            command(['lake', 'build', *modules], cwd=directory, timeout=3600, log=directory / 'build.log')
            if kind == 'runtime':
                campaign = directory / '.lake/mutated'
                code, report = runtime(directory, campaign)
                if code == 0 or not report['divergences']:
                    raise HarnessError(f'{name}: mutation survived')
                reduced = json.loads((campaign / 'reduced.json').read_text())
                if not reduced['deletion_minimal'] or not reduced['transactions'] or not reduced['signature']:
                    raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
                entry = {'witness': reduced, 'campaign': str(campaign)}
            else:
                code, log = rejection(directory, case, directory / '.lake/mutated-rejection')
                if code == 0 or f'{case}: expected exact located rejection' not in log:
                    raise HarnessError(f'{name}: guard removal escaped the {case} near-miss check')
                entry = {'kind': 'unsupported-admission', 'case': case}
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True,
                        'baselinePassed': True, 'path': relative, **entry})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    selected = None
    if args.only:
        selected = [name for name in MUTANTS if args.only == name]
        if not selected:
            raise HarnessError(f'no mutants matched --only {args.only}')
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='create2-struct-emit-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
