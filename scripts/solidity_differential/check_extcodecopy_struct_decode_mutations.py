"""`<address>.code` and dynamic-struct `abi.decode` mutants in isolated source/cache snapshots.

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
DECODE = 'Compiler/SolidityImport/AbiMemoryDecode.lean'
DENOTE = 'Verity/Core/Model/Denote.lean'
ECM = 'Verity/Core/Model/ECM.lean'
# name: (file, anchor, replacement, kind, rejection case)
MUTANTS = {
    'import-code-copy-target': (IMPORT,
        'let copy := Stmt.ecm (Compiler.ECM.SolidityExtCodeCopy.module array) [target.expr]',
        'let copy := Stmt.ecm (Compiler.ECM.SolidityExtCodeCopy.module array) [.caller]',
        'runtime', None),
    'import-code-copy-length': (IMPORT,
        '.letVar length (.mload (.localVar array))],',
        '.letVar length (.sub (.mload (.localVar array)) (.literal 1))],', 'runtime', None),
    'import-struct-return-size': (IMPORT,
        'let returnSize ← atom { pre := #[], expr := buffer.size }',
        'let returnSize ← atom { pre := #[], expr := .sub buffer.size (.literal 32) }', 'runtime', None),
    'import-struct-return-pointer': (IMPORT,
        '#[.ecm Compiler.ECM.SolidityReturnMemory.module [pointer.expr, returnSize.expr],',
        '#[.ecm Compiler.ECM.SolidityReturnMemory.module'
        ' [.add pointer.expr (.literal 32), returnSize.expr],', 'runtime', None),
    'memory-decode-struct-head-size': (DECODE,
        'guard (.logicalNot (.slt (.sub dataEnd (.localVar head)) (.literal (32*schema.length)))) ]',
        'guard (.logicalNot (.slt (.sub dataEnd (.localVar head)) (.literal (32*schema.length - 32)))) ]',
        'runtime', None),
    'memory-decode-array-payload-bound': (DECODE,
        'guard (.logicalNot (.gt (.add data (.mul length (.literal (32*elementWords)))) dataEnd))',
        'guard (.logicalNot (.gt (.add data (.mul length (.literal (32*elementWords - 32)))) dataEnd))',
        'runtime', None),
    'memory-decode-scalar-bound': (DECODE,
        'if bound < 2^256 then [guard (.lt value (.literal bound))] else []',
        'if bound < 2^256 then [guard (.lt value (.literal (2 * bound)))] else []', 'runtime', None),
    'memory-decode-scalar-element': (DECODE,
        'scalarChecks kind value ++ [.mstore slot value]',
        'scalarChecks kind value ++ [.mstore slot (.add value (.literal 1))]', 'runtime', None),
    'memory-decode-struct-field-order': (DECODE,
        'scalarChecks kind value ++ [.mstore (.add (.localVar pointer) (.literal (32*i))) value]',
        'scalarChecks kind value ++ [.mstore (.add (.localVar pointer)'
        ' (.literal (32*(fields.length - 1 - i)))) value]', 'runtime', None),
    'memory-decode-member-offset': (DECODE,
        'let value := Expr.mload (.add (.localVar head) (.literal (32*i)))',
        'let value := Expr.mload (.add (.localVar head) (.literal (32*i + 32)))', 'runtime', None),
    'denote-code-copy-target': (DENOTE,
        'DenoteExternalCode.accountCode state.world (Verity.Core.Address.ofNat account)',
        'DenoteExternalCode.accountCode state.world (Verity.Core.Address.ofNat (account + 1))',
        'runtime', None),
    'denote-code-copy-bytes': (DENOTE,
        ').copyPhysicalMemory (rawPhysicalByte code) (pointer + 32) 0 code.length',
        ').copyPhysicalMemory (rawPhysicalByte code) (pointer + 32) 1 code.length', 'runtime', None),
    'denote-code-copy-length': (DENOTE,
        ').writePhysicalMemoryValue pointer (Verity.Core.Uint256.ofNat code.length)',
        ').writePhysicalMemoryValue pointer (Verity.Core.Uint256.ofNat (code.length + 32))',
        'runtime', None),
    'denote-code-copy-free-pointer': (DENOTE,
        'let world := ((state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat next)',
        'let world := ((state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat pointer)',
        'runtime', None),
    'denote-memory-return-words': (DENOTE,
        '(DenoteMemory.wordValue (state.world.byteMemory.readWord (offset + 32 * index))).val',
        '(DenoteMemory.wordValue (state.world.byteMemory.readWord (offset + 32 * index + 32))).val',
        'runtime', None),
    'ecm-code-copy-offset': (ECM,
        '.exprStmt (.call "extcodecopy" [target, .call "add" [pointer, .lit 32], .lit 0, size])',
        '.exprStmt (.call "extcodecopy" [target, .call "add" [pointer, .lit 32], .lit 1, size])',
        'runtime', None),
    'ecm-code-copy-free-pointer': (ECM,
        '.exprStmt (.call "mstore" [.lit 64, next]),\n      .exprStmt (.call "mstore" [pointer, size]),',
        '.exprStmt (.call "mstore" [pointer, size]),', 'runtime', None),
    'import-code-copy-this-guard': (IMPORT,
        'if (← isThisAddressConv account) then\n    failAt code "code of the executing contract is unsupported"',
        'if false then\n    failAt code "code of the executing contract is unsupported"',
        'admission', 'this-code'),
    'import-struct-decode-calldata-guard': (IMPORT,
        'if decodesDynamicStruct && fromCalldata then',
        'if false then', 'admission', 'calldata-source'),
    'import-struct-decode-member-guard': (IMPORT,
        'if schema.all AbiMemoryDecode.supportedMember && schema.any AbiSchema.isDynamicMember then\n'
        '          let members',
        'if schema.any AbiSchema.isDynamicMember then\n          let members',
        'admission', 'bytes-member'),
    'import-struct-return-named-guard': (IMPORT,
        'unless (← mStr (← mField r "name")) == "" do\n    failAt r "named dynamic struct return',
        'unless true do\n    failAt r "named dynamic struct return', 'admission', 'named-return'),
    'import-struct-return-calldata-guard': (IMPORT,
        'unless mem.structId == retSid && mem.schema.isSome && !mem.calldataLocation do',
        'unless mem.structId == retSid && mem.schema.isSome do', 'admission', 'calldata-return'),
}


def environment(directory):
    env = dict(os.environ)
    env['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + env.get('PYTHONPATH', '')
    return env


def runtime(directory, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_extcodecopy_struct_decode', '--single',
            '--transactions', '81', '--seed', '2545', '--shrink-attempts', '40', '--output', str(output)]
    result = subprocess.run(argv, cwd=directory, env=environment(directory), text=True,
                            capture_output=True, timeout=10800)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'no differential report; tool failure is not detection: {output.with_suffix(".log")}')
    return result.returncode, json.loads(report_path.read_text())


def rejection(directory, case, output):
    argv = [sys.executable, '-m', 'solidity_differential.check_extcodecopy_struct_decode_rejections',
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
              Path(tempfile.mkdtemp(prefix='extcodecopy-struct-decode-mutations-', dir='.lake')).resolve())
    result = mutation_campaign(output, selected)
    write_json(output / 'complete.json', {'exit': 0, 'selected': selected or list(MUTANTS),
                                          'results': result['mutants']})
    print(output)


if __name__ == '__main__':
    main()
