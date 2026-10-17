"""Actual scalar storage importer mutations, with unmodified controls and reduced witnesses."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import snapshot

MUTANTS = {
    'import-void-fallthrough': ('out := out.push .stop', 'out := out.push (.require (.literal 0) "mutated void return") |>.push .stop'),
    'denote-scalar-sibling-mask': ('let cleared := Verity.Core.Uint256.and current (Verity.Core.Uint256.not shiftedMaskNat)', 'let cleared := Verity.Core.Uint256.and current 0'),
    'import-scalar-read': ('pure { pre, expr := .storage name }', 'pure { pre, expr := .literal 0 }'),
    'import-scalar-slot': ('slot := some slot, packedBits }', 'slot := some (slot + 1), packedBits }'),
    'import-scalar-offset': ('some { offset, width }', 'some { offset := if width == 128 then 128 - offset else offset, width }'),
    'import-scalar-write': ('(.setStorage name value.expr)', '(.setStorage name (.literal 0))'),
    'import-scalar-delete': ('if deleting then pure ({ pre := #[], expr := .literal 0 } : Val)', 'if deleting then pure ({ pre := #[], expr := .literal 1 } : Val)'),
}

MUTANTS.update({'import-mapping-layout': ('if width == 256 then none else some { offset := 0, width }',
                           'if width == 256 then none else some { offset := 1, width }'),
 'import-mapping-read-one': ('Expr.structMember field key "__solidity_value"',
                             'Expr.structMember field (.literal 0) "__solidity_value"'),
 'import-mapping-read-two': ('Expr.structMember2 field key1 key2 "__solidity_value"',
                             'Expr.structMember2 field key2 key1 "__solidity_value"'),
 'import-mapping-write-one': ('Stmt.setStructMember field key "__solidity_value" value',
                              'Stmt.setStructMember field key "__solidity_value" (.literal 0)'),
 'import-mapping-write-two': ('Stmt.setStructMember2 field key1 key2 "__solidity_value" value',
                              'Stmt.setStructMember2 field key2 key1 "__solidity_value" value'),
 'import-mapping-delete': ('expr := (.literal 0 : Expr)', 'expr := (.literal 1 : Expr)'),
 'import-mapping-bool-literal': ('| "true" => pure 1', '| "true" => pure 0'),
 'import-mapping-bool-read': ('Expr.logicalNot (.logicalNot read)', 'Expr.logicalNot read')})


MUTANTS.update({
    'import-logical-and-branch': ('then Stmt.ite a.expr rhs.toList []', 'then Stmt.ite a.expr [] rhs.toList'),
    'import-logical-or-branch': ('else Stmt.ite a.expr [] rhs.toList', 'else Stmt.ite a.expr rhs.toList []'),
    'import-logical-initial-value': ('a.pre.push (.letVar dest a.expr)', 'a.pre.push (.letVar dest (.logicalNot a.expr))'),
})


MUTANTS.update({
    'import-event-converted-binding': ('value := { pre := value.pre.push (.letVar binding value.expr), expr := .localVar binding }', 'value := { pre := value.pre.push (.letVar binding (.literal 0)), expr := .localVar binding }'),
    'import-event-indexed': ('kind := if indexed then .indexed else .unindexed', 'kind := .unindexed'),
    'import-event-drop': ('pure (pre.push (.emit name values))', 'pure pre'),
    'import-event-values': ('pure (pre.push (.emit name values))', 'pure (pre.push (.emit name (values.map (fun _ => .literal 0))))'),
    'import-event-signature': ('failAt declaration "anonymous events are unsupported"\n  let name ← mStr (← mField declaration "name")',
        'failAt declaration "anonymous events are unsupported"\n  let originalName ← mStr (← mField declaration "name")\n  let name := originalName ++ "Mutated"'),
    'observe-event-word': ('| .uint256 | .bytes32 => pure (value % 2^256)', '| .uint256 | .bytes32 => pure 0'),
    'observe-event-narrow': ('pure (value % 2^bits)', 'pure 0'),
    'observe-event-address': ('| .address => pure (value % 2^160)', '| .address => pure 0'),
    'observe-event-bool': ('| .bool => pure (if value == 0 then 0 else 1)', '| .bool => pure (if value == 0 then 1 else 0)'),
})


MUTANTS.update({
    'import-if-root-swap': ('.push (.ite condition.expr yesOut.toList noOut.toList)',
                            '.push (.ite condition.expr noOut.toList yesOut.toList)'),
    'import-if-root-else-drop': ('let (noOut, noReturned) ← lowerRootStatements no',
                                 'let (noOut, noReturned) ← lowerRootStatements #[]'),
    'import-if-helper-swap': ('let branch := Stmt.ite condition.expr (assign yesPre yesResult).toList\n            (assign noPre noResult).toList',
                              'let branch := Stmt.ite condition.expr (assign noPre noResult).toList\n            (assign yesPre yesResult).toList'),
    'import-if-helper-guard-swap': ('(.ite condition.expr yesPre.toList noPre.toList) ++ tail',
                                    '(.ite condition.expr noPre.toList yesPre.toList) ++ tail'),
})


MUTANTS.update({
    'import-const-identifier': ('pure (.expr (← lowerConstant decl j))', 'pure (.expr { pre := #[], expr := .literal 0 })'),
    'import-const-declared': ('return { pre := #[], expr := .literal n }', 'return { pre := #[], expr := .literal (n + 1) }'),
    'import-const-folded': ('return { pre := #[], expr := .literal folded }', 'return { pre := #[], expr := .literal (folded / 2) }'),
    'import-const-conversion': ('convert declTy valueTy (← lowerExpr value) use', 'pure { pre := #[], expr := .literal 1 }'),
})


MUTANTS.update({
    'import-arith-mod-op': ('| "%" => checkedDiv .mod left right', '| "%" => checkedDiv .div left right'),
    'import-arith-div-guard': ('let ite := iteStmt (.eq b.expr (.literal 0)) divPanic ok', 'let ite := ok'),
    'import-arith-compound-sub': ('| "-=" => pure (some "-")', '| "-=" => pure (some "+")'),
    'import-arith-compound-old': ('| some op => checkedArith op targetTy { pre := #[], expr := old }',
                                  '| some op => checkedArith op targetTy { pre := #[], expr := .literal 0 }'),
    'import-arith-increment': ('| "++" => pure (some "+")', '| "++" => pure none'),
    'import-arith-order': ('return (rhs.pre ++ pre ++ value.pre).push (write expr)',
                           'return (pre ++ rhs.pre ++ value.pre).push (write expr)'),
})


MUTANTS.update({
    'import-member-write-one': ('fun (value : Expr) => Stmt.setStructMember field key member value)',
                                'fun (_ : Expr) => Stmt.setStructMember field key member (.literal 0))'),
    'import-member-write-two': ('fun (value : Expr) => Stmt.setStructMember2 field key1 key2 member value)',
                                'fun (_ : Expr) => Stmt.setStructMember2 field key1 key2 member (.literal 0))'),
    'import-member-write-old': ('| .one field key => pure (field, Expr.structMember field key member,',
                                '| .one field key => pure (field, Expr.literal 0,'),
    'import-member-write-order': ('return (rhs.pre ++ pre ++ value.pre).push (write value.expr)',
                                  'return (pre ++ rhs.pre ++ value.pre).push (write value.expr)'),
})


MUTANTS.update({
    'import-loop-count': ('out := out.push (.forEach binding bound.expr bodyOut.toList)',
                          'out := out.push (.forEach binding (.literal 0) bodyOut.toList)'),
    'import-loop-counter': ('{ e with values := e.values.insert counter (.localVar binding),',
                            '{ e with values := e.values.insert counter (.literal 0),'),
    'import-local-assign': ('return (rhs.pre ++ value.pre).push (.assignVar binding value.expr)',
                            'return rhs.pre ++ value.pre'),
    'import-local-old': ('let value ← update rhs (.localVar binding)', 'let value ← update rhs (.literal 0)'),
    'import-local-zero': ('          pure { pre := #[], expr := .literal 0 }',
                          '          pure { pre := #[], expr := .literal 1 }'),
    'import-local-alias': ('if (← get).mutables.toList.any (·.2 == b) then', 'if false then'),
})


MUTANTS.update({
    'import-unchecked-wrap': ('if bits == 256 then raw else .bitAnd raw (.literal (2 ^ bits - 1))', 'raw'),
    'import-unchecked-root': ('if (← mKind s) == "UncheckedBlock" then modify fun e => { e with unchecked := true }',
                              'if (← mKind s) == "UncheckedBlock" then pure ()'),
    'import-unchecked-helper': ('currentFile := frameFile, unchecked := false }', 'currentFile := frameFile }'),
    'import-unchecked-helper-block': ('        modify fun e => { e with unchecked := true }\n        if ← helperListReturns inner then',
                                      '        if ← helperListReturns inner then'),
    'import-unchecked-end': ('    | "VerityUncheckedEnd" =>\n        modify fun e => { e with unchecked := false }\n',
                             '    | "VerityUncheckedEnd" =>\n'),
})


MUTANTS.update({
    'import-tuple-order': ('        pre := pre ++ v.pre\n        values := values.push v.expr',
                           '        pre := v.pre ++ pre\n        values := values.push v.expr'),
    'import-tuple-skip': ('let some value := values[i]? | failAt d "missing tuple component"',
                          'let some value := values[decls.size - 1 - i]? | failAt d "missing tuple component"'),
    'import-tuple-branch': ('let ite := Stmt.ite cond.expr (assign yesPre yes) (assign noPre no)',
                            'let ite := Stmt.ite cond.expr (assign noPre no) (assign yesPre yes)'),
    'import-tuple-lazy': ('(assign yesPre yes) (assign noPre no)\n      pure (cond.pre ++ dests.map',
                          '(assign yesPre yes) (assign #[] no)\n      pure (cond.pre ++ noPre ++ dests.map'),
    'import-tuple-helper-if': ('| some exprs => pre ++ (dests.zip exprs).map', '| some exprs => pre ++ (dests.zip exprs.reverse).map'),
    'import-tuple-return': ('out := out ++ pre |>.push (.returnValues values.toList)',
                            'out := out ++ pre |>.push (.returnValues values.reverse.toList)'),
})


def run(directory, output, name):
    fixture = "StorageVoidSequence" if name == "import-void-fallthrough" else "StorageSequence"
    if name.startswith("import-mapping-"):
        fixture = "MappingSequence"
    if name.startswith("import-logical-"):
        fixture = "ShortCircuitSequence"
    if name.startswith('import-if-'):
        fixture = 'IfElseSequence'
    if name.startswith('import-const-'):
        fixture = 'ConstantSequence'
    if name.startswith('import-arith-'):
        fixture = 'ArithmeticSequence'
    if name.startswith('import-member-'):
        fixture = 'MemberWriteSequence'
    if name.startswith(('import-loop-', 'import-local-')):
        fixture = 'LoopSequence'
    if name.startswith('import-unchecked-'):
        fixture = 'UncheckedSequence'
    if name.startswith('import-tuple-'):
        fixture = 'TupleSequence'
    if name.startswith(('import-event-', 'observe-event-')):
        fixture = 'NarrowEventSequence' if name == 'observe-event-narrow' else 'ImportedEventSequence'
    argv = [sys.executable, '-m', 'solidity_differential.check_stateful',
            '--model-driver', f'Contracts/SolidityImportSmoke/{fixture}Model.lean',
            '--source-fixture', f'Contracts/SolidityImportSmoke/{fixture}.sol',
            '--argument-bits', '128' if fixture == 'NarrowEventSequence' else '256',
            '--transactions', '3', '--seed', '2453', '--shrink-attempts', '30',
            '--output', str(output)]
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts') + os.pathsep + environment.get('PYTHONPATH', '')
    result = subprocess.run(argv, cwd=directory, env=environment,
                            text=True, capture_output=True, timeout=600)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    report_path = output / 'campaign.json'
    if not report_path.exists():
        raise HarnessError(f'{name}: no differential report; tool failure is not mutation detection; see {output.with_suffix(".log")}')
    report = json.loads(report_path.read_text())
    return result.returncode, report


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        before, after = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        baseline_code, baseline = run(directory, directory / '.lake/baseline', name)
        if baseline_code or not baseline['transactions'] or baseline['divergences']:
            raise HarnessError(f'{name}: unmodified positive control failed')
        source = directory / ('Compiler/SolidityImport/SequenceRunner.lean' if name.startswith('observe-event-')
                              else 'Verity/Core/Model/Denote.lean' if name.startswith('denote-')
                              else 'Compiler/SolidityImport/Import.lean')
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import', 'Compiler.SolidityImport.SequenceRunner'], cwd=directory,
                timeout=600, log=directory / 'build.log')
        campaign = directory / '.lake/mutated'
        code, result = run(directory, campaign, name)
        if code == 0 or not result['divergences']:
            raise HarnessError(f'{name}: mutation survived')
        reduced = json.loads((campaign / 'reduced.json').read_text())
        if not reduced['deletion_minimal'] or not reduced['transactions'] or not reduced['signature']:
            raise HarnessError(f'{name}: unexpected or unreproduced minimal witness: {reduced}')
        reports.append({'mutant': name, 'status': 'detected', 'detected': True, 'baselinePassed': True,
                        'witness': reduced, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    output = Path(tempfile.mkdtemp(prefix='storage-mutations-', dir='.lake')).resolve()
    mutation_campaign(output)
    print(output)


if __name__ == '__main__':
    main()
