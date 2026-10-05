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

MUTANTS.update({'import-numeric-separators': ('let raw := raw.replace "_" ""', 'let raw := raw.replace "_" "0"'),
 'import-numeric-leading-dot': ('if whole.isEmpty then some 0 else whole.toNat?', 'if whole.isEmpty then some 1 else whole.toNat?'),
 'import-numeric-decimal-scale': ('let scale := 10 ^ fraction.length',
                                  'let scale := 10 ^ (fraction.length + 1)'),
 'import-numeric-positive-exponent': ('numerator * 10 ^ exponent, denominator',
                                      'numerator * 10 ^ (exponent + 1), denominator'),
 'import-numeric-negative-exponent': ('denominator * 10 ^ exponent',
                                      'denominator * 10 ^ (exponent - 1)'),
 'import-numeric-hex-value': ('then return (n, 1)', 'then return (n + 1, 1)'),
 'import-numeric-integral-value': ('let n := scaled / denominator',
                                   'let n := scaled / denominator + 1'),
 'import-numeric-unit-minutes': ('| "minutes" => some 60', '| "minutes" => some (60 + 1)'),
 'import-numeric-unit-hours': ('| "hours" => some 3600', '| "hours" => some (3600 + 2)'),
 'import-numeric-unit-days': ('| "days" => some 86400', '| "days" => some (86400 + 4)'),
 'import-numeric-unit-weeks': ('| "weeks" => some 604800', '| "weeks" => some (604800 + 1)'),
 'import-numeric-unit-gwei': ('| "gwei" => some (10 ^ 9)', '| "gwei" => some ((10 ^ 9) + 1)'),
 'import-numeric-unit-ether': ('| "ether" => some (10 ^ 18)', '| "ether" => some ((10 ^ 18) + 1000)'),
 'import-numeric-unit-one': ('| "seconds" | "wei" => some 1', '| "seconds" | "wei" => some 2')})

MUTANTS.update({'import-numeric-constant-product': ('let product := a * b', 'let product := a * b + 1')})

MUTANTS.update({'import-numeric-constant-sum': ('let sum := a + b', 'let sum := a + b + 1')})

MUTANTS.update({'import-numeric-constant-value': ('pure (.expr value)',
                                   'pure (.expr { value with expr := .literal 0 })')})

MUTANTS.update({
    'import-constant-array-element': ('constants := constants.push n', 'constants := constants.push (n + 1)'),
    'import-constant-array-selection': ('(.eq key.expr (.literal index))', '(.eq key.expr (.literal (index + 1)))'),
    'import-constant-array-bound': ('(.lt key.expr (.literal constants.size))', '(.lt key.expr (.literal (constants.size + 1)))'),
})


MUTANTS.update({
    'import-modulo-value': ('Stmt.assignVar dest (.mod a.expr b.expr)', 'Stmt.assignVar dest (.div a.expr b.expr)'),
    'import-modulo-zero': ('iteStmt (.eq b.expr (.literal 0)) divPanic moduloResult', 'iteStmt (.eq b.expr (.literal 1)) divPanic moduloResult'),
})


MUTANTS.update({'import-local-write-value': ('return value.pre.push (.assignVar binding value.expr)', 'return value.pre.push (.assignVar binding (.literal 0))')})

MUTANTS.update({'import-default-local-zero': ('return #[.letVar binding (.literal 0)]', 'return #[.letVar binding (.literal 1)]')})

MUTANTS.update({'import-modulo-quote': ('| .mod a b => do `(Compiler.CompilationModel.Expr.mod $(← quoteExpr a) $(← quoteExpr b))', '| .mod a b => do `(Compiler.CompilationModel.Expr.div $(← quoteExpr a) $(← quoteExpr b))')})

MUTANTS.update({"import-local-write-delete": ('let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)', 'let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)')})

MUTANTS.update({'import-invariant-for-bound':
    ('out := out.push (.forEach binding bound.expr bodyOut.toList)',
     'out := out.push (.forEach binding (.add bound.expr (.literal 1)) bodyOut.toList)')})

MUTANTS.update({'import-invariant-for-counter':
    ('{ e with values := e.values.insert counter (.localVar binding),',
     '{ e with values := e.values.insert counter (.literal 0),')})

def run(directory, output, name):
    fixture = "StorageVoidSequence" if name == "import-void-fallthrough" else "StorageSequence"
    if name.startswith("import-invariant-for-"):
        fixture = "InvariantForSequence"
    if name.startswith("import-local-write-"):
        fixture = "LocalWriteSequence"
    if name.startswith("import-default-local-"):
        fixture = "DefaultLocalSequence"
    if name.startswith("import-modulo-"):
        fixture = "ModuloSequence"
    if name.startswith("import-constant-array-"):
        fixture = "ConstantArraySequence"
    if name.startswith("import-numeric-"):
        fixture = "NumericLiteralSequence"
    if name.startswith("import-mapping-"):
        fixture = "MappingSequence"
    if name.startswith("import-logical-"):
        fixture = "ShortCircuitSequence"
    if name.startswith('import-if-'):
        fixture = 'IfElseSequence'
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
                              else 'Compiler/SolidityImport/Quote.lean' if name == 'import-modulo-quote'
                              else 'Verity/Core/Model/Denote.lean' if name.startswith('denote-')
                              else 'Compiler/SolidityImport/Import.lean')
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import', 'Compiler.SolidityImport.SequenceRunner'], cwd=directory,
                timeout=600, log=directory / 'build.log')
        if name == 'import-modulo-quote':
            # Quotation is independently checked against the original model.
            # This mutation must fail that exact invariant, before execution.
            artifact = directory / '.lake/quote-mutated.olean'
            result = subprocess.run(['lake', 'env', 'lean', '-j1',
                'Contracts/SolidityImportSmoke/ModuloSequenceModel.lean', '-o', str(artifact)],
                cwd=directory, text=True, capture_output=True, timeout=600)
            diagnostic = 'internal: the elaborated model differs from the imported value'
            log = result.stdout + result.stderr
            log_path = directory / 'quote-integrity.log'
            log_path.write_text(log)
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise HarnessError('quote mutation did not trigger the exact model-integrity check')
            reports.append({'mutant': name, 'status': 'detected', 'detected': True,
                'baselinePassed': True, 'kind': 'model-integrity-rejection',
                'diagnostic': diagnostic, 'log': str(log_path)})
            write_json(output / 'mutation-results.json', reports)
            print(f'{name}: rejected by exact model-integrity check', flush=True)
            continue
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
