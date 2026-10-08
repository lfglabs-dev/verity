"""Actual scalar storage importer mutations, with unmodified controls and reduced witnesses."""
import json
import os
import re
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
    'import-scalar-delete': ('  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"\n  markField name\n  let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do', '  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"\n  markField name\n  let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do'),
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
 'import-mapping-delete': ('    unless info.scalarMapping && info.keyCount == count do\n      failAt target "only scalar mapping values are writable"\n    markField name\n    let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do', '    unless info.scalarMapping && info.keyCount == count do\n      failAt target "only scalar mapping values are writable"\n    markField name\n    let value ← if deleting then pure ({ pre := #[], expr := (.literal 1 : Expr) } : Val) else do'),
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
    'import-if-root-swap': ('        let (noOut, noReturned) ← lowerRootStatements no\n        restore\n        out := out ++ condition.pre |>.push (.ite condition.expr yesOut.toList noOut.toList)', '        let (noOut, noReturned) ← lowerRootStatements no\n        restore\n        out := out ++ condition.pre |>.push (.ite condition.expr noOut.toList yesOut.toList)'),
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

MUTANTS.update({
    'import-helper-loop-block': ('out := out ++ (← lowerHelperLoopBody statement)', 'out := out ++ #[]'),
    'import-helper-loop-branch': ('let yesOut ← lowerHelperLoopBody (← mField statement "trueBody")', 'let yesOut : Array Stmt := #[]'),
    'import-helper-loop-nested': ('| "ForStatement" => out := out ++ (← lowerFor statement lowerHelperLoopBody)', '| "ForStatement" => pure ()'),
    'import-helper-loop-drop': ('let pre ← lowerFor s lowerHelperLoopBody', 'let pre : Array Stmt := #[]'),
    'import-helper-loop-effect': ('| "ExpressionStatement" => out := out ++ (← lowerEffect statement)', '| "ExpressionStatement" => pure ()'),
    'import-helper-loop-emit': ('| "EmitStatement" => out := out ++ (← lowerEmit statement)', '| "EmitStatement" => pure ()'),
})

MUTANTS.update({
    'import-helper-effect-binary-guard': ('if statefulCallIn (← mField j "leftExpression") env ||\n        statefulCallIn (← mField j "rightExpression") env then', 'if false then'),
    'import-helper-effect-argument-guard': ('if statefulCallIn arg (← get) then', 'if false then'),
    'import-helper-effect-classifier': ('| some fn => ![some "pure", some "view"].contains (optStr fn "stateMutability")', '| some _ => false'),
    'import-helper-effect-drop': ('-- Use the same exact assignment/delete and require rules as root bodies.\n        -- The helper continuation still resumes only after these effects.\n        let pre ← lowerEffect s', '-- Use the same exact assignment/delete and require rules as root bodies.\n        -- The helper continuation still resumes only after these effects.\n        let pre : Array Stmt := #[]'),
    'import-packed-member-delete': ('markField name\n    let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do\n      let right ← mField expression "rightHandSide"\n      atom (← convert ty (← mType right) (← lowerExpr right) right)\n    return value.pre.push (write value.expr)', 'markField name\n    let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do\n      let right ← mField expression "rightHandSide"\n      atom (← convert ty (← mType right) (← lowerExpr right) right)\n    return value.pre.push (write value.expr)'),
    'import-packed-member-value': ('return value.pre.push (write value.expr)', 'return value.pre.push (write (.literal 0))'),
    'import-packed-member-target': ('Stmt.setStructMember field key member value', 'Stmt.setStructMember field key "middle" value'),
    'import-packed-member-two-keys': ('Stmt.setStructMember2 field key1 key2 member value', 'Stmt.setStructMember2 field key2 key1 member value'),
    'import-packed-member-capture': ('pure (#[.letVar binding key], .localVar binding)', 'pure (#[], key)'),
})

MUTANTS.update({'import-fixed-array-word': ('wordOffset := index / perWord, packed', 'wordOffset := (index / perWord) * 2, packed'), 'import-fixed-array-bit': ('let offset := (index % perWord) * width', 'let offset := ((index % perWord + 1) % perWord) * width'), 'import-fixed-array-capture': ('((pre ++ key.pre).push (.letVar captured key.expr))', '((pre ++ key.pre).push (.letVar captured (.literal 0)))'), 'import-fixed-array-read': ('[.assignVar dest (read s!"__solidity_element_{i}")]', '[.assignVar dest (read "__solidity_element_0")]'), 'import-fixed-array-bound': ('(valuePre ++ pre).push (.ite (.lt index (.literal length))', '(valuePre ++ pre).push (.ite (.lt index (.literal (length + 1)))'), 'import-fixed-array-write': ('[write s!"__solidity_element_{i}" (.localVar capturedValue)]', '[write s!"__solidity_element_{i}" (.literal 0)]'), 'import-fixed-array-two-keys': ('Stmt.setStructMember2 name key1 key2 member value', 'Stmt.setStructMember2 name key2 key1 member value'), 'import-fixed-array-snapshot': ('elements := elements.push (.localVar binding)', 'elements := elements.push (read s!"__solidity_element_{i}")'), 'import-fixed-array-delete': ('let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do\n        let right ← mField expression "rightHandSide"', 'let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do\n        let right ← mField expression "rightHandSide"')})


MUTANTS.update({'import-fixed-array-snapshot-read': ('[.assignVar dest element] [])', '[.assignVar dest (.literal 0)] [])'), 'import-fixed-array-read-bound': ('let mut pre := pre.push (.ite (.lt index (.literal length))', 'let mut pre := pre.push (.ite (.lt index (.literal 0))'), 'import-fixed-array-snapshot-bound': ('let mut pre := key.pre.push (.ite (.lt key.expr (.literal elements.size))', 'let mut pre := key.pre.push (.ite (.lt key.expr (.literal 0))')})


MUTANTS.update({
    'import-array-write-order': ('let mut result := (valuePre ++ pre).push', 'let mut result := (pre ++ valuePre).push'),
    'import-array-write-capture': ('let valuePre := value.pre.push (.letVar capturedValue value.expr)', 'let valuePre := value.pre.push (.letVar capturedValue (.literal 0))'),
})

MUTANTS.update({
    'import-discarded-helper-emit': ('let emitted ← lowerEmit s', 'let emitted : Array Stmt := #[]'),
    'import-discarded-helper-drop': ('let result ← atom (← lowerCall expression)\n        return result.pre', 'let _ ← atom (← lowerCall expression)\n        return #[]'),
})

MUTANTS.update({
    'import-byte-local-pointer': ('pointer := .localVar pointer, size := .localVar size }', 'pointer := .literal 0, size := .localVar size }'),
    'import-byte-local-length': ('pointer := .localVar pointer, size := .localVar size }', 'pointer := .localVar pointer, size := .literal 0 }'),
    'import-byte-local-initialize': ('let effects := buffer.pre ++ #[.letVar pointer buffer.pointer, .letVar size buffer.size]', 'let effects := buffer.pre ++ #[.mstore buffer.pointer (.literal 0), .letVar pointer buffer.pointer, .letVar size buffer.size]'),
})

MUTANTS.update({
    'import-named-helper-default': ('pre := pre.push (.letVar binding (.literal 0))', 'pre := pre.push (.letVar binding (.literal 1))'),
    'import-named-helper-fallthrough': ('(← get).helperResult.map fun (binding, _) => Expr.localVar binding', '(← get).helperResult.map fun (_binding, _) => Expr.literal 0'),
    'import-named-helper-assembly': ('pure (v.pre.push (.assignVar binding cleaned) ++ tail, result)', 'pure (v.pre.push (.assignVar binding (.literal 0)) ++ tail, result)'),
    'import-named-helper-width': ('if width < 256 then Expr.bitAnd v.expr (.literal (2^width-1)) else v.expr', 'if width < 256 then v.expr else v.expr'),
    'import-named-helper-bool': ('if ty == "bool" then Expr.logicalNot (.logicalNot v.expr)', 'if ty == "bool" then v.expr'),
    'import-named-helper-frame': ('helperResult := saved.helperResult', 'helperResult := e.helperResult'),
    'import-named-helper-branch': ('| "InlineAssembly" => pure (← get).helperResult.isNone', '| "InlineAssembly" => pure true'),
})

MUTANTS.update({
    'import-yul-numeric-literal': ('pure (.literal value)\n  | "YulIdentifier" =>', 'pure (.bitXor (.literal value) (.literal 1))\n  | "YulIdentifier" =>'),
    'import-yul-numeric-add': ('| "add", #[a, b] => pure (.add a b)', '| "add", #[a, b] => pure (.sub a b)'),
    'import-yul-result-scope': ('{ e with values := e.values.insert id expr, yulNames := e.yulNames.insert name expr,', '{ e with values := e.values.insert id expr, yulNames := e.yulNames,'),
    'import-yul-result-id-guard': ('unless (← get).helperReturnId == some targetId do', 'unless true do'),
    'import-solc-viair-guard': ('if profile.viaIR && !release.supportsViaIR then', 'if false then'),
    'import-solc-uncollected-source-guard': ('unless sources.contains logical do', 'unless true do'),
    'import-inheritance-virtual-dispatch': ('if env.linearizedBases.contains cid then', 'if false then'),
    'import-inheritance-super-c3': ('let some resolvedId := resolveInContracts env superBases id.toNat', 'let some resolvedId := some id.toNat'),
    'import-inheritance-duplicate-storage-guard': ('if env.duplicateLayoutLabels.contains name then', 'if false then'),
    'import-void-helper-continuation': ('let effStmts ← lowerEffect s\n        let tailStmts ← kRest\n        pure (effStmts ++ tailStmts)', 'let effStmts ← lowerEffect s\n        pure effStmts'),
    'import-void-helper-nested-return-branch': ('let yesStmts ← lowerVoidHelperFrom yes.toList (if yesAll then pure #[] else kBranch)', 'let yesStmts ← lowerVoidHelperFrom yes.toList (pure #[])'),
    'import-void-helper-revert-condition': ('return pre.push (.requireError (.literal 0) name values)', 'return pre.push (.requireError (.literal 1) name values)'),
    'import-void-helper-unary-not': ('pure { pre := v.pre, expr := .logicalNot v.expr }', 'pure { pre := v.pre, expr := v.expr }'),
    'import-void-helper-root-named-fallthrough': ('else if !(← get).rootReturns.isEmpty then\n      out := out ++ #[.returnValues (← get).rootReturns.toList]', 'else if !(← get).rootReturns.isEmpty then\n      out := out ++ #[.returnValues ((← get).rootReturns.toList.map fun _ => .literal 0)]'),
    'import-modifier-unchecked-modifier-drop': ('let mut out := rootInit ++ modStmts ++ bodyOut', 'let mut out := rootInit ++ bodyOut'),
    'import-modifier-unchecked-sub-checked': ('let wrapped := if bits < 256 then Expr.bitAnd (.sub lhs rhs) (.literal (2 ^ bits - 1)) else .sub lhs rhs\n      pure { pre := #[], expr := wrapped }', 'checkedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }'),
    'import-modifier-unchecked-compound-op': ('checkedAdd bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }', 'checkedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }'),
    'import-modifier-unchecked-assignment-expr-write': ('return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr) |>.push (.setStorage name (.localVar resultVar)), expr := .localVar resultVar }', 'return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr), expr := .localVar resultVar }'),
    'import-modifier-unchecked-constant-power': ('let power := a ^ b', 'let power := a * b'),
    'import-modifier-unchecked-sibling-guard': ('if (assignmentIn (← mField j "leftExpression") && (!right.pre.isEmpty || !isOrderIndependentSibling right.expr)) ||\n        (assignmentIn (← mField j "rightExpression") && (!left.pre.isEmpty || !isOrderIndependentSibling left.expr)) then', 'if false then'),
    'import-tuple-helper-return-swap': ('for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              pre := pre.push (.assignVar binding (vals.getD i (.literal 0)))', 'for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              pre := pre.push (.assignVar binding (vals.getD (results.size - 1 - i) (.literal 0)))'),
    'import-tuple-helper-local-drop': ('out := out ++ converted.pre |>.push (.letVar binding converted.expr)', 'out := out ++ converted.pre |>.push (.letVar binding (.literal 0))'),
    'import-tuple-helper-assign-storage-drop': ('assigns := assigns ++ pre ++ converted.pre |>.push (.setStorage name storedExpr)', 'assigns := assigns ++ pre ++ converted.pre'),
    'import-tuple-helper-param-compound-init-zero': ('if (bodyCompoundAssignedIds body).contains pid && !(bodyDirectAssignedIds body).contains pid then\n          let some scalar := paramType pty\n            | failAt p s!"unsupported writable helper parameter type {pty}"\n          let binding ← freshFor (if pname == "" then "param" else pname)\n          let expr := Expr.localVar binding\n          pre := pre ++ converted.pre |>.push (.letVar binding converted.expr)', 'if (bodyCompoundAssignedIds body).contains pid && !(bodyDirectAssignedIds body).contains pid then\n          let some scalar := paramType pty\n            | failAt p s!"unsupported writable helper parameter type {pty}"\n          let binding ← freshFor (if pname == "" then "param" else pname)\n          let expr := Expr.localVar binding\n          pre := pre ++ converted.pre |>.push (.letVar binding (.literal 0))'),
    'import-tuple-helper-duplicate-target-guard': ('unless cid ≥ 0 && !seenIds.contains cid.toNat do', 'unless cid ≥ 0 do'),
    'import-int256-contract-unary-neg': ('let ok := Stmt.assignVar dest (.sub (.literal 0) a.expr)\n            let ite := iteStmt (.eq a.expr (.literal (2 ^ 255))) overflowPanic ok', 'let ok := Stmt.assignVar dest a.expr\n            let ite := iteStmt (.eq a.expr (.literal (2 ^ 255))) overflowPanic ok'),
    'import-int256-contract-sdiv': ('let ok := Stmt.assignVar dest (.sdiv a.expr b.expr)', 'let ok := Stmt.assignVar dest (.div a.expr b.expr)'),
    'import-int256-contract-slt': ('if isSigned then cmp .slt left right else cmp .lt left right', 'if isSigned then cmp .lt left right else cmp .lt left right'),
    'import-int256-contract-type-bounds': ('if tname == "int256" || tname == "int" then\n    let bound := if member == "max" then 2 ^ 255 - 1 else 2 ^ 255', 'if tname == "int256" || tname == "int" then\n    let bound := if member == "max" then 0 else 2 ^ 255'),
    'import-int256-contract-checked-add-overflow': ('let nonNegB := iteStmt (.slt sum a.expr) overflowPanic ok\n  let negB := iteStmt (.sgt sum a.expr) overflowPanic ok', 'let nonNegB := ok\n  let negB := ok'),
    'import-int256-contract-signed-modulo-guard': ('unless common.startsWith "uint" do failAt j "modulo requires unsigned scalar operands"', 'unless true do failAt j "modulo requires unsigned scalar operands"'),
    'import-fnptr-struct-delete-modifier-branch-swap': ('pure (pre, .branch (.localVar condBinding) trueFnId falseFnId)', 'pure (pre, .branch (.localVar condBinding) falseFnId trueFnId)'),
    'import-fnptr-struct-delete-modifier-delete-nonzero': ('for member in info.memberNames do\n        out := out.push (writeMember member (.literal 0))', 'for member in info.memberNames do\n        out := out.push (writeMember member (.literal 1))'),
    'import-fnptr-struct-delete-modifier-post-drop': ('out := ((out ++ v.pre).push (.letVar captured v.expr) ++ env.rootPost).push (.returnValues [.localVar captured])', 'out := ((out ++ v.pre).push (.letVar captured v.expr)).push (.returnValues [.localVar captured])'),
    'import-fnptr-struct-delete-modifier-opaque-delete-guard': ('unless info.opaqueNames.isEmpty do\n        failAt target "cannot delete mapping struct with opaque members"', 'unless true do\n        failAt target "cannot delete mapping struct with opaque members"'),
    'import-empty-array-bytes-calldata-length-zero': ('let some cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"\n            pure (.expr { pre, expr := .localVar cb.lengthBinding })', 'let some _cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"\n            pure (.expr { pre, expr := .literal 0 })'),
    'import-empty-array-bytes-calldata-empty-return-len': ('else if emptyBodyArrayRet?.isSome then\n      out := out ++ #[.returnValues [.literal 32, .literal 0]]', 'else if emptyBodyArrayRet?.isSome then\n      out := out ++ #[.returnValues [.literal 0]]'),
    'import-empty-array-bytes-calldata-tail-bound': ('guard (.le (.add (.localVar dataBinding) (.localVar lengthBinding)) .calldatasize) ]', 'guard (.le (.localVar dataBinding) .calldatasize) ]'),
    'import-empty-array-bytes-calldata-nonempty-body-guard': ('unless fnStmts.isEmpty && fnMods.isEmpty do return none', 'unless true do return none'),
    'import-overload-const-error-cond-tuple-tload-branch-swap': ('return (pre.push (.ite cond.expr thenB.toList elseB.toList), outRets)', 'return (pre.push (.ite cond.expr elseB.toList thenB.toList), outRets)'),
    'import-overload-const-error-cond-tuple-tload-tload-one': ('| "tload", #[a] => pure (.tload a)', '| "tload", #[_a] => pure (.literal 1)'),
    'import-overload-const-error-cond-tuple-tload-const-arg-one': ('let isConstLiteral := match converted.expr with\n        | .literal n => converted.pre.isEmpty && Denote.errorScalarValueValid modelType n\n        | _ => false\n      unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"\n    let value ← atom converted', 'let isConstLiteral := match converted.expr with\n        | .literal n => converted.pre.isEmpty && Denote.errorScalarValueValid modelType n\n        | _ => false\n      unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"\n    let value ← atom (if isDirectScalar then converted else { pre := #[], expr := .literal 1 })'),
    'import-overload-const-error-cond-tuple-tload-nonconst-error-guard': ('unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"', 'unless true do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"'),
})

def run(directory, output, name):
    fixture = "StorageVoidSequence" if name == "import-void-fallthrough" else "StorageSequence"
    if name.startswith("import-overload-const-error-cond-tuple-tload-"):
        fixture = "OverloadConstErrorCondTupleTloadSequence"
    if name.startswith("import-empty-array-bytes-calldata-"):
        fixture = "EmptyArrayReturnBytesCalldataSequence"
    if name.startswith("import-fnptr-struct-delete-modifier-"):
        fixture = "FnPtrStructDeleteModifierSequence"
    if name.startswith("import-int256-contract-"):
        fixture = "Int256ContractTypeSequence"
    if name.startswith("import-tuple-helper-"):
        fixture = "TupleHelperSequence"
    if name.startswith("import-modifier-unchecked-"):
        fixture = "ModifierUncheckedCompoundSequence"
    if name.startswith("import-void-helper-"):
        fixture = "VoidHelperGuardSequence"
    if name.startswith("import-inheritance-"):
        fixture = "InheritanceSequence"
    if name.startswith("import-solc-"):
        fixture = "Solc0810Sequence"
    if name.startswith("import-yul-numeric-"):
        fixture = "YulNumericSequence"
    if name.startswith(("import-named-helper-", "import-yul-result-")):
        fixture = "NamedHelperReturnSequence"
    if name.startswith("import-byte-local-"):
        fixture = "EncodedByteLocalSequence"
    if name.startswith("import-discarded-helper-"):
        fixture = "DiscardedHelperSequence"
    if name.startswith("import-array-write-"):
        fixture = "FixedArrayWriteOrderSequence"
    if name.startswith("import-fixed-array-"):
        fixture = "MappingFixedArraySequence"
    if name.startswith("import-helper-effect-"):
        fixture = "HelperEffectSequence"
    if name.startswith("import-packed-member-"):
        fixture = "PackedMemberWriteSequence"
    if name.startswith("import-helper-loop-"):
        fixture = "HelperLoopSequence"
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
            '--transactions', '64' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence'} else '3',
            '--seed', '2490' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence'} else '2453', '--shrink-attempts', '100' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence'} else '30',
            '--output', str(output)]
    if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence'}:
        argv.extend(['--change-prefix', *map(str, list(range(9)) + ([19, 20, 21, 25, 30, 40] if fixture in {'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence'} else [65535, 65536]) + [(1 << 256) - 1])])
    if fixture == 'Solc0810Sequence':
        argv = argv[:argv.index('--change-prefix')] + ['--solc-version', '0.8.10', '--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 100, 1000, 50000, 100000, 999999, (1 << 256) - 1])]
    if fixture == 'YulNumericSequence':
        argv = argv[:argv.index('--change-prefix')] + ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 32, 33, 255, 256, (1 << 255) - 1, 1 << 255, (1 << 256) - 2, (1 << 256) - 1])]
    if fixture == 'NamedHelperReturnSequence':
        prefix = argv.index('--change-prefix')
        argv = argv[:prefix] + ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 40, 50, 60, 70, 255, 256, 257, (1 << 160) - 1, 1 << 160, (1 << 160) + 1, (1 << 256) - 1])]
    if fixture in {'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'OverloadConstErrorCondTupleTloadSequence'}:
        prefix = argv.index('--change-prefix')
        argv = argv[:prefix] + ['--change-prefix', *map(str, [19, 0, 1, 2, 3, 20, 21, 96, 97, 98, 99999, 100000, (1 << 256) - 1])]
    if fixture == 'EmptyArrayReturnBytesCalldataSequence':
        prefix = argv.index('--change-prefix')
        argv = argv[:prefix] + ['--change-prefix', *map(str, [0, 1, 2, 3, 16, 17, 18, (1 << 256) - 1])]
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


def helper_order_control(directory, name, mutated):
    """A guard mutant must admit exactly the source that the baseline rejects."""
    target = directory / '.lake/helper-order-control'
    target.mkdir(exist_ok=True)
    using_clause = '{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }'
    require_located = True
    if name == 'import-yul-result-id-guard':
        diagnostic = 'Yul assigns result, not the return declaration result'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function h(uint256 n) internal pure returns (uint256 result) {
  result = 7;
  if (n == 0) {
   uint256 result = n;
   assembly { result := xor(n, n) }
  }
  return result;
 }
 function checked(uint256 x) external pure returns (uint256) { return h(x); }
}
''')
    elif name == 'import-solc-viair-guard':
        diagnostic = 'viaIR is not supported for solc 0.8.10+commit.fc410830'
        using_clause = '{ solc := "0.8.10+commit.fc410830", evmVersion := "london", viaIR := true, optimizerRuns := some 1, bytecodeHash := "none" }'
        require_located = False
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.10;
contract C {
 function checked(uint256 x) external pure returns (uint256) { return x; }
}
''')
    elif name == 'import-solc-uncollected-source-guard':
        diagnostic = 'solc loaded uncollected source Uncollected.sol'
        using_clause = '{ solc := "0.8.10+commit.fc410830", evmVersion := "london", viaIR := false, optimizerRuns := some 1, bytecodeHash := "none" }'
        require_located = False
        (directory / 'Uncollected.sol').write_text('''pragma solidity 0.8.10;
library Uncollected { uint256 internal constant UNUSED = 1; }
''')
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.10;
import
  "./Uncollected.sol";
contract C {
 function checked(uint256 x) external pure returns (uint256) { return x; }
}
''')
    elif name == 'import-inheritance-duplicate-storage-guard':
        diagnostic = 'shadowed storage declaration dup is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
abstract contract Base { uint256 private dup; }
contract C is Base {
 uint256 private dup;
 function checked(uint256 x) external returns (uint256) { dup = x; return dup; }
}
''')
    elif name == 'import-modifier-unchecked-sibling-guard':
        diagnostic = 'assignment operand with non-atomic sibling requires explicit evaluation-order support'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 uint256 private v;
 function checked(uint256 x) external returns (uint256) { return (v = x) + v; }
}
''')
    elif name == 'import-tuple-helper-duplicate-target-guard':
        diagnostic = 'duplicate or invalid target in tuple assignment'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function _pair(uint256 y) internal pure returns (uint256, uint256) { return (y, y + 1); }
 function checked(uint256 x) external pure returns (uint256) {
  uint256 a = 0;
  (a, a) = _pair(x);
  return a;
 }
}
''')
    elif name == 'import-int256-contract-signed-modulo-guard':
        diagnostic = 'modulo requires unsigned scalar operands'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  return uint256(int256(x) % int256(7));
 }
}
''')
    elif name == 'import-fnptr-struct-delete-modifier-opaque-delete-guard':
        diagnostic = 'cannot delete mapping struct with opaque members'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct S { uint256 a; uint256[] dyn; }
 mapping(uint256 => S) private m;
 function checked(uint256 x) external returns (uint256) {
  delete m[x];
  return m[x].a;
 }
}
''')
    elif name == 'import-empty-array-bytes-calldata-nonempty-body-guard':
        diagnostic = 'an explicit root return is required'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 uint256 private v;
 function checked(uint256 x) external returns (uint256[] memory) {
  v = x;
 }
}
''')
    elif name == 'import-overload-const-error-cond-tuple-tload-nonconst-error-guard':
        diagnostic = 'custom-error arguments currently require literals or scalar bindings'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 error Failure(address who);
 function checked(uint256 x) external pure returns (uint256) {
  if (x > 0) revert Failure(address(uint160(x)));
  return 0;
 }
}
''')
    else:
        argument = name.endswith('argument-guard')
        expression = 'add(bump(), bump())' if argument else 'bump() + bump()'
        diagnostic = ('stateful helper call arguments require explicit evaluation-order support'
                      if argument else 'stateful helper operands require explicit evaluation-order support')
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 uint256 value;
 function bump() internal returns (uint256) { value = value + 1; return value; }
 function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
 function checked(uint256) external returns (uint256) { return ''' + expression + '''; }
}
''')
    driver = target / 'Check.lean'
    driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{target}" entry "Fixture.sol"
  using {using_clause}
  contract C
  function checked(uint256)
''')
    artifact = target / ('mutated.olean' if mutated else 'baseline.olean')
    result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                            cwd=directory, text=True, capture_output=True, timeout=120)
    log = result.stdout + result.stderr
    log_path = target / ('mutated.log' if mutated else 'baseline.log')
    log_path.write_text(log)
    if mutated:
        if result.returncode or not artifact.exists():
            raise HarnessError(f'{name}: removed guard did not admit the exact negative control; see {log_path}')
    elif (result.returncode == 0 or artifact.exists() or diagnostic not in log
          or (require_located and not re.search(r'Fixture\.sol:\d+:\d+:', log))):
        raise HarnessError(f'{name}: baseline did not precisely reject the order control; see {log_path}')
    return diagnostic, str(log_path)


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
        order_guard = name in {'import-helper-effect-binary-guard',
                              'import-helper-effect-argument-guard',
                              'import-helper-effect-classifier',
                              'import-yul-result-id-guard',
                              'import-solc-viair-guard',
                              'import-solc-uncollected-source-guard',
                              'import-inheritance-duplicate-storage-guard',
                              'import-modifier-unchecked-sibling-guard',
                              'import-tuple-helper-duplicate-target-guard',
                              'import-int256-contract-signed-modulo-guard',
                              'import-fnptr-struct-delete-modifier-opaque-delete-guard',
                              'import-empty-array-bytes-calldata-nonempty-body-guard',
                              'import-overload-const-error-cond-tuple-tload-nonconst-error-guard'}
        if order_guard:
            helper_order_control(directory, name, False)
        source = directory / ('Compiler/SolidityImport/SequenceRunner.lean' if name.startswith('observe-event-')
                              else 'Compiler/SolidityImport/Quote.lean' if name == 'import-modulo-quote'
                              else 'Compiler/SolidityImport/AbiLowering.lean' if name == 'import-empty-array-bytes-calldata-tail-bound'
                              else 'Verity/Core/Model/Denote.lean' if name.startswith('denote-')
                              else 'Compiler/SolidityImport/Import.lean')
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import', 'Compiler.SolidityImport.SequenceRunner'], cwd=directory,
                timeout=600, log=directory / 'build.log')
        if order_guard:
            diagnostic, log_path = helper_order_control(directory, name, True)
            reports.append({'mutant': name, 'status': 'detected', 'detected': True,
                            'baselinePassed': True, 'kind': 'unsupported-order-admission',
                            'diagnostic': diagnostic, 'log': log_path})
            write_json(output / 'mutation-results.json', reports)
            print(f'{name}: exact rejection guard removal detected', flush=True)
            continue
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
