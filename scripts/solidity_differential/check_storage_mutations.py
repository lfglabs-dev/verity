"""Actual scalar storage importer mutations, with unmodified controls and reduced witnesses."""
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
from solidity_differential.engine import HarnessError, command, write_json
from solidity_differential.mutations import release, snapshot

MUTANTS = {
    'import-void-fallthrough': ('out := out.push .stop', 'out := out.push (.require (.literal 0) "mutated void return") |>.push .stop'),
    'denote-scalar-sibling-mask': ('let cleared := Verity.Core.Uint256.and current (Verity.Core.Uint256.not shiftedMaskNat)', 'let cleared := Verity.Core.Uint256.and current 0'),
    'import-scalar-read': ('pure { pre, expr := .storage name }', 'pure { pre, expr := .literal 0 }'),
    'import-scalar-slot': ('slot := some slot, packedBits }', 'slot := some (slot + 1), packedBits }'),
    'import-scalar-offset': ('some { offset, width }', 'some { offset := if width == 128 then 128 - offset else offset, width }'),
    'import-scalar-write': ('(.setStorage name value.expr)', '(.setStorage name (.literal 0))'),
    'import-scalar-delete': ('          return ← lowerStorageBytesWrite name pre target right\n      markField name\n      let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do', '          return ← lowerStorageBytesWrite name pre target right\n      markField name\n      let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do'),
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
 'import-mapping-bool-read': ('if info.booleanMapping then Expr.logicalNot (.logicalNot read) else read', 'if info.booleanMapping then Expr.logicalNot read else read')})


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
    'import-if-root-swap': ('        let (noOut, noReturned) ← lowerRootStatements no stmtIsTail\n        restore\n        out := out ++ condition.pre |>.push (.ite condition.expr yesOut.toList noOut.toList)', '        let (noOut, noReturned) ← lowerRootStatements no stmtIsTail\n        restore\n        out := out ++ condition.pre |>.push (.ite condition.expr noOut.toList yesOut.toList)'),
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

MUTANTS.update({"import-local-write-delete": ('          failAt target s!"unsupported scalar local assignment type {ty}"\n        let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)', '          failAt target s!"unsupported scalar local assignment type {ty}"\n        let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)')})

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
    'import-packed-member-delete': ('        markField name\n        let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)\n        return value.pre.push (write value.expr)', '        markField name\n        let value ← if deleting then pure ({ pre := #[], expr := .literal 1 } : Val) else do\n          let right ← mField expression "rightHandSide"\n          atom (← convert ty (← mType right) (← lowerExpr right) right)\n        return value.pre.push (write value.expr)'),
    'import-packed-member-value': ('return value.pre.push (write value.expr)', 'return value.pre.push (write (.literal 0))'),
    'import-packed-member-target': ('      | .one field key => pure (field, 1, fun (value : Expr) => Stmt.setStructMember field key member value)', '      | .one field key => pure (field, 1, fun (value : Expr) => Stmt.setStructMember field key "middle" value)'),
    'import-packed-member-two-keys': ('      | .two field key1 key2 => pure (field, 2, fun (value : Expr) => Stmt.setStructMember2 field key1 key2 member value)', '      | .two field key1 key2 => pure (field, 2, fun (value : Expr) => Stmt.setStructMember2 field key2 key1 member value)'),
    'import-packed-member-capture': ('pure (#[.letVar binding key], .localVar binding)', 'pure (#[], key)'),
})

MUTANTS.update({'import-fixed-array-word': ('wordOffset := index / perWord, packed', 'wordOffset := (index / perWord) * 2, packed'), 'import-fixed-array-bit': ('let offset := (index % perWord) * width', 'let offset := ((index % perWord + 1) % perWord) * width'), 'import-fixed-array-capture': ('pure (.fixedElement ((pre ++ key.pre).push (.letVar captured key.expr))', 'pure (.fixedElement ((pre ++ key.pre).push (.letVar captured (.literal 0)))'), 'import-fixed-array-read': ('[.assignVar dest (read s!"__solidity_element_{i}")]', '[.assignVar dest (read "__solidity_element_0")]'), 'import-fixed-array-bound': ('(valuePre ++ pre).push (.ite (.lt index (.literal length))', '(valuePre ++ pre).push (.ite (.lt index (.literal (length + 1)))'), 'import-fixed-array-write': ('[write s!"__solidity_element_{i}" (.localVar capturedValue)]', '[write s!"__solidity_element_{i}" (.literal 0)]'), 'import-fixed-array-two-keys': ('        | .two name key1 key2 => pure (name, 2, fun member value => Stmt.setStructMember2 name key1 key2 member value)\n        | .outer _ _ => failAt target "fixed array write requires both mapping keys"\n      let info ← resolveField name target\n      let some length := info.fixedArrayLength | failAt target "missing fixed array layout"', '        | .two name key1 key2 => pure (name, 2, fun member value => Stmt.setStructMember2 name key2 key1 member value)\n        | .outer _ _ => failAt target "fixed array write requires both mapping keys"\n      let info ← resolveField name target\n      let some length := info.fixedArrayLength | failAt target "missing fixed array layout"'), 'import-fixed-array-snapshot': ('          result := result.push (.letVar binding (read s!"__solidity_element_{i}"))\n          elements := elements.push (.localVar binding)', '          result := result.push (.letVar binding (read s!"__solidity_element_{i}"))\n          elements := elements.push (read s!"__solidity_element_{i}")'), 'import-fixed-array-delete': ('      let some length := info.fixedArrayLength | failAt target "missing fixed array layout"\n      unless info.keyCount == count do failAt target "fixed array mapping key count differs"\n      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do\n        let right ← mField expression "rightHandSide"', '      let some length := info.fixedArrayLength | failAt target "missing fixed array layout"\n      unless info.keyCount == count do failAt target "fixed array mapping key count differs"\n      let value ← if deleting then pure ({ pre := #[], expr := (.literal 1 : Expr) } : Val) else do\n        let right ← mField expression "rightHandSide"')})


MUTANTS.update({'import-fixed-array-snapshot-read': ('[.assignVar dest element] [])', '[.assignVar dest (.literal 0)] [])'), 'import-fixed-array-read-bound': ('let mut pre := pre.push (.ite (.lt index (.literal length))', 'let mut pre := pre.push (.ite (.lt index (.literal 0))'), 'import-fixed-array-snapshot-bound': ('let mut pre := key.pre.push (.ite (.lt key.expr (.literal elements.size))', 'let mut pre := key.pre.push (.ite (.lt key.expr (.literal 0))')})


MUTANTS.update({
    'import-array-write-order': ('      let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal length))', '      let mut result := (pre ++ valuePre).push (.ite (.lt index (.literal length))'),
    'import-array-write-capture': ('      let valuePre := value.pre.push (.letVar capturedValue value.expr)\n      let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal length))', '      let valuePre := value.pre.push (.letVar capturedValue (.literal 0))\n      let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal length))'),
})

MUTANTS.update({
    'import-discarded-helper-emit': ('let emitted ← lowerEmit s', 'let emitted : Array Stmt := #[]'),
    'import-discarded-helper-drop': ('let result ← atom (← lowerCall expression)\n        return result.pre', 'let _ ← atom (← lowerCall expression)\n        return #[]'),
})

MUTANTS.update({
    'import-byte-local-pointer': ('      { pre := #[], pointer := .localVar pointer, size := .localVar size }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,', '      { pre := #[], pointer := .literal 0, size := .localVar size }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,'),
    'import-byte-local-length': ('      { pre := #[], pointer := .localVar pointer, size := .localVar size }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,', '      { pre := #[], pointer := .localVar pointer, size := .literal 0 }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,'),
    'import-byte-local-initialize': ('    let effects := buffer.pre ++ #[.letVar pointer buffer.pointer, .letVar size buffer.size]\n    let retained : EncodedBytes :=\n      { pre := #[], pointer := .localVar pointer, size := .localVar size }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,', '    let effects := buffer.pre ++ #[.mstore buffer.pointer (.literal 0), .letVar pointer buffer.pointer, .letVar size buffer.size]\n    let retained : EncodedBytes :=\n      { pre := #[], pointer := .localVar pointer, size := .localVar size }\n    modify fun e =>\n      { e with byteBuffers := e.byteBuffers.insert id retained,'),
})

MUTANTS.update({
    'import-named-helper-default': ('pre := pre.push (.letVar binding (.literal 0))', 'pre := pre.push (.letVar binding (.literal 1))'),
    'import-named-helper-fallthrough': ('(← get).helperResult.map fun (binding, _) => Expr.localVar binding', '(← get).helperResult.map fun (_binding, _) => Expr.literal 0'),
    'import-named-helper-assembly': ('pure (v.pre.push (.assignVar binding cleaned) ++ tail, result)', 'pure (v.pre.push (.assignVar binding (.literal 0)) ++ tail, result)'),
    'import-named-helper-width': ('if width < 256 then Expr.bitAnd v.expr (.literal (2^width-1)) else v.expr', 'if width < 256 then v.expr else v.expr'),
    'import-named-helper-bool': ('if ty == "bool" then Expr.logicalNot (.logicalNot v.expr)', 'if ty == "bool" then v.expr'),
    'import-named-helper-frame': ('helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }\n  pure finalResult', 'helperResult := e.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }\n  pure finalResult'),
    'import-named-helper-branch': ('| "InlineAssembly" => pure (← get).helperResult.isNone', '| "InlineAssembly" => pure true'),
})

MUTANTS.update({
    'import-yul-numeric-literal': ('      pure { pre := #[], expr := .literal value }\n  | "YulIdentifier" =>', '      pure { pre := #[], expr := .bitXor (.literal value) (.literal 1) }\n  | "YulIdentifier" =>'),
    'import-yul-numeric-add': ('| "add", #[a, b] => pure { pre, expr := .add a b }', '| "add", #[a, b] => pure { pre, expr := .sub a b }'),
    'import-yul-result-scope': ('{ e with values := e.values.insert id expr, scalarTy := e.scalarTy.insert id scalarType,\n               yulNames := e.yulNames.insert name expr,', '{ e with values := e.values.insert id expr, scalarTy := e.scalarTy.insert id scalarType,\n               yulNames := e.yulNames,'),
    'import-yul-result-id-guard': ('unless (← get).helperReturnId == some targetId do', 'unless true do'),
    'import-solc-viair-guard': ('if profile.viaIR && !release.supportsViaIR then', 'if false then'),
    'import-solc-uncollected-source-guard': ('unless sources.contains logical do', 'unless true do'),
    'import-inheritance-virtual-dispatch': ('              if env.linearizedBases.contains cid then\n                match resolveInContracts env env.linearizedBases.toList id.toNat with', '              if false then\n                match resolveInContracts env env.linearizedBases.toList id.toNat with'),
    'import-inheritance-super-c3': ('          let some resolvedId := resolveInContracts env superBases id.toNat\n            | failAt callee s!"unresolved super function {id.toNat}"', '          let some resolvedId := some id.toNat\n            | failAt callee s!"unresolved super function {id.toNat}"'),
    'import-inheritance-duplicate-storage-guard': ('        if optStr decl "mutability" == some "immutable" then\n          failAt j s!"immutable state variable {name} is outside this slice"\n        if env.duplicateLayoutLabels.contains name then', '        if optStr decl "mutability" == some "immutable" then\n          failAt j s!"immutable state variable {name} is outside this slice"\n        if false then'),
    'import-void-helper-continuation': ('let effStmts ← lowerEffect s\n        let tailStmts ← kRest\n        pure (effStmts ++ tailStmts)', 'let effStmts ← lowerEffect s\n        pure effStmts'),
    'import-void-helper-nested-return-branch': ('let yesStmts ← lowerVoidHelperFrom yes.toList (if yesAll then pure #[] else kBranch)', 'let yesStmts ← lowerVoidHelperFrom yes.toList (pure #[])'),
    'import-void-helper-revert-condition': ('return pre.push (.requireError (.literal 0) name values)', 'return pre.push (.requireError (.literal 1) name values)'),
    'import-void-helper-unary-not': ('pure { pre := v.pre, expr := .logicalNot v.expr }', 'pure { pre := v.pre, expr := v.expr }'),
    'import-void-helper-root-named-fallthrough': ('else if !(← get).rootReturns.isEmpty then\n      out := out ++ #[.returnValues (← get).rootReturns.toList]', 'else if !(← get).rootReturns.isEmpty then\n      out := out ++ #[.returnValues ((← get).rootReturns.toList.map fun _ => .literal 0)]'),
    'import-modifier-unchecked-modifier-drop': ('let mut out := rootInit ++ modStmts ++ bodyOut', 'let mut out := rootInit ++ bodyOut'),
    'import-modifier-unchecked-sub-checked': ('        let wrapped := if bits < 256 then Expr.bitAnd (.sub lhs rhs) (.literal (2 ^ bits - 1)) else .sub lhs rhs\n        pure { pre := #[], expr := wrapped }', '        checkedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }'),
    'import-modifier-unchecked-compound-op': ('checkedAdd bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }', 'checkedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }'),
    'import-modifier-unchecked-assignment-expr-write': ('return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr) |>.push (.setStorage name (.localVar resultVar)), expr := .localVar resultVar }', 'return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr), expr := .localVar resultVar }'),
    'import-modifier-unchecked-constant-power': ('let power := a ^ b', 'let power := a * b'),
    'import-modifier-unchecked-sibling-guard': ('if (assignmentIn (← mField j "leftExpression") && (!right.pre.isEmpty || !isOrderIndependentSibling right.expr)) ||\n        (assignmentIn (← mField j "rightExpression") && (!left.pre.isEmpty || !isOrderIndependentSibling left.expr)) then', 'if false then'),
    'import-tuple-helper-return-swap': ('for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              pre := pre.push (.assignVar binding (vals.getD i (.literal 0)))', 'for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              pre := pre.push (.assignVar binding (vals.getD (results.size - 1 - i) (.literal 0)))'),
    'import-tuple-helper-local-drop': ('out := out ++ converted.pre |>.push (.letVar binding converted.expr)', 'out := out ++ converted.pre |>.push (.letVar binding (.literal 0))'),
    'import-tuple-helper-assign-storage-drop': ('assigns := assigns ++ pre ++ converted.pre |>.push (.setStorage name storedExpr)', 'assigns := assigns ++ pre ++ converted.pre'),
    'import-tuple-helper-param-compound-init-zero': ('if (bodyCompoundAssignedIds body).contains pid || (bodyDirectAssignedIds body).contains pid then\n          let some scalar := paramType pty\n            | failAt p s!"unsupported writable helper parameter type {pty}"\n          let binding ← freshFor (if pname == "" then "param" else pname)\n          let expr := Expr.localVar binding\n          pre := pre ++ converted.pre |>.push (.letVar binding converted.expr)', 'if (bodyCompoundAssignedIds body).contains pid || (bodyDirectAssignedIds body).contains pid then\n          let some scalar := paramType pty\n            | failAt p s!"unsupported writable helper parameter type {pty}"\n          let binding ← freshFor (if pname == "" then "param" else pname)\n          let expr := Expr.localVar binding\n          pre := pre ++ converted.pre |>.push (.letVar binding (.literal 0))'),
    'import-tuple-helper-duplicate-target-guard': ('unless cid ≥ 0 && !seenIds.contains cid.toNat do', 'unless cid ≥ 0 do'),
    'import-int256-contract-unary-neg': ('              let ok := Stmt.assignVar dest (.sub (.literal 0) a.expr)\n              let ite := iteStmt (.eq a.expr (.literal (2 ^ 255))) overflowPanic ok', '              let ok := Stmt.assignVar dest a.expr\n              let ite := iteStmt (.eq a.expr (.literal (2 ^ 255))) overflowPanic ok'),
    'import-int256-contract-sdiv': ('let ok := Stmt.assignVar dest (.sdiv a.expr b.expr)', 'let ok := Stmt.assignVar dest (.div a.expr b.expr)'),
    'import-int256-contract-slt': ('if isSigned then cmp .slt left right else cmp .lt left right', 'if isSigned then cmp .lt left right else cmp .lt left right'),
    'import-int256-contract-type-bounds': ('if tname == "int256" || tname == "int" then\n    let bound := if member == "max" then 2 ^ 255 - 1 else 2 ^ 255', 'if tname == "int256" || tname == "int" then\n    let bound := if member == "max" then 0 else 2 ^ 255'),
    'import-int256-contract-checked-add-overflow': ('let nonNegB := iteStmt (.slt sum a.expr) overflowPanic ok\n  let negB := iteStmt (.sgt sum a.expr) overflowPanic ok', 'let nonNegB := ok\n  let negB := ok'),
    'import-int256-contract-signed-modulo-guard': ('unless common.startsWith "uint" do failAt j "modulo requires unsigned scalar operands"', 'unless true do failAt j "modulo requires unsigned scalar operands"'),
    'import-fnptr-struct-delete-modifier-branch-swap': ('pure (pre, .branch (.localVar condBinding) trueFnId falseFnId)', 'pure (pre, .branch (.localVar condBinding) falseFnId trueFnId)'),
    'import-fnptr-struct-delete-modifier-delete-nonzero': ('    for member in info.memberNames do\n      out := out.push (writeMember member (.literal 0))', '    for member in info.memberNames do\n      out := out.push (writeMember member (.literal 1))'),
    'import-fnptr-struct-delete-modifier-post-drop': ('out := ((out ++ v.pre).push (.letVar captured v.expr) ++ env.rootPost).push (.returnValues [.localVar captured])', 'out := ((out ++ v.pre).push (.letVar captured v.expr)).push (.returnValues [.localVar captured])'),
    'import-fnptr-struct-delete-modifier-opaque-delete-guard': ('    unless info.opaqueNames.isEmpty do\n      failAt target "cannot delete mapping struct with opaque members"', '    unless true do\n      failAt target "cannot delete mapping struct with opaque members"'),
    'import-empty-array-bytes-calldata-length-zero': ('let some cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"\n            pure (.expr { pre, expr := .localVar cb.lengthBinding })', 'let some _cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"\n            pure (.expr { pre, expr := .literal 0 })'),
    'import-empty-array-bytes-calldata-empty-return-len': ('else if emptyBodyArrayRet?.isSome then\n      out := out ++ #[.returnValues [.literal 32, .literal 0]]', 'else if emptyBodyArrayRet?.isSome then\n      out := out ++ #[.returnValues [.literal 0]]'),
    'import-empty-array-bytes-calldata-tail-bound': ('guard (.le (.add (.localVar dataBinding) (.localVar lengthBinding)) .calldatasize) ]', 'guard (.le (.localVar dataBinding) .calldatasize) ]'),
    'import-empty-array-bytes-calldata-nonempty-body-guard': ('unless fnStmts.isEmpty && fnMods.isEmpty do return none', 'unless true do return none'),
    'import-overload-const-error-cond-tuple-tload-branch-swap': ('return (pre.push (.ite cond.expr thenB.toList elseB.toList), outRets)', 'return (pre.push (.ite cond.expr elseB.toList thenB.toList), outRets)'),
    'import-overload-const-error-cond-tuple-tload-tload-one': ('| "tload", #[a] => pure { pre, expr := .tload a }', '| "tload", #[_a] => pure { pre, expr := .literal 1 }'),
    'import-overload-const-error-cond-tuple-tload-const-arg-one': ('let isConstLiteral := match converted.expr with\n        | .literal n => converted.pre.isEmpty && Denote.errorScalarValueValid modelType n\n        | _ => false\n      unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"\n    let value ← atom converted', 'let isConstLiteral := match converted.expr with\n        | .literal n => converted.pre.isEmpty && Denote.errorScalarValueValid modelType n\n        | _ => false\n      unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"\n    let value ← atom (if isDirectScalar then converted else { pre := #[], expr := .literal 1 })'),
    'import-overload-const-error-cond-tuple-tload-nonconst-error-guard': ('unless isConstLiteral do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"', 'unless true do\n        failAt argument "custom-error arguments currently require literals or scalar bindings"'),
    'import-struct-fixed-array-read-zero': ('[.assignVar dest (read s!"__solidity_struct_array_{arrInfo.member}_{i}")] [])', '[.assignVar dest (.literal 0)] [])'),
    'import-struct-fixed-array-write-bounds': ('let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal arrInfo.length))\n        [] [.panicCode (.literal 0x32)])', 'let mut result := (valuePre ++ pre)'),
    'import-struct-fixed-array-return-zero': ('out := out.push (.returnValues elements.toList)', 'out := out.push (.returnValues (elements.toList.map fun _ => .literal 0))'),
    'import-struct-fixed-array-delete-guard': ('    unless info.structFixedArrays.isEmpty do\n      failAt target "cannot delete mapping struct with fixed-array members"', '    unless true do\n      failAt target "cannot delete mapping struct with fixed-array members"'),
    'import-msg-data-and-enum-calldata-guard': ('        let limit := match env.enumBounds.find? p.id with\n          | some enumMax => some enumMax', '        let limit := match env.enumBounds.find? p.id with\n          | some _enumMax => some (2^8)'),
    'import-msg-data-and-enum-cast-panic': ('    let check := Stmt.ite (.lt a.expr (.literal members.size))\n      [.assignVar dest a.expr] [.panicCode (.literal 0x21)]', '    let check := Stmt.ite (.literal 1)\n      [.assignVar dest a.expr] [.panicCode (.literal 0x21)]'),
    'import-msg-data-and-enum-length-zero': ('          let pre ← lowerMsgDataExpr base\n          pure (.expr { pre, expr := .calldatasize })', '          let pre ← lowerMsgDataExpr base\n          pure (.expr { pre, expr := .literal 0 })'),
    'import-msg-data-and-enum-encoding-cast-guard': ('      if (← mType j).startsWith "enum " then\n        unless args.size == 1 && (← mType args[0]!) == (← mType j) do\n          failAt j "fallible enum conversion in ABI encoding argument is unsupported"', '      if (← mType j).startsWith "enum " then\n        unless true do\n          failAt j "fallible enum conversion in ABI encoding argument is unsupported"'),
    'import-exp-and-bitwise-shift-exp-guard': ('        let maxExp := maxSafeExponent baseVal bits\n        let ok := Stmt.assignVar dest (.externalCall builtinExpName [.literal baseVal, b.expr])\n        let ite := iteStmt (.lt (.literal maxExp) b.expr) overflowPanic ok', '        let _maxExp := maxSafeExponent baseVal bits\n        let ok := Stmt.assignVar dest (.externalCall builtinExpName [.literal baseVal, b.expr])\n        let ite := ok'),
    'import-exp-and-bitwise-shift-shl-order': ('        let some bits := bitsOf common | failAt j s!"unsupported shift type {common}"\n        let shifted := if bits < 256 then Expr.bitAnd (.shl b.expr a.expr) (.literal (2 ^ bits - 1)) else .shl b.expr a.expr', '        let some bits := bitsOf common | failAt j s!"unsupported shift type {common}"\n        let shifted := if bits < 256 then Expr.bitAnd (.shl a.expr b.expr) (.literal (2 ^ bits - 1)) else .shl a.expr b.expr'),
    'import-exp-and-bitwise-shift-bitnot-mask': ('            let some bits := bitsOf jTy | failAt j s!"unsupported bitwise negation type {jTy}"\n            let inverted := if bits < 256 then Expr.bitAnd (.bitNot a.expr) (.literal (2 ^ bits - 1)) else .bitNot a.expr', '            let some _bits := bitsOf jTy | failAt j s!"unsupported bitwise negation type {jTy}"\n            let inverted := Expr.bitNot a.expr'),
    'import-exp-and-bitwise-shift-sar-unsigned': ('    else if operator == ">>=" then\n      pure { pre := #[], expr := .sar rhs lhs }', '    else if operator == ">>=" then\n      pure { pre := #[], expr := .shr rhs lhs }'),
    'import-exp-and-bitwise-shift-dynamic-exp-guard': ('  unless isConstLiteralVal left || isConstLiteralVal right do\n    failAt at_ "checked exponentiation with dynamic base and exponent is outside this slice"', '  unless true do\n    failAt at_ "checked exponentiation with dynamic base and exponent is outside this slice"'),
    'import-while-clz-struct-loc-clz-zero': ('            .ite (.eq (.localVar inputBinding) (.literal 0))\n              [.assignVar countBinding (.literal 256)]\n              searchStmts', '            .ite (.eq (.localVar inputBinding) (.literal 0))\n              [.assignVar countBinding (.literal 0)]\n              searchStmts'),
    'import-while-clz-struct-loc-while-bound-one': ('  pure #[.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]]', '  pure #[.forEach loopVar (.literal 1) [.ite condVal.expr bodyOut.toList []]]'),
    'import-while-clz-struct-loc-mem-elem-zero': ('            let offset := Expr.add pointer (.literal (32*i))\n            let value := if !inMemory then Expr.calldataload offset else Expr.mload offset', '            let offset := Expr.add pointer (.literal (32*i))\n            let value := if !inMemory then Expr.calldataload offset else .literal 0'),
    'import-while-clz-struct-loc-nondecreasing-guard': ('  unless rightShiftOk || clearLowestOk || clearMsbOk do\n    failAt stepExpr "while loop update is not a recognized bounded bit-clearing or right-shift step"', '  unless true do\n    failAt stepExpr "while loop update is not a recognized bounded bit-clearing or right-shift step"'),
    'import-yul-builtins-encode-selector-smod-div': ('| "smod", #[a, b] => pure { pre, expr := .smod a b }', '| "smod", #[a, b] => pure { pre, expr := .sdiv a b }'),
    'import-yul-builtins-encode-selector-byte-zero': ('| "byte", #[a, b] => pure { pre, expr := .byte a b }', '| "byte", #[_a, _b] => pure { pre, expr := .literal 0 }'),
    'import-yul-builtins-encode-selector-signextend-id': ('| "signextend", #[a, b] => pure { pre, expr := .signextend a b }', '| "signextend", #[_a, b] => pure { pre, expr := b }'),
    'import-yul-builtins-encode-selector-selector-pad': ('      | failAt fnExpr "invalid functionSelector hex digit"\n    word := word * 16 + digit\n  let padded := word * 16 ^ 56', '      | failAt fnExpr "invalid functionSelector hex digit"\n    word := word * 16 + digit\n  let padded := word'),
    'import-yul-builtins-encode-selector-pure-receiver-guard': ('  unless ← isPureSelectorReceiver receiver do\n    failAt receiver "selector receiver must be a contract/interface type, this, or a local/parameter"', '  unless true do\n    failAt receiver "selector receiver must be a contract/interface type, this, or a local/parameter"'),
    'import-array-string-params-context-scalar-array-read-zero': ('            let value := Expr.calldataload (.add (.localVar arr.dataBinding) (.mul key.expr (.literal 32)))', '            let value := Expr.literal 0'),
    'import-array-string-params-context-scalar-array-length-zero': ('            let some arr := (← get).scalarArrays.find? id | failAt j "unknown scalar array parameter"\n            pure (.expr { pre, expr := .localVar arr.lengthBinding })', '            let some _arr := (← get).scalarArrays.find? id | failAt j "unknown scalar array parameter"\n            pure (.expr { pre, expr := .literal 0 })'),
    'import-array-string-params-context-selfbalance-one': ('        if ← isThisAddressConv base then\n          pure (.expr { pre := #[], expr := .selfBalance })', '        if ← isThisAddressConv base then\n          pure (.expr { pre := #[], expr := .literal 1 })'),
    'import-array-string-params-context-txorigin-zero': ('        unless member == "origin" do failAt j s!"unsupported transaction context member {member}"\n        pure (.expr { pre := #[], expr := .txOrigin })', '        unless member == "origin" do failAt j s!"unsupported transaction context member {member}"\n        pure (.expr { pre := #[], expr := .literal 0 })'),
    'import-array-string-params-context-external-balance-guard': ('        if ← isThisAddressConv base then\n          pure (.expr { pre := #[], expr := .selfBalance })\n        else\n          failAt j "external account balance reads are outside this slice"', '        if true then\n          pure (.expr { pre := #[], expr := .selfBalance })\n        else\n          failAt j "external account balance reads are outside this slice"'),
    'import-bytes-memory-encode-call-byte-buffer-length-zero': ('        let some buf ← isByteBufferIdent base\n          | failAt base "internal error: missing byte buffer"\n        pure (.expr { pre := buf.pre, expr := buf.size })', '        let some buf ← isByteBufferIdent base\n          | failAt base "internal error: missing byte buffer"\n        pure (.expr { pre := buf.pre, expr := .literal 0 })'),
    'import-bytes-memory-encode-call-signature-selector-zero': ('    let selWord := Expr.bitAnd (.keccak256 sigBuf.pointer sigBuf.size) (.literal (0xffffffff * 16 ^ 56))', '    let _ := sigBuf\n    let selWord := Expr.literal 0'),
    'import-bytes-memory-encode-call-selector-words-size': ('  pre := pre.push (.letVar sizeName (.literal (4 + 32 * words.length)))', '  pre := pre.push (.letVar sizeName (.literal (32 * words.length)))'),
    'import-bytes-memory-encode-call-bytes-concat-truncate': ('            failAt arg s!"unsupported bytes.concat argument type {argTy}"\n        return ← lowerPacked args', '            failAt arg s!"unsupported bytes.concat argument type {argTy}"\n        return ← lowerPacked (args.extract 0 1)'),
    'import-bytes-memory-encode-call-param-type-guard': ('      unless (paramType pty).isSome do\n        failAt p s!"unsupported ABI encoding argument type {pty}"\n      checkEncodingScalar arg', '      unless (paramType pty).isSome do\n        failAt p s!"unsupported ABI encoding argument type {pty}"\n      pure ()'),
    'import-dynamic-bytes-string-return-length-zero': ('let bindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding buf.size]', 'let bindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding (.literal 0)]'),
    'import-dynamic-bytes-string-return-pointer-zero': ('let bindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding buf.size]', 'let bindStmts := #[Stmt.letVar dataBinding (.literal 0), Stmt.letVar lenBinding buf.size]'),
    'import-dynamic-bytes-string-return-post-drop': ('out := (out ++ buf.pre ++ bindStmts ++ env.rootPost).push (.returnBytes memStem)', 'out := (out ++ buf.pre ++ bindStmts).push (.returnBytes memStem)'),
    'import-dynamic-bytes-string-return-string-concat-truncate': ('            failAt arg s!"unsupported string.concat argument type {argTy}"\n        return ← lowerPacked args', '            failAt arg s!"unsupported string.concat argument type {argTy}"\n        return ← lowerPacked (args.extract 0 1)'),
    'import-dynamic-bytes-string-return-memret-param-guard': ('    if rawName.startsWith "_verity_memret_" then\n      failAt p s!"parameter name {rawName} uses reserved _verity_memret_ prefix"', '    if false then\n      failAt p s!"parameter name {rawName} uses reserved _verity_memret_ prefix"'),
    'import-bytes-string-storage-length-zero': ('  return { pre := pre ++ stmts, expr := .localVar len }', '  return { pre := pre ++ stmts, expr := .literal 0 }'),
    'import-bytes-string-storage-short-read-zero': ('          [.mstore (.localVar pointer) shortWord]', '          [.mstore (.localVar pointer) (.literal 0)]'),
    'import-bytes-string-storage-long-tag-zero': ('    .setStorage name (.add (.mul (.localVar newLen) (.literal 2)) (.literal 1))', '    .setStorage name (.mul (.localVar newLen) (.literal 2))'),
    'import-bytes-string-storage-cleanup-skip': ('            .letVar clearCount (.sub (.localVar oldSlotCount) (.localVar newSlotCount)),', '            .letVar clearCount (.literal 0),'),
    'import-bytes-string-storage-shadowed-read-guard': ('    if env.duplicateLayoutLabels.contains name then\n      failAt j s!"shadowed storage declaration {name} is outside this slice"\n    if let some item := env.layoutItems.find? name then\n      unless (← mNat (← mField item "astId")) == id.toNat do\n        failAt j s!"shadowed storage declaration {name} is outside this slice"\n    let info ← resolveField name j\n    if info.bytesStorage then', '    if false then\n      failAt j s!"shadowed storage declaration {name} is outside this slice"\n    if let some item := env.layoutItems.find? name then\n      unless (← mNat (← mField item "astId")) == id.toNat do\n        failAt j s!"shadowed storage declaration {name} is outside this slice"\n    let info ← resolveField name j\n    if info.bytesStorage then'),
    'import-yul-block-mulmod-tstore-let-zero': ('        yulLocals := yulLocals.insert vname binding\n        out := out ++ v.pre |>.push (.letVar binding v.expr)', '        yulLocals := yulLocals.insert vname binding\n        out := out ++ v.pre |>.push (.letVar binding (.literal 0))'),
    'import-yul-block-mulmod-tstore-drop': ('          out := out ++ slotVal.pre ++ valVal.pre |>.push (.tstore slotVal.expr valVal.expr)', '          out := out ++ slotVal.pre ++ valVal.pre'),
    'import-yul-block-mulmod-tstore-mulmod-zero': ('  pure { pre := stmts, expr := .localVar accBinding }', '  pure { pre := stmts, expr := .literal 0 }'),
    'import-yul-block-mulmod-tstore-compound-mul-add': ('        checkedMul bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }', '        checkedAdd bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }'),
    'import-yul-block-mulmod-tstore-narrow-local-guard': ('    unless isFullWordYulScalar scalarType do\n      failAt stmt s!"Yul assignment to narrow local {vname} is unsupported"', '    unless true do\n      failAt stmt s!"Yul assignment to narrow local {vname} is unsupported"'),
    'import-merkle-and-nonces-scratch-keccak-zero': ('          pure { pre, expr := .keccak256 (.literal off) (.literal size) }', '          pure { pre, expr := .literal 0 }'),
    'import-merkle-and-nonces-mstore-drop': ('          out := out ++ valVal.pre |>.push (.mstore (.literal off) valVal.expr)', '          out := out ++ valVal.pre'),
    'import-merkle-and-nonces-incdec-op-flip': ('  let compoundOp := if operator == "++" then "+=" else "-="', '  let compoundOp := if operator == "++" then "-=" else "+="'),
    'import-merkle-and-nonces-incdec-prefix-flip': ('        return { pre := stmts, expr := if isPrefix then .localVar binding else .localVar oldVar }', '        return { pre := stmts, expr := if isPrefix then .localVar oldVar else .localVar binding }'),
    'import-merkle-and-nonces-unwritten-scratch-guard': ('          unless validScratch do\n            failAt j "keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block"', '          unless true do\n            failAt j "keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block"'),
    'import-multiproof-ratifiers-alloc-length-zero': ('      .letVar lenBinding lenVal.expr,', '      .letVar lenBinding (.literal 0),'),
    'import-multiproof-ratifiers-array-write-zero': ('            (.mstore (.add (.add (.localVar arr.memoryPointer) (.literal 32)) (.mul key.expr (.literal 32))) stored)', '            (.mstore (.add (.add (.localVar arr.memoryPointer) (.literal 32)) (.mul key.expr (.literal 32))) (.literal 0))'),
    'import-multiproof-ratifiers-bool-member-read-invert': ('  let expr := if info.booleanMembers.contains member then Expr.logicalNot (.logicalNot read) else read', '  let expr := if info.booleanMembers.contains member then Expr.logicalNot read else read'),
    'import-multiproof-ratifiers-root-named-ret-uncleaned': ('              modify fun e => { e with helperResult := some (rbinding, rty), helperReturnId := some rid }', '              modify fun e => { e with helperResult := some (rbinding, "uint256"), helperReturnId := some rid }'),
    'import-multiproof-ratifiers-stateful-array-index-guard': ('          if !key.pre.isEmpty && (statefulCallIn indexExpression (← get) || !pre.isEmpty) then', '          if false then'),
    'import-udvt-param-hashmarket-udvt-zero': ('            let arg := args[0]!\n            return ← convert uTy (← mType arg) (← lowerExpr arg) arg', '            let arg := args[0]!\n            return { pre := (← lowerExpr arg).pre, expr := .literal 0 }'),
    'import-udvt-param-hashmarket-root-param-init-zero': ('        let pbinding ← freshFor (if p.name == "" then "param" else p.name)\n        let pexpr := Expr.localVar pbinding\n        rootInit := rootInit.push (.letVar pbinding initExpr)', '        let pbinding ← freshFor (if p.name == "" then "param" else p.name)\n        let pexpr := Expr.localVar pbinding\n        let _ := initExpr\n        rootInit := rootInit.push (.letVar pbinding (.literal 0))'),
    'import-udvt-param-hashmarket-array-keccak-zero': ('  return some (.add (.localVar arrayPtr) (.literal 32), .mul (.mload (.localVar arrayPtr)) (.literal 32))', '  return some (.add (.localVar arrayPtr) (.literal 32), .literal 0)'),
    'import-udvt-param-hashmarket-chained-multi-ret-zero': ('            for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              let (valExpr, _) := retExprs.getD i (.literal 0, "")\n              pre := pre.push (.assignVar binding valExpr)', '            for i in [:results.size] do\n              let (binding, _, _) := results[i]!\n              let (_valExpr, _) := retExprs.getD i (.literal 0, "")\n              pre := pre.push (.assignVar binding (.literal 0))'),
    'import-udvt-param-hashmarket-mismatched-keccak-guard': ('  unless arrFromSize? == some arrName do return none', '  unless arrFromSize?.isSome do return none'),
    'import-struct-mapping-bytes4-interfaceid-leaf-slot-zero': ('  return (baseStmts ++ leafStmts, .localVar leafSlot)', '  return (baseStmts ++ leafStmts, .literal 0)'),
    'import-struct-mapping-bytes4-interfaceid-xor-zero': ('      acc := Nat.xor acc word', '      let _ := word\n      acc := 0'),
    'import-struct-mapping-bytes4-interfaceid-uint32-shift-drop': ('    let shifted := Stmt.letVar dest (.shr (.literal 224) a.expr)', '    let shifted := Stmt.letVar dest a.expr'),
    'import-struct-mapping-bytes4-interfaceid-calldata-guard-drop': ('        if env.bytes4Params.contains p.id then', '        if false && env.bytes4Params.contains p.id then'),
    'import-struct-mapping-bytes4-interfaceid-int-const-cmp-guard': ('    unless leftTy == "bytes4" && rightTy == "bytes4" do\n      failAt j "implicit constant conversion to bytes4 is outside this slice"', '    unless true do\n      failAt j "implicit constant conversion to bytes4 is outside this slice"'),
    'import-erc2981-holders-arrays-msghash-whole-struct-write-zero': ('    let stored := if info.booleanMembers.contains mName then Expr.logicalNot (.logicalNot mExpr) else mExpr\n    out := out.push (writeMember mName stored)', '    let _ := mExpr\n    out := out.push (writeMember mName (.literal 0))'),
    'import-erc2981-holders-arrays-msghash-selector-zero': ('      word := word * 16 + digit\n    return .expr { pre := #[], expr := .literal (word * 16 ^ 56) }', '      word := word * 16 + digit\n    let _ := word\n    return .expr { pre := #[], expr := .literal 0 }'),
    'import-erc2981-holders-arrays-msghash-yul-array-load-index-zero': ('  return some {\n    pre := posVal.pre,\n    expr := .mload (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul posVal.expr (.literal 32)))\n  }', '  return some {\n    pre := posVal.pre,\n    expr := .mload (.add (.localVar arrayPtr) (.literal 32))\n  }'),
    'import-erc2981-holders-arrays-msghash-prefix-keccak-zero': ('    let keccakExpr := Expr.keccak256 (.literal 0) (.literal (prefixLen + 32))\n    let assignStmt ← lowerYulDirectAssignmentTarget j stmts[2]! varNode refs retName { pre := #[], expr := keccakExpr }', '    let _ := prefixLen\n    let assignStmt ← lowerYulDirectAssignmentTarget j stmts[2]! varNode refs retName { pre := #[], expr := .literal 0 }'),
    'import-erc2981-holders-arrays-msghash-flat-struct-aliasing-guard': ('      unless allowFlatLocalSource do\n        failAt j "memory struct local aliasing is outside this slice"', '      unless true || allowFlatLocalSource do\n        failAt j "memory struct local aliasing is outside this slice"'),
    'import-storage-struct-params-deque-shortstrings-flat-member-zero': ('        for (mName, mTy, mExpr) in memberVals do\n          let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"\n          pre := pre.push (.letVar binding mExpr)', '        for (mName, mTy, _mExpr) in memberVals do\n          let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"\n          pre := pre.push (.letVar binding (.literal 0))'),
    'import-storage-struct-params-deque-shortstrings-storage-to-mem-zero': ('            let readVal ← atom (← memberRead #[] path mName p)\n            let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"\n            pre := pre ++ readVal.pre |>.push (.letVar binding readVal.expr)', '            let readVal ← atom (← memberRead #[] path mName p)\n            let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"\n            pre := pre ++ readVal.pre |>.push (.letVar binding (.literal 0))'),
    'import-storage-struct-params-deque-shortstrings-bytes-to-fixed-zero': ('    .letVar word (.bitAnd (.mload (.localVar ptr)) (.literal fullMask)),', '    .letVar word (.literal 0),'),
    'import-storage-struct-params-deque-shortstrings-compound-mapping-rhs-zero': ('      let lhsVal ← readStructMappingElement pre path mapInfo key target\n      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression\n      let writeStmts ← writeStructMappingElement #[] path mapInfo key combined.expr false target', '      let lhsVal ← readStructMappingElement pre path mapInfo key target\n      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression\n      let _ := combined.expr\n      let writeStmts ← writeStructMappingElement #[] path mapInfo key (.literal 0) false target'),
    'import-storage-struct-params-deque-shortstrings-reassigned-storage-param-guard': ('        if location == "storage" then\n          if (bodyAssignedIds body).contains pid then\n            failAt p "reassigned storage struct parameters are outside this slice"', '        if location == "storage" then\n          if false then\n            failAt p "reassigned storage struct parameters are outside this slice"'),
    'import-storage-slot-short-strings-time-raw-packed-read-shift-zero': ('  let shifted := if mInfo.byteOffset == 0 then rawWord else Expr.shr (.literal (mInfo.byteOffset * 8)) rawWord', '  let shifted := if true || mInfo.byteOffset == 0 then rawWord else Expr.shr (.literal (mInfo.byteOffset * 8)) rawWord'),
    'import-storage-slot-short-strings-time-raw-scalar-write-zero': ('  if mInfo.bitWidth == 256 && mInfo.byteOffset == 0 then\n    return pre.push (.setStorageArrayElement rawStorageFieldName wordSlot cleanVal)', '  if mInfo.bitWidth == 256 && mInfo.byteOffset == 0 then\n    let _ := cleanVal\n    return pre.push (.setStorageArrayElement rawStorageFieldName wordSlot (.literal 0))'),
    'import-storage-slot-short-strings-time-raw-mapping-slot-zero': ('    let raw := Expr.storageArrayElement rawStorageFieldName (.localVar leafSlot)', '    let raw := Expr.storageArrayElement rawStorageFieldName (.literal 0)'),
    'import-storage-slot-short-strings-time-short-string-word-zero': ('  ] ++ allocStmts.toArray ++ #[\n    .mstore (.localVar ptr) (.localVar wordBinding)\n  ]', '  ] ++ allocStmts.toArray ++ #[\n    .mstore (.localVar ptr) (.literal 0)\n  ]'),
    'import-storage-slot-short-strings-time-bytes-slot-wrapper-guard': ('                  unless sMembers.size == 1 do\n                    failAt r "StorageSlot bytes/string wrapper struct must have a single value member"', '                  unless true do\n                    failAt r "StorageSlot bytes/string wrapper struct must have a single value member"'),
    'import-enumerable-set-map-storage-arrays-push-len-no-inc': ('    .letVar newLen (.add lenVal.expr (.literal 1)),', '    .letVar newLen lenVal.expr,'),
    'import-enumerable-set-map-storage-arrays-pop-clear-skip': ('  let clearStmts ← writeStorageDynamicArrayElementAtUnchecked baseDataSlot elemTy (.localVar newLen) (.literal 0) true', '  let clearStmts : Array Stmt := #[]'),
    'import-enumerable-set-map-storage-arrays-read-elem-zero': ('    .letVar dest cleaned\n  ]\n  pure { pre := lenVal.pre ++ stmts, expr := .localVar dest }', '    .letVar dest cleaned\n  ]\n  pure { pre := lenVal.pre ++ stmts, expr := .literal 0 }'),
    'import-enumerable-set-map-storage-arrays-copy-to-mem-elem-zero': ('  let elemVal := if isBool then Expr.logicalNot (.logicalNot masked) else masked', '  let _ := isBool\n  let _ := masked\n  let elemVal := Expr.literal 0'),
    'import-enumerable-set-map-storage-arrays-reassigned-param-guard': ('    unless info.structDynamicArrays.isEmpty do\n      failAt target "cannot delete mapping struct with dynamic-array members"', '    unless true do\n      failAt target "cannot delete mapping struct with dynamic-array members"'),
    'import-checkpoints-and-struct-arrays-struct-push-len-no-inc': ('  let wordOff := if rawInfo.wordCount == 1 then lenVal.expr else Expr.mul lenVal.expr (.literal rawInfo.wordCount)\n  let mut stmts : Array Stmt := #[\n    .letVar newLen (.add lenVal.expr (.literal 1)),', '  let wordOff := if rawInfo.wordCount == 1 then lenVal.expr else Expr.mul lenVal.expr (.literal rawInfo.wordCount)\n  let mut stmts : Array Stmt := #[\n    .letVar newLen lenVal.expr,'),
    'import-checkpoints-and-struct-arrays-named-ctor-zero': ('        evaluatedByName := evaluatedByName.push (argName, mTy, normVal.expr)', '        let _ := normVal.expr\n        evaluatedByName := evaluatedByName.push (argName, mTy, .literal 0)'),
    'import-checkpoints-and-struct-arrays-bsearch-iters-zero': ('            return #[.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]]', '            let _ := bits\n            return #[.forEach loopVar (.literal 0) [.ite condVal.expr bodyOut.toList []]]'),
    'import-checkpoints-and-struct-arrays-unsafe-access-prefix-skip': ('          let prefixPre ← lowerYulStmtSlice s prefixYstmts refs ""\n          let slotVal ← lowerYul rhs', '          let _ ← lowerYulStmtSlice s prefixYstmts refs ""\n          let prefixPre : Array Stmt := #[]\n          let slotVal ← lowerYul rhs'),
    'import-checkpoints-and-struct-arrays-named-ctor-stateful-guard': ('        if statefulCallIn arg (← get) || assignmentIn arg then\n          failAt j "named struct constructor with stateful or assignment argument is outside this slice"', '        if false then\n          failAt j "named struct constructor with stateful or assignment argument is outside this slice"'),
    'import-ticklib-and-three-key-mapping-signflip-result-zero': ('  let result ← lowerHelper falseStmts retName\n  let finalResult : Val := { pre := pre ++ result.pre, expr := result.expr }', '  let result ← lowerHelper falseStmts retName\n  let finalResult : Val := { pre := pre ++ result.pre, expr := .literal 0 }'),
    'import-ticklib-and-three-key-mapping-top-fixed-write-zero': ('      let (name, count, write) ← match path with\n        | .zero name => pure (name, 0, fun member value => Stmt.setStorage (topStructMemberFieldName (splitSPathField name).1 member) value)', '      let (name, count, write) ← match path with\n        | .zero name => pure (name, 0, fun (member : String) (_value : Expr) => Stmt.setStorage (topStructMemberFieldName (splitSPathField name).1 member) (.literal 0))'),
    'import-ticklib-and-three-key-mapping-top-fixed-copy-zero': ('        let (field, count, read) ← match path with\n          | .zero field => pure (field, 0, fun member => Expr.storage (topStructMemberFieldName (splitSPathField field).1 member))', '        let (field, count, read) ← match path with\n          | .zero field => pure (field, 0, fun (_member : String) => Expr.literal 0)'),
    'import-ticklib-and-three-key-mapping-top-fixed-delete-skip': ('      let mut out := pre\n      for i in [:length] do\n        out := out.push (writeMember s!"__solidity_element_{i}" (.literal 0))\n      return out', '      let _ := length\n      let out := pre\n      return out'),
    'import-ticklib-and-three-key-mapping-while-neq-zero-low-guard': ('            if condOp == "!=" && !env.zeroInitLocals.contains lowId then\n              failAt cond "binary-search while (low != high) requires low to be zero at loop entry"', '            if false then\n              failAt cond "binary-search while (low != high) requires low to be zero at loop entry"'),
    'import-offer-hash-domain-sep-uninit-bytes-size': ('      let effects : Array Stmt := #[.letVar pointer (.literal 96), .letVar size (.literal 0)]', '      let effects : Array Stmt := #[.letVar pointer (.literal 96), .letVar size (.literal 32)]'),
    'import-offer-hash-domain-sep-bytes-concat-reassign-size-zero': ('            if let (.localVar ptrBinding, .localVar sizeBinding) := (buf.pointer, buf.size) then\n              let rhsBuf ← lowerEncodedBytes right\n              return rhsBuf.pre ++ #[.assignVar ptrBinding rhsBuf.pointer, .assignVar sizeBinding rhsBuf.size]', '            if let (.localVar ptrBinding, .localVar sizeBinding) := (buf.pointer, buf.size) then\n              let rhsBuf ← lowerEncodedBytes right\n              return rhsBuf.pre ++ #[.assignVar ptrBinding rhsBuf.pointer, .assignVar sizeBinding (.literal 0)]'),
    'import-offer-hash-domain-sep-mem-bytes-field-len-zero': ('          let loadStmts : Array Stmt := #[\n            .letVar bytesPtr (.mload (.add (.localVar (mem.abiStem ++ "_memory")) (.literal (32 * memberIndex)))),\n            .letVar length (.mload (.localVar bytesPtr))\n          ]', '          let loadStmts : Array Stmt := #[\n            .letVar bytesPtr (.mload (.add (.localVar (mem.abiStem ++ "_memory")) (.literal (32 * memberIndex)))),\n            .letVar length (.literal 0)\n          ]'),
    'import-offer-hash-domain-sep-cd-bytes-field-len-zero': ('            if mem.calldataLocation then\n              let header ← fresh\n              let length ← fresh\n              let data ← fresh\n              let checks := AbiLowering.calldataBytesFieldHead\n                (.localVar (mem.abiStem ++ "_calldata")) memberIndex header length data\n              return .expr { pre := pre ++ checks.toArray, expr := .localVar length }', '            if mem.calldataLocation then\n              let header ← fresh\n              let length ← fresh\n              let data ← fresh\n              let checks := AbiLowering.calldataBytesFieldHead\n                (.localVar (mem.abiStem ++ "_calldata")) memberIndex header length data\n              return .expr { pre := pre ++ checks.toArray, expr := .literal 0 }'),
    'import-offer-hash-domain-sep-encoding-custom-revert-guard': ('            if fnHasCustomRevert env targetId then\n              failAt j "effectful ABI encoding argument is unsupported"', '            if false && fnHasCustomRevert env targetId then\n              failAt j "effectful ABI encoding argument is unsupported"'),
    'import-abi-decode-ratifier-bool-guard-skip': ('  else if ty == "bool" then\n    some (AbiLowering.guard (.lt word (.literal 2)))', '  else if ty == "bool" then\n    none'),
    'import-abi-decode-ratifier-struct-member-offset-zero': ('        for mIdx in [:members.size] do\n          let (mName, mTy) := members[mIdx]!\n          let wordVar ← fresh\n          let off := headCursor + 32 * mIdx', '        for mIdx in [:members.size] do\n          let (mName, mTy) := members[mIdx]!\n          let wordVar ← fresh\n          let off := headCursor'),
    'import-abi-decode-ratifier-array-copy-skip': ('        let loopBody : List Stmt :=\n          [ .letVar elemVal (readAbiDecodeWord fromCalldata elemAddr) ] ++\n          elemChecks ++\n          [ .mstore (.add (.add (.localVar arrPtr) (.literal 32)) (.mul (.localVar copyIdx) (.literal 32))) (.localVar elemVal) ]\n        pre := pre.push (.forEach copyIdx (.localVar arrLen) loopBody)', '        let loopBody : List Stmt :=\n          [ .letVar elemVal (readAbiDecodeWord fromCalldata elemAddr) ] ++\n          elemChecks ++\n          [ .mstore (.add (.add (.localVar arrPtr) (.literal 32)) (.mul (.localVar copyIdx) (.literal 32))) (.localVar elemVal) ]\n        let _ := (copyIdx, loopBody)'),
    'import-abi-decode-ratifier-dynamic-bytes-len-zero': ('        let buf : EncodedBytes := {\n          pre := #[]\n          pointer := .add (.localVar bytesPointer) (.literal 32)\n          size := .localVar byteLen\n        }', '        let buf : EncodedBytes := {\n          pre := #[]\n          pointer := .add (.localVar bytesPointer) (.literal 32)\n          size := .literal 0\n        }'),
    'import-abi-decode-ratifier-struct-enum-member-guard': ('      unless !mTy.startsWith "enum " && (paramType mTy).isSome do\n        failAt mNode s!"unsupported abi.decode struct member type {mTy}"', '      unless (paramType mTy).isSome do\n        failAt mNode s!"unsupported abi.decode struct member type {mTy}"'),
    'import-votes-checkpoints-arrays-bitmaps-fnptr-param-branch-invert': ('        modify fun e =>\n          { e with fnPtrs := e.fnPtrs.insert pid ptr }', '        let collapsed := match ptr with | .branch _ t _ => FnPtr.direct t | p => p\n        modify fun e =>\n          { e with fnPtrs := e.fnPtrs.insert pid collapsed }'),
    'import-votes-checkpoints-arrays-bitmaps-discarded-fnptr-skip': ('        else if arity > 1 then\n          let (multiPre, _) ← lowerMultiCall expression\n          return multiPre\n        else\n          let result ← atom (← lowerCall expression)\n          return result.pre', '        else if arity > 1 then\n          let (multiPre, _) ← lowerMultiCall expression\n          return multiPre\n        else\n          let _ ← atom (← lowerCall expression)\n          return #[]'),
    'import-votes-checkpoints-arrays-bitmaps-root-struct-return-zero': ('            for (_, _, valExpr) in memberVals do\n              if env.rootPost.isEmpty then\n                exprs := exprs.push valExpr', '            for (_, _, valExpr) in memberVals do\n              if env.rootPost.isEmpty then\n                exprs := exprs.push (.literal 0)'),
    'import-votes-checkpoints-arrays-bitmaps-reassigned-fnptr-param-guard': ('    else if let some (_, _, _, _, memberSpecs) := flatStructRet? then\n      if stmts.isEmpty then', '    else if let some (_, _, _, _, memberSpecs) := flatStructRet? then\n      if true || stmts.isEmpty then'),
})

def run(directory, output, name):
    fixture = "StorageVoidSequence" if name == "import-void-fallthrough" else "StorageSequence"
    if name.startswith("import-votes-checkpoints-arrays-bitmaps-"):
        fixture = "VotesCheckpointsArraysBitMapsSequence"
    if name.startswith("import-abi-decode-ratifier-"):
        fixture = "AbiDecodeAndRatifierSequence"
    if name.startswith("import-offer-hash-domain-sep-"):
        fixture = "OfferHashAndDomainSeparatorSequence"
    if name.startswith("import-ticklib-and-three-key-mapping-"):
        fixture = "TickLibAndThreeKeyMappingSequence"
    if name.startswith("import-checkpoints-and-struct-arrays-"):
        fixture = "CheckpointsAndStructArraysSequence"
    if name.startswith("import-enumerable-set-map-storage-arrays-"):
        fixture = "EnumerableSetMapSequence"
    if name.startswith("import-storage-slot-short-strings-time-"):
        fixture = "StorageSlotShortStringsTimeSequence"
    if name.startswith("import-storage-struct-params-deque-shortstrings-"):
        fixture = "StorageStructParamsDequeShortStringsSequence"
    if name.startswith("import-erc2981-holders-arrays-msghash-"):
        fixture = "ERC2981HoldersArraysMsgHashSequence"
    if name.startswith("import-struct-mapping-bytes4-interfaceid-"):
        fixture = "StructMappingAndBytes4InterfaceSequence"
    if name.startswith("import-udvt-param-hashmarket-"):
        fixture = "UdvtParamAssignHashMarketSequence"
    if name.startswith("import-multiproof-ratifiers-"):
        fixture = "MultiProofMappingKeysRatifiersSequence"
    if name.startswith("import-merkle-and-nonces-"):
        fixture = "MerkleAndNoncesSequence"
    if name.startswith("import-yul-block-mulmod-tstore-"):
        fixture = "YulBlockMulmodTstoreSequence"
    if name.startswith("import-bytes-string-storage-"):
        fixture = "BytesAndStringStorageSequence"
    if name.startswith("import-dynamic-bytes-string-return-"):
        fixture = "DynamicBytesAndStringReturnSequence"
    if name.startswith("import-bytes-memory-encode-call-"):
        fixture = "BytesMemoryAndAbiEncodeCallSequence"
    if name.startswith("import-array-string-params-context-"):
        fixture = "ArrayStringParamsAndContextSequence"
    if name.startswith("import-yul-builtins-encode-selector-"):
        fixture = "YulBuiltinsAndEncodeSelectorSequence"
    if name.startswith("import-while-clz-struct-loc-"):
        fixture = "WhileClzAndStructLocSequence"
    if name.startswith("import-exp-and-bitwise-shift-"):
        fixture = "ExpAndBitwiseShiftSequence"
    if name.startswith("import-msg-data-and-enum-"):
        fixture = "MsgDataAndEnumSequence"
    if name.startswith("import-struct-fixed-array-"):
        fixture = "StructFixedArrayAndFixedReturnSequence"
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
            '--transactions', '64' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'} else '3',
            '--seed', '2490' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'} else '2453', '--shrink-attempts', '100' if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'} else '30',
            '--output', str(output)]
    if fixture in {'MappingFixedArraySequence', 'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'}:
        argv.extend(['--change-prefix', *map(str, list(range(9)) + ([19, 20, 21, 25, 30, 40] if fixture in {'FixedArrayWriteOrderSequence', 'DiscardedHelperSequence', 'EncodedByteLocalSequence', 'NamedHelperReturnSequence', 'YulNumericSequence', 'Solc0810Sequence', 'InheritanceSequence', 'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'EmptyArrayReturnBytesCalldataSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'} else [65535, 65536]) + [(1 << 256) - 1])])
    if fixture == 'Solc0810Sequence':
        argv = argv[:argv.index('--change-prefix')] + ['--solc-version', '0.8.10', '--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 100, 1000, 50000, 100000, 999999, (1 << 256) - 1])]
    if fixture == 'YulNumericSequence':
        argv = argv[:argv.index('--change-prefix')] + ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 32, 33, 255, 256, (1 << 255) - 1, 1 << 255, (1 << 256) - 2, (1 << 256) - 1])]
    if fixture == 'NamedHelperReturnSequence':
        prefix = argv.index('--change-prefix')
        argv = argv[:prefix] + ['--change-prefix', *map(str, [0, 1, 2, 3, 19, 20, 21, 30, 31, 40, 50, 60, 70, 255, 256, 257, (1 << 160) - 1, 1 << 160, (1 << 160) + 1, (1 << 256) - 1])]
    if fixture in {'VoidHelperGuardSequence', 'ModifierUncheckedCompoundSequence', 'TupleHelperSequence', 'Int256ContractTypeSequence', 'FnPtrStructDeleteModifierSequence', 'OverloadConstErrorCondTupleTloadSequence', 'StructFixedArrayAndFixedReturnSequence', 'MsgDataAndEnumSequence', 'ExpAndBitwiseShiftSequence', 'WhileClzAndStructLocSequence', 'YulBuiltinsAndEncodeSelectorSequence', 'ArrayStringParamsAndContextSequence', 'BytesMemoryAndAbiEncodeCallSequence', 'DynamicBytesAndStringReturnSequence', 'BytesAndStringStorageSequence', 'YulBlockMulmodTstoreSequence', 'MerkleAndNoncesSequence', 'MultiProofMappingKeysRatifiersSequence', 'UdvtParamAssignHashMarketSequence', 'StructMappingAndBytes4InterfaceSequence', 'ERC2981HoldersArraysMsgHashSequence', 'StorageStructParamsDequeShortStringsSequence', 'StorageSlotShortStringsTimeSequence', 'EnumerableSetMapSequence', 'CheckpointsAndStructArraysSequence', 'TickLibAndThreeKeyMappingSequence', 'OfferHashAndDomainSeparatorSequence', 'AbiDecodeAndRatifierSequence', 'VotesCheckpointsArraysBitMapsSequence'}:
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
 struct S { uint256 a; int128[] dyn; }
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
    elif name == 'import-struct-fixed-array-delete-guard':
        diagnostic = 'cannot delete mapping struct with fixed-array members'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct S { uint256 a; uint128[4] arr; }
 mapping(uint256 => S) private m;
 function checked(uint256 x) external returns (uint256) {
  delete m[x];
  return m[x].a;
 }
}
''')
    elif name == 'import-msg-data-and-enum-encoding-cast-guard':
        diagnostic = 'fallible enum conversion in ABI encoding argument is unsupported'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 enum Mode { A, B }
 function checked(uint256 x) external pure returns (bytes32) {
  return keccak256(abi.encode(Mode(x)));
 }
}
''')
    elif name == 'import-exp-and-bitwise-shift-dynamic-exp-guard':
        diagnostic = 'checked exponentiation with dynamic base and exponent is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  return x ** x;
 }
}
''')
    elif name == 'import-while-clz-struct-loc-nondecreasing-guard':
        diagnostic = 'while loop update is not a recognized bounded bit-clearing or right-shift step'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  uint256 v = x;
  while (v != 0) {
   v += 1;
  }
  return v;
 }
}
''')
    elif name == 'import-yul-builtins-encode-selector-pure-receiver-guard':
        diagnostic = 'selector receiver must be a contract/interface type, this, or a local/parameter'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
interface IERC20 { function transfer(address to, uint256 amount) external returns (bool); }
contract C {
 IERC20 public token;
 function checked(uint256 x) external view returns (bytes32) {
  return keccak256(abi.encodeWithSelector(token.transfer.selector, address(0), x));
 }
}
''')
    elif name == 'import-array-string-params-context-external-balance-guard':
        diagnostic = 'external account balance reads are outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external view returns (uint256) {
  return address(uint160(x)).balance;
 }
}
''')
    elif name == 'import-bytes-memory-encode-call-param-type-guard':
        diagnostic = 'effectful ABI encoding argument is unsupported'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
interface IBad { function f(uint256 a) external; }
contract C {
 function checked(uint256 x) external pure returns (bytes32) {
  return keccak256(abi.encodeCall(IBad.f, (x + 1)));
 }
}
''')
    elif name == 'import-dynamic-bytes-string-return-memret-param-guard':
        diagnostic = 'parameter name _verity_memret_x uses reserved _verity_memret_ prefix'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 _verity_memret_x) external pure returns (uint256) {
  return _verity_memret_x;
 }
}
''')
    elif name == 'import-bytes-string-storage-shadowed-read-guard':
        diagnostic = 'shadowed storage declaration dup is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
abstract contract Base { string private dup; }
contract C is Base {
 string private dup;
 function checked(uint256) external view returns (bytes32) {
  return keccak256(bytes(dup));
 }
}
''')
    elif name == 'import-yul-block-mulmod-tstore-narrow-local-guard':
        diagnostic = 'Yul assignment to narrow local narrow is unsupported'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  uint128 narrow = uint128(x);
  assembly { narrow := add(narrow, 1) }
  return uint256(narrow);
 }
}
''')
    elif name == 'import-merkle-and-nonces-unwritten-scratch-guard':
        diagnostic = 'keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  uint256 out = 0;
  assembly {
   mstore(0x00, x)
   out := keccak256(0x00, 0x40)
  }
  return out;
 }
}
''')
    elif name == 'import-multiproof-ratifiers-stateful-array-index-guard':
        diagnostic = 'stateful or assignment array index is unsupported'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 uint256 private s;
 function bump(uint256 x) internal returns (uint256) { s = x + 1; return 0; }
 function checked(uint256 x) external returns (uint256) {
  uint256[] memory a = new uint256[](1);
  return a[bump(x)];
 }
}
''')
    elif name == 'import-udvt-param-hashmarket-mismatched-keccak-guard':
        diagnostic = 'unbound Yul identifier a'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (bytes32 h) {
  uint256[] memory a = new uint256[](1);
  uint256[] memory b = new uint256[](1);
  a[0] = x;
  b[0] = x;
  assembly ("memory-safe") {
   h := keccak256(add(a, 0x20), mul(mload(b), 0x20))
  }
 }
}
''')
    elif name == 'import-struct-mapping-bytes4-interfaceid-int-const-cmp-guard':
        diagnostic = 'implicit constant conversion to bytes4 is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 x) external pure returns (uint256) {
  bytes4 sel = bytes4(uint32(x));
  return sel == 0x01ffc9a7 ? 1 : 0;
 }
}
''')
    elif name == 'import-erc2981-holders-arrays-msghash-flat-struct-aliasing-guard':
        diagnostic = 'memory struct local aliasing is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct Box { uint128 a; uint128 b; }
 function checked(uint256 x) external pure returns (uint256) {
  Box memory b1 = Box(uint128(x), 2);
  Box memory b2 = Box(3, 4);
  b2 = b1;
  return uint256(b2.a);
 }
}
''')
    elif name == 'import-storage-struct-params-deque-shortstrings-reassigned-storage-param-guard':
        diagnostic = 'reassigned storage struct parameters are outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct Box { uint128 a; uint128 b; }
 Box private _box;
 function _bad(Box storage b) internal returns (uint256) {
  b = _box;
  return uint256(b.a);
 }
 function checked(uint256) external returns (uint256) {
  return _bad(_box);
 }
}
''')
    elif name == 'import-storage-slot-short-strings-time-bytes-slot-wrapper-guard':
        diagnostic = 'StorageSlot bytes/string wrapper struct must have a single value member'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct BadSlot { string value; uint256 extra; }
 string private _s;
 function _slot(string storage store) internal pure returns (BadSlot storage r) {
  assembly ("memory-safe") { r.slot := store.slot }
 }
 function checked(uint256) external view returns (uint256) {
  return bytes(_slot(_s).value).length;
 }
}
''')
    elif name == 'import-enumerable-set-map-storage-arrays-reassigned-param-guard':
        diagnostic = 'cannot delete mapping struct with dynamic-array members'
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
    elif name == 'import-checkpoints-and-struct-arrays-named-ctor-stateful-guard':
        diagnostic = 'named struct constructor with stateful or assignment argument is outside this slice'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct Box { uint128 a; uint128 b; }
 function checked(uint256 x) external pure returns (uint256) {
  Box memory b1 = Box({b: 2, a: uint128(x = x + 1)});
  return uint256(b1.a);
 }
}
''')
    elif name == 'import-ticklib-and-three-key-mapping-while-neq-zero-low-guard':
        diagnostic = 'binary-search while (low != high) requires low to be zero at loop entry'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 function checked(uint256 target) external pure returns (uint256) {
  uint256 low = 1;
  uint256 high = 16;
  while (low != high) {
   uint256 mid = (low + high) >> 1;
   if (mid > target) {
    high = mid;
   } else {
    low = mid + 1;
   }
  }
  return low;
 }
}
''')
    elif name == 'import-offer-hash-domain-sep-encoding-custom-revert-guard':
        diagnostic = 'effectful ABI encoding argument is unsupported'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 error Bad();
 function _mayRevert(uint256 x) internal pure returns (uint256) {
  if (x == 99) revert Bad();
  return x;
 }
 function checked(uint256 x) external pure returns (uint256) {
  return uint256(keccak256(abi.encode(_mayRevert(x))));
 }
}
''')
    elif name == 'import-abi-decode-ratifier-struct-enum-member-guard':
        diagnostic = 'unsupported abi.decode struct member type enum C.Mode'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 enum Mode { Off, On }
 struct S { Mode m; }
 function checked(uint256 x) external pure returns (uint256) {
  bytes memory buf = abi.encode(x);
  S memory s = abi.decode(buf, (S));
  return uint256(s.m);
 }
}
''')
    elif name == 'import-votes-checkpoints-arrays-bitmaps-reassigned-fnptr-param-guard':
        diagnostic = 'an explicit root return is required'
        (target / 'Fixture.sol').write_text('''pragma solidity 0.8.34;
contract C {
 struct S { uint256 a; uint256 b; }
 uint256 private v;
 function checked(uint256 x) external returns (S memory) {
  v = x;
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
        try:
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
                                  'import-overload-const-error-cond-tuple-tload-nonconst-error-guard',
                                  'import-struct-fixed-array-delete-guard',
                                  'import-msg-data-and-enum-encoding-cast-guard',
                                  'import-exp-and-bitwise-shift-dynamic-exp-guard',
                                  'import-while-clz-struct-loc-nondecreasing-guard',
                                  'import-yul-builtins-encode-selector-pure-receiver-guard',
                                  'import-array-string-params-context-external-balance-guard',
                                  'import-bytes-memory-encode-call-param-type-guard',
                                  'import-dynamic-bytes-string-return-memret-param-guard',
                                  'import-bytes-string-storage-shadowed-read-guard',
                                  'import-yul-block-mulmod-tstore-narrow-local-guard',
                                  'import-merkle-and-nonces-unwritten-scratch-guard',
                                  'import-multiproof-ratifiers-stateful-array-index-guard',
                                  'import-udvt-param-hashmarket-mismatched-keccak-guard',
                                  'import-struct-mapping-bytes4-interfaceid-int-const-cmp-guard',
                                  'import-erc2981-holders-arrays-msghash-flat-struct-aliasing-guard',
                                  'import-storage-struct-params-deque-shortstrings-reassigned-storage-param-guard',
                                  'import-storage-slot-short-strings-time-bytes-slot-wrapper-guard',
                                  'import-enumerable-set-map-storage-arrays-reassigned-param-guard',
                                  'import-checkpoints-and-struct-arrays-named-ctor-stateful-guard',
                                  'import-ticklib-and-three-key-mapping-while-neq-zero-low-guard',
                                  'import-offer-hash-domain-sep-encoding-custom-revert-guard',
                                  'import-abi-decode-ratifier-struct-enum-member-guard',
                                  'import-votes-checkpoints-arrays-bitmaps-reassigned-fnptr-param-guard'}
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
        finally:
            release(directory)
        reports.append({'mutant': name, 'status': 'detected', 'detected': True, 'baselinePassed': True,
                        'witness': reduced, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}


def main():
    selected = None
    if len(sys.argv) == 3 and sys.argv[1] == '--only':
        pattern = sys.argv[2]
        selected = [name for name in MUTANTS if pattern in name]
        if not selected:
            raise HarnessError(f'no mutants matched --only {pattern}')
    elif len(sys.argv) != 1:
        raise HarnessError(f'unexpected arguments: {sys.argv[1:]}')
    output = Path(tempfile.mkdtemp(prefix='storage-mutations-', dir='.lake')).resolve()
    mutation_campaign(output, selected=selected)
    print(output)


if __name__ == '__main__':
    main()
