import TranslationValidationMemoryGuardExtension
import Lean
import EvmYul.Yul.Ast

namespace SolidityTranslationValidation.AstBridge.Dispatcher
open Lean

private def textField (node : Json) (name : String) : Except String String := do
  (← node.getObjVal? name).getStr?

private def keys (node : Json) (allowed : List String) : Except String Unit := do
  let obj ← node.getObj?
  for (name, _) in obj.toList do
    unless allowed.contains name do throw s!"unknown AST field {name}"
  for name in ["src", "nativeSrc"] do
    let _ ← textField node name

private def numeral (raw : String) : Except String Nat := do
  let chars := raw.toList
  let (base, digits) := if chars.take 2 == ['0', 'x'] then (16, chars.drop 2) else (10, chars)
  unless !digits.isEmpty do throw "empty Yul numeral"
  let value ← digits.foldlM (init := 0) fun acc c => do
    let d := ("0123456789abcdef".toList.idxOf c.toLower)
    unless d < base do throw "invalid Yul numeral digit"
    pure (acc * base + d)
  unless value < 2^256 do throw "Yul numeral exceeds one word"
  pure value

/-- Native expressions used in the captured dispatcher. This separate decoder
retains the old arithmetic-only decoder unchanged. Void
builtins have a separate statement decoder and cannot be nested expressions. -/
def decodeExpr : Nat → Json → Except String EvmYul.Yul.Ast.Expr
  | 0, _ => .error "AST decoding fuel exhausted"
  | fuel + 1, node => do
    match ← textField node "nodeType" with
    | "YulIdentifier" =>
      keys node ["nodeType", "name", "src", "nativeSrc"]
      let name ← textField node "name"
      unless !name.isEmpty do throw "empty Yul identifier"
      pure (.Var name)
    | "YulFunctionCall" =>
      keys node ["nodeType", "functionName", "arguments", "src", "nativeSrc"]
      let callee ← node.getObjVal? "functionName"
      keys callee ["nodeType", "name", "src", "nativeSrc"]
      unless (← textField callee "nodeType") == "YulIdentifier" do
        throw "Yul callee is not an identifier"
      let name ← textField callee "name"
      let (prim, arity) : EvmYul.Operation .Yul × Nat ← match name with
        | "calldataload" => pure (.CALLDATALOAD, 1)
        | "calldatasize" => pure (.CALLDATASIZE, 0)
        | "callvalue" => pure (.CALLVALUE, 0)
        | "lt" => pure (.LT, 2)
        | "slt" => pure (.SLT, 2)
        | "shr" => pure (.SHR, 2)
        | "add" => pure (.ADD, 2)
        | "not" => pure (.NOT, 1)
        | "mul" => pure (.MUL, 2)
        | "div" => pure (.DIV, 2)
        | "eq" => pure (.EQ, 2)
        | "or" => pure (.OR, 2)
        | "iszero" => pure (.ISZERO, 1)
        | "shl" => pure (.SHL, 2)
        | _ => throw s!"unsupported Yul builtin {name}"
      let args ← (← node.getObjVal? "arguments").getArr?
      unless args.size == arity do throw s!"wrong arity for {name}: {args.size}"
      let values ← args.toList.mapM (decodeExpr fuel)
      pure (.Call (.inl prim) values)
    | "YulLiteral" =>
      keys node ["nodeType", "kind", "type", "value", "src", "nativeSrc"]
      unless (← textField node "kind") == "number" do throw "unsupported Yul literal kind"
      unless (← textField node "type") == "" do throw "unsupported Yul literal type"
      pure (.Lit (EvmYul.UInt256.ofNat (← numeral (← textField node "value"))))
    | kind => throw s!"unsupported Yul expression {kind}"

/-- Single initialized declaration, sufficient for the captured product
binding. Multiple bindings, missing initializers and other statements fail. -/
def decodeDeclaration (fuel : Nat) (node : Json) : Except String EvmYul.Yul.Ast.Stmt := do
  unless (← textField node "nodeType") == "YulVariableDeclaration" do
    throw "unsupported Yul statement"
  keys node ["nodeType", "variables", "value", "src", "nativeSrc"]
  let vars ← (← node.getObjVal? "variables").getArr?
  unless vars.size == 1 do throw "expected one Yul declaration variable"
  let var := vars[0]!
  keys var ["nodeType", "name", "type", "src", "nativeSrc"]
  unless (← textField var "nodeType") == "YulTypedName" do
    throw "declaration variable is not a typed name"
  unless (← textField var "type") == "" do throw "unsupported Yul declaration type"
  let name ← textField var "name"
  unless !name.isEmpty do throw "empty declaration name"
  let value ← decodeExpr fuel (← node.getObjVal? "value")
  pure (.Let [name] (some value))

private def decodeEffect (fuel : Nat) (node : Json) : Except String EvmYul.Yul.Ast.Expr := do
  keys node ["nodeType", "functionName", "arguments", "src", "nativeSrc"]
  unless (← textField node "nodeType") == "YulFunctionCall" do throw "expected Yul effect call"
  let callee ← node.getObjVal? "functionName"
  keys callee ["nodeType", "name", "src", "nativeSrc"]
  unless (← textField callee "nodeType") == "YulIdentifier" do throw "invalid effect callee"
  let name ← textField callee "name"
  let prim : EvmYul.Operation .Yul ← match name with
    | "mstore" => pure .MSTORE
    | "revert" => pure .REVERT
    | "return" => pure .RETURN
    | _ => throw s!"unsupported Yul effect {name}"
  let args ← (← node.getObjVal? "arguments").getArr?
  unless args.size == 2 do throw s!"wrong effect arity for {name}"
  pure (.Call (.inl prim) (← args.toList.mapM (decodeExpr fuel)))

def decodeStmt : Nat → Json → Except String EvmYul.Yul.Ast.Stmt
  | 0, _ => .error "statement decoding fuel exhausted"
  | fuel + 1, node => do
    match ← textField node "nodeType" with
    | "YulBlock" =>
      keys node ["nodeType", "statements", "src", "nativeSrc"]
      let stmts ← (← node.getObjVal? "statements").getArr?
      pure (.Block (← stmts.toList.mapM (decodeStmt fuel)))
    | "YulVariableDeclaration" => decodeDeclaration fuel node
    | "YulIf" =>
      keys node ["nodeType", "condition", "body", "src", "nativeSrc"]
      let cond ← decodeExpr fuel (← node.getObjVal? "condition")
      let body ← node.getObjVal? "body"
      keys body ["nodeType", "statements", "src", "nativeSrc"]
      unless (← textField body "nodeType") == "YulBlock" do throw "expected Yul if block"
      let stmts ← (← body.getObjVal? "statements").getArr?
      pure (.If cond (← stmts.toList.mapM (decodeStmt fuel)))
    | "YulExpressionStatement" =>
      keys node ["nodeType", "expression", "src", "nativeSrc"]
      pure (.ExprStmtCall (← decodeEffect fuel (← node.getObjVal? "expression")))
    | kind => throw s!"unsupported Yul statement {kind}"

/-- Preserve the first memoryguard node as an explicit extension constructor,
then decode every remaining native statement in the actual enclosing block. -/
def decodeRuntime (fuel : Nat) (node : Json) : Except String MemoryGuard.Statement := do
  keys node ["nodeType", "statements", "src", "nativeSrc"]
  unless (← textField node "nodeType") == "YulBlock" do throw "expected runtime block"
  let statements ← (← node.getObjVal? "statements").getArr?
  match statements.toList with
  | [] => throw "expected runtime memoryguard declaration"
  | head :: tail =>
    let guard ← MemoryGuard.decodeDeclaration head
    let rest ← tail.mapM (decodeStmt fuel)
    pure (.block (guard :: rest.map MemoryGuard.Statement.native))

end SolidityTranslationValidation.AstBridge.Dispatcher
