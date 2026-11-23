import Compiler.SolidityImport.ExprHelpers

/-! Conservative admission for the initial Solidity 0.7.6 scalar slice.
The existing lowering remains responsible for admitting individual constructs.
This additional boundary prevents newer failure, ABI, and conversion semantics
from being silently applied to a legacy declaration. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport

private partial def validateLegacySyntax (node : Json) : M Unit := do
  match node with
  | .arr children => children.forM validateLegacySyntax
  | .obj fields =>
    if let some kind := optStr node "nodeType" then
      unless #["FunctionDefinition", "ParameterList", "VariableDeclaration", "Block",
          "ExpressionStatement", "VariableDeclarationStatement", "IfStatement", "Return",
          "BinaryOperation", "UnaryOperation", "Assignment", "Identifier", "Literal",
          "ElementaryTypeName", "ElementaryTypeNameExpression", "FunctionCall",
          "MemberAccess", "IndexAccess", "Mapping", "TupleExpression",
          "UserDefinedTypeName", "OverrideSpecifier", "StructuredDocumentation"].contains kind do
        failAt node s!"Solidity 0.7.6 scalar slice does not support {kind}"
      if kind == "FunctionDefinition" then
        unless #[some "pure", some "view"].contains (optStr node "stateMutability") do
          failAt node "Solidity 0.7.6 scalar slice requires a read-only function"
      if let some ty := (field? node "typeDescriptions").bind (optStr · "typeString") then
        if ty.contains '[' || ty.startsWith "struct " || ty.startsWith "enum " ||
            (ty.startsWith "int" && !ty.startsWith "int_const") ||
            ty.startsWith "bytes " || ty.startsWith "string " then
          failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty}"
        if let some width := fixedBytesWidth? ty then
          unless width == 32 do
            failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty}"
      if kind == "BinaryOperation" || kind == "Assignment" then
        if #[some "/", some "%", some "/=", some "%="].contains (optStr node "operator") then
          failAt node ("Solidity 0.7.6 division/modulo may execute INVALID; " ++
            "legacy exceptional halt is not modeled")
      if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
        let target := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        unless target.startsWith "uint" || target.startsWith "address" do
          failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
        for arg in (← mArr (← mField node "arguments")) do
          let source := (field? arg "typeDescriptions").bind (optStr · "typeString") |>.getD ""
          unless source.startsWith "uint" || source.startsWith "address" ||
              source.startsWith "int_const" do
            failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
      if kind == "FunctionCall" && optStr node "kind" == some "functionCall" then
        let callee ← mField node "expression"
        let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        if (ty.splitOn " external").length > 1 then
          failAt node "Solidity 0.7.6 external calls are outside the scalar slice"
        if optStr callee "nodeType" == some "Identifier" then
          -- Legacy builtins retain duplicate negative overloadedDeclarations.
          -- Ordinary reference/overload resolution is checked by the lowering.
          if let some id := (field? callee "referencedDeclaration").bind (·.getInt?.toOption) then
            if id < 0 && !#[some "require", some "revert"].contains (optStr callee "name") then
              failAt node ("Solidity 0.7.6 builtin call is outside the scalar slice " ++
                "(assert/INVALID is not modeled)")
    for (_, child) in fields do
      validateLegacySyntax child
  | _ => pure ()

/-- Check a reached declaration and the initializers of constants and immutables it uses.
Solc links both identifiers and qualified members to their declaration IDs. -/
partial def validateLegacyDeclaration (root : Json) : M Unit := do
  let env ← get
  let constants := env.numericConstants
  let immutables := env.stateVars
  let mut seen : Std.HashSet Nat := {}
  let mut pending := [root]
  while let decl :: rest := pending do
    pending := rest
    validateLegacySyntax decl
    for id in referencedDecls decl do
      let referenced := constants.find? id <|>
        (immutables.find? id).filter (optStr · "mutability" == some "immutable")
      if let some initializer := referenced then
        unless seen.contains id do
          seen := seen.insert id
          pending := initializer :: pending

/-- Validate each legacy declaration on first reach, inside its lowering recovery point. -/
def noteProfiledFn (fn : Json) : M Unit := do
  let env ← get
  if env.legacyWrapping then
    let id ← mNat (← mField fn "id")
    unless env.included.any (·.declId == id) do
      let stack := if env.stack.head? == some id then env.stack else id :: env.stack
      let file := env.nodeFile.find? id |>.getD env.currentFile
      (validateLegacyDeclaration fn).run' { env with stack, currentFile := file }
  noteFn fn

/-- The `literals` of every pragma directive of a source unit. -/
def pragmaLiterals (ast : Json) : Array (Array Json) :=
  match (field? ast "nodes").bind (·.getArr?.toOption) with
  | none => #[]
  | some nodes => nodes.filterMap fun node =>
    if optStr node "nodeType" == some "PragmaDirective" then
      (field? node "literals").bind (·.getArr?.toOption)
    else none

/-- The literals of `pragma abicoder <version>`. -/
def abicoderPragma (version : String) : Array Json := #[Json.str "abicoder", Json.str version]

/-- A source unit with `pragma abicoder v1`. -/
def abiCoderV1Pragma (ast : Json) : Bool :=
  (pragmaLiterals ast).contains (abicoderPragma "v1")

/-- Solidity 0.7.6 defaults to ABI coder v1. External decoding uses the
target contract's source unit, including for inherited functions. -/
def legacyAbiV2 (ast : Json) : Bool :=
  (pragmaLiterals ast).any fun literals =>
    literals == #[Json.str "experimental", Json.str "ABIEncoderV2"] || literals == abicoderPragma "v2"

end Compiler.CompilationModel.SolidityImport
