import Lean
import Compiler.SolidityImport.SolidityAbi
import Compiler.CompilationModel.AbiTypeLayout

namespace Compiler.CompilationModel.SolidityImport.AbiSchema
open Lean

/-- Keep the exact offending solc node so the importer can use its `src` span
with the existing file:line:column reporter. Schema failure is never calldata
malformation and must never become an EVM runtime revert. -/
structure Failure where
  node : Json
  message : String

structure ScalarField where
  name : String
  kind : SolidityAbi.ScalarKind
  deriving Repr

inductive Member where
  | scalar (field : ScalarField)
  | scalarArray (field : ScalarField)
  | structArray (name : String) (fields : List ScalarField)
  deriving Repr

private def fail (node : Json) (message : String) : Except Failure α :=
  .error ⟨node, message⟩

private def field (node : Json) (key : String) : Except Failure Json :=
  (node.getObjVal? key).mapError fun _ => ⟨node, s!"ABI schema: missing {key}"⟩

private def stringField (node : Json) (key : String) : Except Failure String := do
  let value ← field node key
  value.getStr?.mapError fun _ => ⟨node, s!"ABI schema: {key} must be a string"⟩

private def members (node : Json) : Except Failure (List Json) := do
  unless (← stringField node "nodeType") == "StructDefinition" do
    fail node "ABI schema: expected a struct declaration"
  let value ← field node "members"
  let items ← value.getArr?.mapError fun _ => ⟨node, "ABI schema: invalid members"⟩
  if items.isEmpty then fail node "ABI schema: empty structs are unsupported"
  else pure items.toList

/-- Parse only supported unsigned scalar syntax, with no fallback or coercion.
Signed/fixed-byte/user-defined types need their own semantics before admission. -/
def scalarKind (node : Json) : Except Failure SolidityAbi.ScalarKind := do
  unless (← stringField node "nodeType") == "ElementaryTypeName" do
    fail node "ABI schema: expected an unsigned scalar type"
  let name ← stringField node "name"
  if name == "address" then return .address
  if name == "bool" then return .bool
  if name == "bytes32" then return .bytes32
  let width := if name == "uint" then some 256 else
    if name.startsWith "uint" then (name.drop 4).toString.toNat? else none
  let some width := width | fail node s!"ABI schema: unsupported scalar {name}"
  if 8 ≤ width ∧ width ≤ 256 ∧ width % 8 = 0 then
    let bytes := width / 8 - 1
    if hb : bytes < 32 then return .uint ⟨bytes, hb⟩
    else fail node "ABI schema: unsigned width outside [8,256]"
  else fail node s!"ABI schema: invalid unsigned width {width}"

def scalarField (node : Json) : Except Failure ScalarField := do
  return { name := ← stringField node "name", kind := ← scalarKind (← field node "typeName") }

/-- Schema for Market-shaped roots: unsigned scalars plus dynamic arrays of
flat scalar structs. Resolves declaration ids, never textual struct names.
Nested structs/arrays and fixed arrays fail at their own type-name node. -/
def root (resolve : Nat → Option Json) (node : Json) : Except Failure (List Member) := do
  (← members node).mapM fun member => do
    let ty ← field member "typeName"
    if (← stringField ty "nodeType") != "ArrayTypeName" then
      return .scalar (← scalarField member)
    -- solc omits `length` for dynamic arrays (some AST producers use null).
    if let .ok length := ty.getObjVal? "length" then
      unless length.isNull do fail ty "ABI schema: fixed arrays are unsupported"
    let base ← field ty "baseType"
    if (← stringField base "nodeType") == "ElementaryTypeName" then
      return .scalarArray { name := ← stringField member "name", kind := ← scalarKind base }
    unless (← stringField base "nodeType") == "UserDefinedTypeName" do
      fail base "ABI schema: expected a flat struct array element"
    let ref ← field base "referencedDeclaration"
    let id ← ref.getNat?.mapError fun _ => ⟨base, "ABI schema: invalid struct declaration id"⟩
    let some decl := resolve id | fail base s!"ABI schema: unresolved struct declaration {id}"
    let fields ← (← members decl).mapM scalarField
    return .structArray (← stringField member "name") fields

def scalarType : SolidityAbi.ScalarKind → ParamType
  | .uint width => if width.val == 31 then .uint256 else .uintN (8*(width.val+1))
  | .address => .address
  | .bool => .bool
  | .bytes32 => .bytes32

def memberType : Member → ParamType
  | .scalar field => scalarType field.kind
  | .scalarArray field => .array (scalarType field.kind)
  | .structArray _ fields => .array (.tuple (fields.map fun f => scalarType f.kind))

def paramType (schema : List Member) : ParamType := .tuple (schema.map memberType)

end Compiler.CompilationModel.SolidityImport.AbiSchema
