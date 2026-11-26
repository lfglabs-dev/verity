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
  /-- A `bytes` or `string` member: both share the dynamic byte-array ABI
  encoding; `isString` only selects the ABI type name (`string` vs `bytes`). -/
  | bytesField (name : String) (isString : Bool := false)
  | scalarArray (field : ScalarField)
  | structArray (name : String) (fields : List ScalarField)
  | nestedStruct (name : String) (structId : Nat) (structName : String) (members : List (String × String)) (schema : List Member)
  /-- A dynamic array of `bytes` (`bytes[]`); only produced for root parameters. -/
  | bytesArray (name : String)
  deriving Repr

def isDynamicMember : Member → Bool
  | .scalar _ => false
  | .bytesField _ _ | .scalarArray _ | .structArray _ _ | .nestedStruct _ _ _ _ _
  | .bytesArray _ => true

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

/-- The diagnostic for a user-defined type name `ty` that does not resolve to a struct
declaration: it names the field's actual type (an `enum`, a user-defined value type or a
contract type, from solc's type descriptions) rather than reporting an unresolved struct.
Such fields need their own ABI semantics (an enum's range check, a value type's underlying
type) before admission. -/
def unsupportedUserTypeMessage (ty : Json) (id : Nat) : String :=
  let descriptions := (ty.getObjVal? "typeDescriptions").toOption
  let typeString := descriptions.bind fun d => (d.getObjVal? "typeString").toOption.bind
    (·.getStr?.toOption)
  let typeIdentifier := descriptions.bind fun d => (d.getObjVal? "typeIdentifier").toOption.bind
    (·.getStr?.toOption)
  match typeString, typeIdentifier with
  | some name, some ident =>
      if ident.startsWith "t_enum$" then s!"ABI schema: unsupported struct field type {name}"
      else if ident.startsWith "t_userDefinedValueType$" then
        s!"ABI schema: unsupported struct field type {name} (user-defined value type)"
      else if ident.startsWith "t_contract$" then
        s!"ABI schema: unsupported struct field type {name}"
      else s!"ABI schema: unresolved struct declaration {id}"
  | _, _ => s!"ABI schema: unresolved struct declaration {id}"

private def isContractTypeName (node : Json) : Bool :=
  match node.getObjVal? "typeDescriptions" with
  | .ok td =>
      match td.getObjVal? "typeString" with
      | .ok (.str s) => s.startsWith "contract "
      | _ => false
  | _ => false

/-- Parse only supported unsigned scalar or enum syntax, with no fallback or coercion.
Interface and contract types (`UserDefinedTypeName` with `contract ...` type
string) have the exact Solidity ABI encoding and 160-bit validation of `address`.
Signed/fixed-byte/user-defined types need their own semantics before admission. -/
def scalarKind (node : Json) (resolveEnum : Nat → Option Nat := fun _ => none) :
    Except Failure SolidityAbi.ScalarKind := do
  let kind ← stringField node "nodeType"
  if kind == "UserDefinedTypeName" then
    if isContractTypeName node then
      return .address
    if let .ok ref := node.getObjVal? "referencedDeclaration" then
      if let .ok id := ref.getNat? then
        if let some count := resolveEnum id then
          if count > 0 && count ≤ 256 then
            return .enum count
          else
            fail node s!"ABI schema: invalid enum member count {count}"
  unless kind == "ElementaryTypeName" do
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

def scalarField (node : Json) (resolveEnum : Nat → Option Nat := fun _ => none) :
    Except Failure ScalarField := do
  return { name := ← stringField node "name",
           kind := ← scalarKind (← field node "typeName") resolveEnum }

/-- The `structArray` member `name` for the dynamic array type node `ty` of a
flat scalar struct (`S[]`): a struct-array member or a root `S[]` parameter.
Resolves the declaration id, never the textual struct name. -/
def structArrayMember (resolve : Nat → Option Json) (name : String) (ty : Json)
    (resolveEnum : Nat → Option Nat := fun _ => none) :
    Except Failure Member := do
  unless (← stringField ty "nodeType") == "ArrayTypeName" do
    fail ty "ABI schema: expected a dynamic array type"
  -- solc omits `length` for dynamic arrays (some AST producers use null).
  if let .ok length := ty.getObjVal? "length" then
    unless length.isNull do fail ty "ABI schema: fixed arrays are unsupported"
  let base ← field ty "baseType"
  unless (← stringField base "nodeType") == "UserDefinedTypeName" do
    fail base "ABI schema: expected a flat struct array element"
  let ref ← field base "referencedDeclaration"
  let id ← ref.getNat?.mapError fun _ => ⟨base, "ABI schema: invalid struct declaration id"⟩
  let some decl := resolve id | fail base (unsupportedUserTypeMessage base id)
  let fields ← (← members decl).mapM (scalarField · resolveEnum)
  return .structArray name fields

/-- Schema for Market- and Offer-shaped roots: unsigned scalars, enums, dynamic bytes,
nested dynamic structs, and dynamic arrays of unsigned scalars or flat scalar
structs. Resolves declaration ids, never textual struct names. -/
def root (resolve : Nat → Option Json) (node : Json) (seen : List Nat := [])
    (fuel : Nat := 16) (resolveEnum : Nat → Option Nat := fun _ => none) :
    Except Failure (List Member) :=
  match fuel with
  | 0 => fail node "ABI schema: struct nesting depth exceeded"
  | fuel + 1 => do
    (← members node).mapM fun member => do
      let mname ← stringField member "name"
      let ty ← field member "typeName"
      let tyKind ← stringField ty "nodeType"
      if tyKind == "ElementaryTypeName" then
        let elementary ← stringField ty "name"
        if elementary == "bytes" || elementary == "string" then
          return .bytesField mname (elementary == "string")
        else
          return .scalar (← scalarField member resolveEnum)
      if tyKind == "UserDefinedTypeName" then
        if isContractTypeName ty then
          return .scalar { name := mname, kind := .address }
        let ref ← field ty "referencedDeclaration"
        let id ← ref.getNat?.mapError fun _ => ⟨ty, "ABI schema: invalid struct declaration id"⟩
        if let some variantCount := resolveEnum id then
          if 0 < variantCount ∧ variantCount ≤ 256 then
            return .scalar { name := mname, kind := .enum variantCount }
          else
            fail ty s!"ABI schema: invalid enum member count {variantCount}"
        if seen.contains id then
          fail ty "ABI schema: recursive struct declaration"
        let some decl := resolve id | fail ty (unsupportedUserTypeMessage ty id)
        unless (← stringField decl "nodeType") == "StructDefinition" do
          fail ty "ABI schema: expected an unsigned scalar type"
        let sname ← stringField decl "name"
        let subMembers ← (← members decl).mapM fun sub => do
          let subName ← stringField sub "name"
          let subTyDesc ← field sub "typeDescriptions"
          let subTyStr ← stringField subTyDesc "typeString"
          return (subName, subTyStr)
        let subSchema ← root resolve decl (id :: seen) fuel resolveEnum
        unless subSchema.any isDynamicMember do
          fail ty "ABI schema: static nested structs inside dynamic structs are outside this slice"
        return .nestedStruct mname id sname subMembers subSchema
      if tyKind != "ArrayTypeName" then
        return .scalar (← scalarField member resolveEnum)
      -- solc omits `length` for dynamic arrays (some AST producers use null).
      if let .ok length := ty.getObjVal? "length" then
        unless length.isNull do fail ty "ABI schema: fixed arrays are unsupported"
      let base ← field ty "baseType"
      if (← stringField base "nodeType") == "ElementaryTypeName" ||
          ((← stringField base "nodeType") == "UserDefinedTypeName" && isContractTypeName base) then
        return .scalarArray { name := mname, kind := ← scalarKind base }
      structArrayMember resolve mname ty resolveEnum

def scalarType : SolidityAbi.ScalarKind → ParamType
  | .uint width => if width.val == 31 then .uint256 else .uintN (8*(width.val+1))
  | .address => .address
  | .bool => .bool
  | .bytes32 => .bytes32
  | .enum _ => .uintN 8

mutual
  def memberType : Member → ParamType
    | .scalar field => scalarType field.kind
    | .bytesField _ isString => if isString then .string else .bytes
    | .scalarArray field => .array (scalarType field.kind)
    | .structArray _ fields => .array (.tuple (fields.map fun f => scalarType f.kind))
    | .nestedStruct _ _ _ _ subSchema => .tuple (memberTypeList subSchema)
    | .bytesArray _ => .array .bytes
  termination_by m => sizeOf m

  def memberTypeList : List Member → List ParamType
    | [] => []
    | m :: rest => memberType m :: memberTypeList rest
  termination_by ms => sizeOf ms
end

def paramType (schema : List Member) : ParamType := .tuple (memberTypeList schema)

mutual
  /-- Whether a member is, or (through nested structs) contains, a `string`. -/
  def memberHasString : Member → Bool
    | .bytesField _ isString => isString
    | .nestedStruct _ _ _ _ subSchema => membersHaveString subSchema
    | _ => false
  termination_by m => sizeOf m

  def membersHaveString : List Member → Bool
    | [] => false
    | m :: rest => memberHasString m || membersHaveString rest
  termination_by ms => sizeOf ms
end

mutual
  /-- Whether a member is, or (through nested structs) contains, an `enum`. -/
  def memberHasEnum : Member → Bool
    | .scalar field => match field.kind with | .enum _ => true | _ => false
    | .scalarArray field => match field.kind with | .enum _ => true | _ => false
    | .structArray _ fields => fields.any fun f => match f.kind with | .enum _ => true | _ => false
    | .nestedStruct _ _ _ _ subSchema => membersHaveEnum subSchema
    | .bytesField _ _ | .bytesArray _ => false
  termination_by m => sizeOf m

  def membersHaveEnum : List Member → Bool
    | [] => false
    | m :: rest => memberHasEnum m || membersHaveEnum rest
  termination_by ms => sizeOf ms
end

end Compiler.CompilationModel.SolidityImport.AbiSchema
