import Lean
import Verity.Macro.Syntax
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

partial def valueTypeToSolidityString : ValueType → String
  | .uint256 => "uint256"
  | .int256 => "int256"
  | .uint8 => "uint8"
  | .uint16 => "uint16"
  | .uintN bits => s!"uint{bits}"
  | .intN bits => s!"int{bits}"
  | .bytesN bytes => s!"bytes{bytes}"
  | .address => "address"
  | .bytes32 => "bytes32"
  | .bool => "bool"
  | .string => "string"
  | .bytes => "bytes"
  | .array elemTy => valueTypeToSolidityString elemTy ++ "[]"
  | .fixedArray elemTy size => valueTypeToSolidityString elemTy ++ "[" ++ toString size ++ "]"
  | .tuple elemTys =>
      "(" ++ String.intercalate "," (elemTys.map valueTypeToSolidityString) ++ ")"
  | .struct _ fields =>
      "(" ++ String.intercalate "," (fields.map (fun field => valueTypeToSolidityString field.snd)) ++ ")"
  | .newtype _ baseType => valueTypeToSolidityString baseType
  | .adt name _ => name
  | .unit => "()"

def interfaceFunctionSignature (methodName : String) (params : Array ValueType) : String :=
  methodName ++ "(" ++
    String.intercalate "," (params.toList.map valueTypeToSolidityString) ++
    ")"

def parseInterfaceParam
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityInterfaceParam| $name:ident : $ty:term) => do
      let parsedTy ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      pure {
        ident := name
        name := toString name.getId
        ty := parsedTy
      }
  | _ => throwErrorAt stx "invalid interface parameter declaration"

def parseInterfaceFunction
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM InterfaceFunctionDecl := do
  let expectReturnsMarker (marker : Ident) : CommandElabM Unit := do
    unless toString marker.getId == "returns" do
      throwErrorAt marker "expected 'returns'"
  -- `returnTys?` is `none` for a void interface method (no returns clause).
  let parseParts (name : Ident) (params : Array ParamDecl)
      (mods : TSyntaxArray `verityMutability) (returnTys? : Option (TSyntaxArray `term)) := do
    let mut isView := false
    for mod in mods do
      match mod with
      | `(verityMutability| view) =>
          if isView then
            throwErrorAt mod "duplicate 'view' modifier"
          isView := true
      | _ => throwErrorAt mod "interface functions currently support only the optional `view` modifier"
    let parsedReturns ←
      match returnTys? with
      | none => pure #[]
      | some returnTys => do
          let parsed ← returnTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
          if parsed.isEmpty then
            throwErrorAt stx "interface function returns clause must contain at least one return type"
          if parsed.size > 1 then
            throwErrorAt stx "typed interface calls currently support exactly one return value"
          pure parsed
    pure {
      ident := name
      name := toString name.getId
      params := params
      returnTys := parsedReturns
      isView := isView
    }
  -- positional (`(term, ...)`) params lower to synthetic arg0/arg1/... names.
  let parsePositionalParams (paramTys : TSyntaxArray `term) : CommandElabM (Array ParamDecl) :=
    paramTys.mapIdxM fun idx ty => do
      pure {
        ident := mkIdent (Name.mkSimple s!"arg{idx}")
        name := s!"arg{idx}"
        ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      }
  match stx with
  | `(verityInterfaceFunction| function $name:ident ($[$params:verityInterfaceParam],*) $[$mods:verityMutability]* $returnsMarker:ident ($[$returnTys:term],*)) => do
      expectReturnsMarker returnsMarker
      parseParts name (← params.mapM (parseInterfaceParam newtypes structDecls adtDecls)) mods (some returnTys)
  | `(verityInterfaceFunction| function $name:ident ($[$paramTys:term],*) $[$mods:verityMutability]* $returnsMarker:ident ($[$returnTys:term],*)) => do
      expectReturnsMarker returnsMarker
      parseParts name (← parsePositionalParams paramTys) mods (some returnTys)
  -- void forms: no returns clause
  | `(verityInterfaceFunction| function $name:ident ($[$params:verityInterfaceParam],*) $[$mods:verityMutability]*) => do
      parseParts name (← params.mapM (parseInterfaceParam newtypes structDecls adtDecls)) mods none
  | `(verityInterfaceFunction| function $name:ident ($[$paramTys:term],*) $[$mods:verityMutability]*) => do
      parseParts name (← parsePositionalParams paramTys) mods none
  | _ => throwErrorAt stx "invalid interface function declaration"

def parseInterface
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM InterfaceDecl := do
  match stx with
  | `(verityInterface| interface $name:ident where $[$fns:verityInterfaceFunction]* end) =>
      let parsedFns ← fns.mapM (parseInterfaceFunction newtypes structDecls adtDecls)
      if parsedFns.isEmpty then
        throwErrorAt name s!"interface '{toString name.getId}' must declare at least one function"
      pure { ident := name, name := toString name.getId, functions := parsedFns }
  | _ => throwErrorAt stx "invalid interface declaration"

def interfaceExternalName (interfaceName methodName : String) : String :=
  s!"{interfaceName}.{methodName}"

def interfaceExternals (ifaces : Array InterfaceDecl) : Array ExternalDecl :=
  ifaces.foldl
    (fun acc iface =>
      acc ++ iface.functions.map (fun fn => {
        ident := fn.ident
        name := interfaceExternalName iface.name fn.name
        params := fn.params.map (·.ty)
        returnTys := fn.returnTys
        linkMode := Compiler.CompilationModel.ForeignLinkMode.external
        interfaceName? := some iface.name
        isView := fn.isView
      }))
    #[]

end Verity.Macro
