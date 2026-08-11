import Lean
import Compiler.CompilationModel.InternalNaming
import Verity.Macro.Types

namespace Verity.Macro

open Lean

partial def valueTypeSignatureComponent : ValueType → String
  | .uint256 => "scalar_uint256"
  | .int256 => "scalar_int256"
  | .uint8 => "scalar_uint8"
  | .uint16 => "scalar_uint16"
  | .uintN bits => s!"scalar_uint{bits}"
  | .intN bits => s!"scalar_int{bits}"
  | .bytesN bytes => s!"scalar_bytes{bytes}"
  | .address => "scalar_address"
  | .bool => "scalar_bool"
  | .bytes32 => "scalar_bytes32"
  | .string => "scalar_string"
  | .bytes => "scalar_bytes"
  | .unit => "scalar_unit"
  | .array ty => "array_" ++ valueTypeSignatureComponent ty
  | .fixedArray ty size => "fixed_array_" ++ toString size ++ "_" ++ valueTypeSignatureComponent ty
  | .tuple tys => "tuple" ++ toString tys.length ++ "_" ++ String.intercalate "__" (tys.map valueTypeSignatureComponent)
  | .newtype name baseType => "newtype_" ++ name ++ "_" ++ valueTypeSignatureComponent baseType
  | .enum name _ => "enum_" ++ name
  | .struct name fields =>
      "struct_" ++ name ++ "_" ++
        String.intercalate "__" (fields.map (fun field => field.fst ++ "_" ++ valueTypeSignatureComponent field.snd))
  | .adt name _ => "adt_" ++ name

def functionSignatureKey (fn : FunctionDecl) : String :=
  fn.name ++ "(" ++ String.intercalate "," (fn.params.toList.map (fun p => valueTypeSignatureComponent p.ty)) ++ ")"

partial def valueTypeAbiSignatureComponent : ValueType → String
  | .newtype _ baseType => valueTypeAbiSignatureComponent baseType
  | .enum _ _ => "scalar_uint8"
  | .array ty => "array_" ++ valueTypeAbiSignatureComponent ty
  | .fixedArray ty size => "fixed_array_" ++ toString size ++ "_" ++ valueTypeAbiSignatureComponent ty
  | .tuple tys => "tuple" ++ toString tys.length ++ "_" ++ String.intercalate "__" (tys.map valueTypeAbiSignatureComponent)
  | .struct _ fields =>
      "tuple" ++ toString fields.length ++ "_" ++ String.intercalate "__" (fields.map (fun field => valueTypeAbiSignatureComponent field.snd))
  | .adt _ maxFields =>
      "tuple" ++ toString (maxFields + 1) ++ "_" ++
        String.intercalate "__" ("scalar_uint8" :: List.replicate maxFields "scalar_uint256")
  | ty => valueTypeSignatureComponent ty

def functionAbiSignatureKey (fn : FunctionDecl) : String :=
  fn.name ++ "(" ++ String.intercalate "," (fn.params.toList.map (fun p => valueTypeAbiSignatureComponent p.ty)) ++ ")"

def nameComponents : Name → List String
  | .anonymous => []
  | .str parent part => nameComponents parent ++ [part]
  | .num parent n => nameComponents parent ++ [toString n]

def mapNameLastComponent (f : String → String) : Name → Name
  | .anonymous => .anonymous
  | .str parent part => .str parent (f part)
  | .num parent n => .str parent (f (toString n))

def isQualifiedFunctionName (name : Name) : Bool :=
  (nameComponents name).length == 2

def startsWithLowercaseAscii (s : String) : Bool :=
  match s.toList with
  | c :: _ => 'a' ≤ c && c ≤ 'z'
  | [] => false

def qualifiedFunctionModelName (name : Name) : Name :=
  mapNameLastComponent (fun part => part ++ "_model") name

def qualifiedFunctionDisplayName (name : Name) : String :=
  String.intercalate "." (nameComponents name)

def internalHelperSpecNameFor (fn : FunctionDecl) : String :=
  Compiler.CompilationModel.internalFunctionPrefix ++ toString fn.ident.getId

def qualifiedInternalHelperBaseName (name : Name) : String :=
  let encodedComponents :=
    nameComponents name |>.map fun component =>
      s!"{component.length}_{component}"
  Compiler.CompilationModel.internalFunctionPrefix ++
    "qualified_" ++ String.intercalate "_" encodedComponents

def qualifiedInternalHelperName (functions : Array FunctionDecl) (name : Name) : String :=
  Compiler.CompilationModel.pickFreshName
    (qualifiedInternalHelperBaseName name)
    ((functions.map internalHelperSpecNameFor).toList)

def qualifiedInternalHelperNameFromUsed
    (usedNames : List String)
    (name : Name) : String :=
  Compiler.CompilationModel.pickFreshName (qualifiedInternalHelperBaseName name) usedNames

partial def qualifiedFunctionAppSyntax? (stx : Term) : Option (Name × Array Term) :=
  match stx.raw with
  | .node _ `Lean.Parser.Term.doExpr args =>
      match args.getD 0 Syntax.missing with
      | inner => qualifiedFunctionAppSyntax? ⟨inner⟩
  | .node _ `Lean.Parser.Term.paren args =>
      match args.getD 1 Syntax.missing with
      | inner => qualifiedFunctionAppSyntax? ⟨inner⟩
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ _ raw _ =>
          if isQualifiedFunctionName raw then
            let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
            some (raw, argTerms)
          else
            none
      | _ => none
  | _ => none

def overloadedFunctionIdentName (fn : FunctionDecl) : String :=
  -- Length-prefix each component so the suffix encoding is injective.
  -- Component strings can contain `_` (e.g. `newtype_Foo_scalar_uint256`,
  -- `tuple2_scalar_uint256__scalar_bool`), so a plain `_` join is ambiguous
  -- and distinct overloads can collapse to the same identifier.
  let suffix :=
    match fn.params.toList.map (fun p => valueTypeSignatureComponent p.ty) with
    | [] => "0"
    | parts => String.join (parts.map fun p => toString p.length ++ "x" ++ p)
  fn.name ++ "__" ++ suffix

def assignOverloadInternalIdents (functions : Array FunctionDecl) :
    Array FunctionDecl :=
  functions.map fun fn =>
    if functions.any (fun other => other.name == fn.name && functionSignatureKey other != functionSignatureKey fn) then
      { fn with ident := mkIdentFrom fn.ident (Name.mkSimple (overloadedFunctionIdentName fn)) }
    else
      fn

end Verity.Macro
