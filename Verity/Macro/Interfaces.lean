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
  | .enum _ _ => "uint8"
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

def parseLinkedContract (stx : Syntax) : CommandElabM LinkedContractDecl := do
  match stx with
  | `(verityLinkedContract| $name:ident : $iface:ident := $callee:ident) =>
      pure {
        ident := name
        name := toString name.getId
        interfaceName := toString iface.getId
        interfaceIdent := iface
        calleeName := toString callee.getId
        calleeIdent := callee
      }
  | `(verityLinkedContract| $name:ident : $iface:ident := deferred) =>
      pure {
        ident := name
        name := toString name.getId
        interfaceName := toString iface.getId
        interfaceIdent := iface
        calleeName := ""
        calleeIdent := name
        isDeferred := true
      }
  | _ => throwErrorAt stx "invalid linked_contracts binding; expected `name : IFace := Callee` or `name : IFace := deferred`"

def parseInterface
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM InterfaceDecl := do
  match stx with
  | `(verityInterface| interface $name:ident where $[$fns:verityInterfaceFunction]* end) =>
      let parsedFns ← fns.mapM (parseInterfaceFunction newtypes structDecls adtDecls)
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

/-! ### Multi-Return Interface Signatures (`#2418`, `#2424`) -/

/-- Normalize an interface function's return types so a single `Tuple [T₁, ..., Tₙ]`
    return annotation and a multi-return `(T₁, ..., Tₙ)` clause share the same
    canonical leaf return array (`#2418`, `#2424`). -/
def normalizeInterfaceReturnTypes (returnTys : Array ValueType) : Array ValueType :=
  match returnTys.toList with
  | [.tuple elemTys] => elemTys.toArray
  | _ => returnTys

/-- Canonical EDSL `ValueType` returned by an `InterfaceFunctionDecl`:
    `.unit` for void methods, `ty` for single-return methods, and `.tuple` for
    multi-return methods (`#2418`, `#2424`). -/
def interfaceReturnValueType (fn : InterfaceFunctionDecl) : ValueType :=
  let norm := normalizeInterfaceReturnTypes fn.returnTys
  match norm.toList with
  | [] => .unit
  | [ty] => ty
  | tys => .tuple tys

/-- Canonical ABI return-tuple signature string `(t1,t2,...)` for an interface method. -/
def interfaceFunctionReturnSignature (fn : InterfaceFunctionDecl) : String :=
  let norm := normalizeInterfaceReturnTypes fn.returnTys
  "(" ++ String.intercalate "," (norm.toList.map valueTypeToSolidityString) ++ ")"

/-- Full human/audit signature `f(p1,p2)->(r1,r2)` including multi-return types (`#2418`, `#2424`). -/
def interfaceFunctionFullSignature (fn : InterfaceFunctionDecl) : String :=
  interfaceFunctionSignature fn.name (fn.params.map (·.ty)) ++
    "->" ++ interfaceFunctionReturnSignature fn

/-- Static 32-byte ABI word count of a `ValueType` when statically sized (`none` for dynamic types). -/
partial def valueTypeStaticWords? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool | .enum _ _ =>
      some 1
  | .unit =>
      some 0
  | .newtype _ baseType =>
      valueTypeStaticWords? baseType
  | .fixedArray elemTy size =>
      (valueTypeStaticWords? elemTy).map (· * size)
  | .tuple elemTys =>
      elemTys.foldlM
        (fun acc elemTy => do
          let w ← valueTypeStaticWords? elemTy
          pure (acc + w))
        0
  | .struct _ fields =>
      fields.foldlM
        (fun acc (_, fty) => do
          let w ← valueTypeStaticWords? fty
          pure (acc + w))
        0
  | _ => none

/-- Total static 32-byte ABI return word count for a single- or multi-return interface function. -/
def interfaceFunctionStaticReturnWords? (fn : InterfaceFunctionDecl) : Option Nat :=
  let norm := normalizeInterfaceReturnTypes fn.returnTys
  norm.toList.foldlM
    (fun acc rty => do
      let w ← valueTypeStaticWords? rty
      pure (acc + w))
    0

/-! ### Interface-Typed Storage Field Descriptors (`#2418`, `#2424`) -/

/-- Descriptor for an interface-typed contract storage field (`token : IERC20 := slot k`).
    At the EVM storage level, interface references occupy an `Address` slot (160 bits)
    while retaining `interfaceName` for typed external/hop dispatch (`#2418`, `#2424`). -/
structure InterfaceStorageFieldDesc where
  ident : Ident
  name : String
  interfaceName : String
  slotNum : Nat
  isTransient : Bool := false
  packedBits : Option (Nat × Nat) := none

namespace InterfaceStorageFieldDesc

/-- Lower an interface-typed storage field descriptor to its underlying `Address`-typed
    `StorageFieldDecl`. -/
def toStorageFieldDecl (d : InterfaceStorageFieldDesc) : StorageFieldDecl :=
  { ident := d.ident
    name := d.name
    ty := .scalar .address
    slotNum := d.slotNum
    isTransient := d.isTransient
    packedBits := d.packedBits }

end InterfaceStorageFieldDesc

/-- Check whether `ty` names a declared interface in `ifaces`, returning its interface name. -/
def resolveInterfaceStorageType? (ifaces : Array InterfaceDecl) (ty : Term) : Option String :=
  match stripParens ty with
  | `(term| $id:ident) =>
      let candidate := toString id.getId
      ifaces.find? (fun iface => iface.name == candidate) |>.map (·.name)
  | _ => none

/-- Construct an `InterfaceStorageFieldDesc` if `ty` resolves to a declared interface. -/
def interfaceStorageFieldFromSyntax?
    (ifaces : Array InterfaceDecl)
    (ident : Ident)
    (ty : Term)
    (slotNum : Nat)
    (isTransient : Bool := false)
    (packedBits : Option (Nat × Nat) := none) : Option InterfaceStorageFieldDesc := do
  let ifaceName ← resolveInterfaceStorageType? ifaces ty
  pure
    { ident := ident
      name := toString ident.getId
      interfaceName := ifaceName
      slotNum := slotNum
      isTransient := isTransient
      packedBits := packedBits }

/-! ### `public` State-Variable Getter Descriptors for `hopCallView` (`#2439`) -/

/-- Convert a `MappingKeyType` to its corresponding `ValueType` parameter in a synthesized getter. -/
def mappingKeyTypeToValueType : MappingKeyType → ValueType
  | .address => .address
  | .uint256 => .uint256
  | .bytes32 => .bytes32

/-- Convert a `StorageArrayElemType` to its corresponding `ValueType` return in a synthesized getter. -/
def storageArrayElemTypeToValueType : Compiler.CompilationModel.StorageArrayElemType → ValueType
  | .uint256 => .uint256
  | .address => .address
  | .bool => .bool
  | .uint8 => .uint8
  | .bytes32 => .bytes32

/-- Classification of Solidity auto-generated `public` state-variable getters (`#2439`). -/
inductive PublicGetterKind where
  | scalar (valueTy : ValueType)
  | mappingChain (keyTys : List MappingKeyType) (valueTy : ValueType)
  | dynamicArray (elemTy : ValueType)
  | mappingStruct (keyTy : MappingKeyType) (memberTys : List ValueType)
  | mappingStruct2 (outerKey innerKey : MappingKeyType) (memberTys : List ValueType)
  deriving BEq

/-- Descriptor for a `public` state-variable getter usable as a valid `hopCallView`
    and interface-binding target (`#2439`). -/
structure PublicGetterDesc where
  fieldIdent : Ident
  fieldName : String
  slotNum : Nat
  kind : PublicGetterKind
  paramTys : Array ValueType
  returnTys : Array ValueType

/-- Derive the `PublicGetterDesc` for a persistent `StorageFieldDecl` (`#2439`).
    Transient storage fields do not expose public ABI getters in Solidity. -/
def publicGetterDescForField? (field : StorageFieldDecl) : Option PublicGetterDesc :=
  if field.isTransient then
    none
  else
    match field.ty with
    | .scalar vt =>
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .scalar vt
            paramTys := #[]
            returnTys := #[vt] }
    | .dynamicArray elemTy =>
        let vt := storageArrayElemTypeToValueType elemTy
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .dynamicArray vt
            paramTys := #[.uint256]
            returnTys := #[vt] }
    | .mappingAddressToUint256 =>
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.address] .uint256
            paramTys := #[.address]
            returnTys := #[.uint256] }
    | .mappingAddressToEnum name count =>
        let vt := ValueType.enum name count
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.address] vt
            paramTys := #[.address]
            returnTys := #[vt] }
    | .mappingUintToUint256 =>
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.uint256] .uint256
            paramTys := #[.uint256]
            returnTys := #[.uint256] }
    | .mappingUintToEnum name count =>
        let vt := ValueType.enum name count
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.uint256] vt
            paramTys := #[.uint256]
            returnTys := #[vt] }
    | .mapping2AddressToAddressToUint256 =>
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.address, .address] .uint256
            paramTys := #[.address, .address]
            returnTys := #[.uint256] }
    | .mapping2AddressToAddressToEnum name count =>
        let vt := ValueType.enum name count
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain [.address, .address] vt
            paramTys := #[.address, .address]
            returnTys := #[vt] }
    | .mappingChain keyTys =>
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain keyTys .uint256
            paramTys := keyTys.toArray.map mappingKeyTypeToValueType
            returnTys := #[.uint256] }
    | .mappingChainEnum keyTys name count =>
        let vt := ValueType.enum name count
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingChain keyTys vt
            paramTys := keyTys.toArray.map mappingKeyTypeToValueType
            returnTys := #[vt] }
    | .mappingStruct keyTy members =>
        let memberTys := members.map (·.ty)
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingStruct keyTy memberTys
            paramTys := #[mappingKeyTypeToValueType keyTy]
            returnTys := memberTys.toArray }
    | .mappingStruct2 outerKey innerKey members =>
        let memberTys := members.map (·.ty)
        some
          { fieldIdent := field.ident
            fieldName := field.name
            slotNum := field.slotNum
            kind := .mappingStruct2 outerKey innerKey memberTys
            paramTys := #[mappingKeyTypeToValueType outerKey, mappingKeyTypeToValueType innerKey]
            returnTys := memberTys.toArray }

namespace PublicGetterDesc

/-- Synthesize the corresponding `view` `InterfaceFunctionDecl` for a `PublicGetterDesc` (`#2439`). -/
def toInterfaceFunctionDecl (d : PublicGetterDesc) : InterfaceFunctionDecl :=
  { ident := d.fieldIdent
    name := d.fieldName
    params := d.paramTys.mapIdx fun idx ty =>
      { ident := mkIdent (Name.mkSimple s!"arg{idx}")
        name := s!"arg{idx}"
        ty := ty }
    returnTys := d.returnTys
    isView := true }

/-- Synthesize the corresponding `ExternalDecl` for a `PublicGetterDesc` on `interfaceName` (`#2439`). -/
def toExternalDecl (interfaceName : String) (d : PublicGetterDesc) : ExternalDecl :=
  { ident := d.fieldIdent
    name := interfaceExternalName interfaceName d.fieldName
    params := d.paramTys
    returnTys := d.returnTys
    linkMode := Compiler.CompilationModel.ForeignLinkMode.external
    interfaceName? := some interfaceName
    isView := true }

end PublicGetterDesc

/-- Resolve a `hopCallView` target against a callee's `StorageFieldDecl` table when
    `methodName` refers to a `public` state-variable getter (`#2439`). -/
def resolveHopCallViewGetter?
    (calleeFields : Array StorageFieldDecl)
    (methodName : String)
    (argCount? : Option Nat := none) : Option PublicGetterDesc := do
  let field ← calleeFields.find? (fun f => f.name == methodName)
  let desc ← publicGetterDescForField? field
  if let some n := argCount? then
    guard (desc.paramTys.size == n)
  pure desc

end Verity.Macro
