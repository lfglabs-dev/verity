import Lean
import Compiler.Modules.ERC20
import Compiler.Modules.Calls
import Compiler.Modules.Precompiles
import Compiler.Selectors
import Compiler.CompilationModel.InternalNaming
import Compiler.Keccak.Sponge
import Verity.Macro.Translate.Parsing
import Verity.Macro.Executable
import Verity.Macro.ExternalCalls
import Verity.Macro.Functions
import Verity.Macro.Interfaces
import Verity.Macro.Internal
import Verity.Macro.Storage
import Verity.Macro.Types
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false


partial def modelParamTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Compiler.CompilationModel.ParamType.uint256)
  | .int256 => `(Compiler.CompilationModel.ParamType.int256)
  | .uint8 => `(Compiler.CompilationModel.ParamType.uint8)
  | .uint16 => `(Compiler.CompilationModel.ParamType.uint16)
  | .uintN bits => `(Compiler.CompilationModel.ParamType.uintN $(natTerm bits))
  | .intN bits => `(Compiler.CompilationModel.ParamType.intN $(natTerm bits))
  | .bytesN bytes => `(Compiler.CompilationModel.ParamType.bytesN $(natTerm bytes))
  | .address => `(Compiler.CompilationModel.ParamType.address)
  | .bytes32 => `(Compiler.CompilationModel.ParamType.bytes32)
  | .bool => `(Compiler.CompilationModel.ParamType.bool)
  | .string => `(Compiler.CompilationModel.ParamType.string)
  | .bytes => `(Compiler.CompilationModel.ParamType.bytes)
  | .array elemTy => do
      `(Compiler.CompilationModel.ParamType.array $(← modelParamTypeTerm elemTy))
  | .fixedArray elemTy size => do
      `(Compiler.CompilationModel.ParamType.fixedArray $(← modelParamTypeTerm elemTy) $(natTerm size))
  | .tuple elemTys => do
      let elemTerms ← elemTys.mapM modelParamTypeTerm
      `(Compiler.CompilationModel.ParamType.tuple [ $[$elemTerms.toArray],* ])
  | .struct _ fields => do
      let elemTerms ← fields.mapM (fun field => modelParamTypeTerm field.snd)
      `(Compiler.CompilationModel.ParamType.tuple [ $[$elemTerms.toArray],* ])
  | .unit => throwError "function parameters cannot be Unit"
  | .newtype name baseType => do
      let baseTerm ← modelParamTypeTerm baseType
      `(Compiler.CompilationModel.ParamType.newtypeOf $(Lean.quote name) $baseTerm)
  | .adt name maxFields => do
      `(Compiler.CompilationModel.ParamType.adt $(Lean.quote name) $(Lean.quote maxFields))

def modelReturnTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `(none)
  | .uint256 => `(some Compiler.CompilationModel.FieldType.uint256)
  | .int256 => `(none)
  | .uint8 => `(none)
  | .uint16 => `(none)
  | .uintN _ | .intN _ | .bytesN _ => `(none)
  | .address => `(some Compiler.CompilationModel.FieldType.address)
  | .bytes32 => `(none)
  | .bool => `(none)
  | .string => `(none)
  | .bytes => `(none)
  | .array _ => `(none)
  | .fixedArray _ _ => `(none)
  | .tuple _ => `(none)
  | .struct _ _ => `(none)
  | .newtype _ baseType => modelReturnTypeTerm baseType
  | .adt _ _ => `(none)  -- ADTs are not directly returnable as single FieldType

partial def modelReturnsTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `([])
  | .uint256 => `([Compiler.CompilationModel.ParamType.uint256])
  | .int256 => `([Compiler.CompilationModel.ParamType.int256])
  | .uint8 => `([Compiler.CompilationModel.ParamType.uint8])
  | .uint16 => `([Compiler.CompilationModel.ParamType.uint16])
  | .uintN bits => `([Compiler.CompilationModel.ParamType.uintN $(natTerm bits)])
  | .intN bits => `([Compiler.CompilationModel.ParamType.intN $(natTerm bits)])
  | .bytesN bytes => `([Compiler.CompilationModel.ParamType.bytesN $(natTerm bytes)])
  | .address => `([Compiler.CompilationModel.ParamType.address])
  | .bytes32 => `([Compiler.CompilationModel.ParamType.bytes32])
  | .bool => `([Compiler.CompilationModel.ParamType.bool])
  | .string => `([Compiler.CompilationModel.ParamType.string])
  | .bytes => `([Compiler.CompilationModel.ParamType.bytes])
  | .array elemTy => do
      `([Compiler.CompilationModel.ParamType.array $(← modelParamTypeTerm elemTy)])
  | .fixedArray elemTy size => do
      `([Compiler.CompilationModel.ParamType.fixedArray $(← modelParamTypeTerm elemTy) $(natTerm size)])
  | .tuple elemTys => do
      let elemTerms ← elemTys.mapM modelParamTypeTerm
      `([ $[$elemTerms.toArray],* ])
  | .struct _ fields => do
      let elemTerms ← fields.mapM (fun field => modelParamTypeTerm field.snd)
      `([Compiler.CompilationModel.ParamType.tuple [ $[$elemTerms.toArray],* ]])
  | .newtype name baseType => do
      let baseTerm ← modelParamTypeTerm baseType
      `([Compiler.CompilationModel.ParamType.newtypeOf $(Lean.quote name) $baseTerm])
  | .adt name maxFields => do
      `([Compiler.CompilationModel.ParamType.adt $(Lean.quote name) $(Lean.quote maxFields)])

partial def valueTypeFromModelParamType? : Compiler.CompilationModel.ParamType → Option ValueType
  | .uint256 => some .uint256
  | .int256 => some .int256
  | .uint8 => some .uint8
  | .uint16 => some .uint16
  | .uintN bits => some (.uintN bits)
  | .intN bits => some (.intN bits)
  | .bytesN bytes => some (.bytesN bytes)
  | .address => some .address
  | .bool => some .bool
  | .bytes32 => some .bytes32
  | .string => some .string
  | .bytes => some .bytes
  | .array elemTy => do
      let elem ← valueTypeFromModelParamType? elemTy
      some (.array elem)
  | .fixedArray elemTy size => do
      let elem ← valueTypeFromModelParamType? elemTy
      some (.fixedArray elem size)
  | .tuple elemTys => do
      let elems ← elemTys.mapM valueTypeFromModelParamType?
      some (.tuple elems)
  | .newtypeOf name baseType => do
      let base ← valueTypeFromModelParamType? baseType
      some (.newtype name base)
  | .adt name maxFields => some (.adt name maxFields)

unsafe def evalQualifiedFunctionSpec
    (fnName : Name) : CommandElabM Compiler.CompilationModel.FunctionSpec := do
  let modelTerm : Term := ⟨(mkIdent (qualifiedFunctionModelName fnName)).raw⟩
  liftTermElabM do
    let expectedType := mkConst ``Compiler.CompilationModel.FunctionSpec
    let expr ← Lean.Elab.Term.elabTermEnsuringType modelTerm expectedType
    Lean.Meta.evalExpr Compiler.CompilationModel.FunctionSpec expectedType expr .unsafe

unsafe def qualifiedFunctionReturnTypes
    (stx : Syntax)
    (fnName : Name) : CommandElabM (Array ValueType) := do
  let spec ←
    try
      unsafe evalQualifiedFunctionSpec fnName
    catch _ =>
      throwErrorAt stx
        s!"unable to inspect qualified helper '{qualifiedFunctionDisplayName fnName}'; expected generated model '{qualifiedFunctionModelName fnName}' to be in scope"
  let mut result := #[]
  for returnTy in spec.returns do
    match valueTypeFromModelParamType? returnTy with
    | some ty => result := result.push ty
    | none =>
        throwErrorAt stx
          s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns unsupported value type {repr returnTy}"
  pure result

mutual
partial def mkTupleContractType (elemTys : List ValueType) : CommandElabM Term := do
  let rec go : List ValueType → CommandElabM Term
    | [] => throwError "tuple types must have at least 2 elements"
    | [ty] => contractValueTypeTerm ty
    | ty :: rest => do
        `(($(← contractValueTypeTerm ty) × $(← go rest)))
  go elemTys

partial def contractValueTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Uint256)
  | .int256 => `(Int256)
  | .uint8 => `(Uint256)
  | .uint16 => `(Uint16)
  | .uintN bits => `(UIntN $(natTerm bits))
  | .intN bits => `(IntN $(natTerm bits))
  | .bytesN bytes => `(BytesN $(natTerm bytes))
  | .address => `(Address)
  | .bytes32 => `(Bytes32)
  | .bool => `(Bool)
  | .string => `(String)
  | .bytes => `(ByteArray)
  | .array elemTy => do
      `(Array $(← contractValueTypeTerm elemTy))
  | .fixedArray elemTy _size => do
      `(Array $(← contractValueTypeTerm elemTy))
  | .tuple elemTys => mkTupleContractType elemTys
  | .unit => `(Unit)
  | .newtype _ baseType => contractValueTypeTerm baseType  -- Erased to base type at contract level
  | .struct name _ => pure (mkIdent (Name.mkSimple name))
  | .adt _ _ => `(Uint256)  -- ADTs represented as tag value at contract level
end

def normalizeTranslatedExprForType
    (expectedTy : ValueType) (source : Term) (expr : Term) : CommandElabM Term := do
  match expectedTy with
  | .uintN bits =>
      `(Compiler.CompilationModel.Expr.bitAnd $expr
          (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1))))
  | .intN bits =>
      `(Compiler.CompilationModel.Expr.signextend
          (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $expr)
  | .bytesN bytes =>
      match stripParens source with
      | `(term| $n:num) =>
          let literal ← natFromSyntax n
          let normalized := (literal % 2 ^ (8 * bytes)) * 2 ^ (8 * (32 - bytes))
          `(Compiler.CompilationModel.Expr.literal $(natTerm normalized))
      | _ =>
          let mask := (2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))
          `(Compiler.CompilationModel.Expr.bitAnd $expr
              (Compiler.CompilationModel.Expr.literal $(natTerm mask)))
  | .newtype _ baseType => normalizeTranslatedExprForType baseType source expr
  | _ => pure expr

def immutableHiddenName (imm : ImmutableDecl) : String :=
  s!"__immutable_{imm.name}"

def storageFieldFootprintSize (field : StorageFieldDecl) : Nat :=
  match field.ty with
  | .scalar (.adt _ maxFields) => maxFields + 1
  | _ => 1

def immutableSlotIndex (fields : Array StorageFieldDecl) (idx : Nat) : Nat :=
  let nextUserSlot := fields.foldl (fun maxSlot field =>
    max maxSlot (field.slotNum + storageFieldFootprintSize field)) 0
  nextUserSlot + idx

def immutableSlotIdent (imm : ImmutableDecl) : Ident :=
  mkIdent (Name.mkSimple s!"__verity_immutable_slot_{imm.name}")

def immutableStorageFieldDecl
    (fields : Array StorageFieldDecl)
    (imm : ImmutableDecl)
    (idx : Nat) : StorageFieldDecl :=
  {
    ident := immutableSlotIdent imm
    name := immutableHiddenName imm
    ty := match imm.ty with
      | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
      | .bytes32 | .bool => .scalar .uint256
      | .address => .scalar .address
      | _ => .scalar imm.ty
    slotNum := immutableSlotIndex fields idx
    isTransient := false
    adtInfo? := none
  }

def validateImmutableType (imm : ImmutableDecl) : CommandElabM Unit :=
  match imm.ty with
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => pure ()
  | _ =>
      throwErrorAt imm.ident
        s!"contract immutables currently support only Uint256, Int256, Uint8, Address, Bytes32, and Bool; '{imm.name}' uses unsupported type"

def validateImmutableBodyType
    (imm : ImmutableDecl)
    (ctorParams : Array ParamDecl) : CommandElabM Unit := do
  let expectedTy ← contractValueTypeTerm imm.ty
  let mut wrappedBody : Term := imm.body
  wrappedBody ← `(term| (($wrappedBody : $expectedTy)))
  for param in ctorParams.reverse do
    wrappedBody ← `(term| fun ($(param.ident) : $(← contractValueTypeTerm param.ty)) => $wrappedBody)
  liftTermElabM do
    discard <| Lean.Elab.Term.elabTerm wrappedBody none

partial def containsAdtValueType : ValueType → Bool
  | .adt _ _ => true
  | .newtype _ baseType => containsAdtValueType baseType
  | .array elemTy => containsAdtValueType elemTy
  | .fixedArray elemTy _ => containsAdtValueType elemTy
  | .tuple elemTys => elemTys.any containsAdtValueType
  | .struct _ fields => fields.any (fun field => containsAdtValueType field.snd)
  | _ => false

def rejectExecutableBoundaryAdt
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  if containsAdtValueType ty then
    throwErrorAt stx
      s!"{context} uses an ADT at the executable contract boundary. ADT storage is supported, but ABI/function boundary ADT lowering is not yet implemented; pass scalar fields explicitly or keep the ADT in storage."

def tupleElemsFromTerm? (stx : Term) : Option (Array Term) :=
  tupleElemsFromSyntax? (stripParens stx).raw |>.map (·.map (fun syn => ⟨syn⟩))

def throwNonCompileTimeConstantError (stx : Syntax) (what : String) : CommandElabM α :=
  throwErrorAt stx s!"contract constants must be compile-time expressions; '{what}' is runtime-dependent"

def lookupStructMemberDecl
    (fields : Array StorageFieldDecl)
    (fieldName memberName : String)
    (expectNested : Bool) : CommandElabM StructMemberDecl := do
  let field ←
    match fields.find? (fun f => f.name == fieldName || f.aliases.contains fieldName) with
    | some f => pure f
    | none => throwError s!"unknown storage field '{fieldName}'"
  let members ←
    match field.ty with
    | .mappingStruct _ members =>
        if expectNested then
          throwError s!"field '{fieldName}' is not a nested struct mapping"
        pure members
    | .mappingStruct2 _ _ members =>
        if expectNested then pure members
        else throwError s!"field '{fieldName}' is a nested struct mapping; use structMember2/setStructMember2"
    | _ =>
        if expectNested then
          throwError s!"field '{fieldName}' is not a nested struct mapping"
        else
          throwError s!"field '{fieldName}' is not a struct-valued mapping"
  match members.find? (fun member => member.name == memberName) with
  | some member => pure member
  | none => throwError s!"unknown struct member '{memberName}' on field '{fieldName}'"

def lookupStorageField (fields : Array StorageFieldDecl) (name : String) : CommandElabM StorageFieldDecl := do
  match fields.find? (fun f => f.name == name || f.aliases.contains name) with
  | some f => pure f
  | none => throwError s!"unknown storage field '{name}'"

def resolveInitGuardField
    (fields : Array StorageFieldDecl)
    (guard : InitGuardDecl)
    (stx : Syntax) : CommandElabM StorageFieldDecl := do
  let field ←
    match guard with
    | .initializer _ fieldName => lookupStorageField fields fieldName
    | .reinitializer _ fieldName _ => lookupStorageField fields fieldName
  match field.ty with
  | .scalar .uint256 => pure field
  | _ =>
      throwErrorAt stx
        s!"initializer guard field '{field.name}' must be a Uint256 storage slot"

def initGuardRequireMessage : InitGuardDecl → String
  | .initializer .. => "initializer already run"
  | .reinitializer _ _ version => s!"reinitializer({version}) already run"

def initGuardVersionTerm (version : Nat) : Term :=
  natTerm version

def initGuardPreludeStmtTerms
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.initGuard? with
  | none => pure #[]
  | some guard =>
      let field ← resolveInitGuardField fields guard fn.ident
      let message := strTerm (initGuardRequireMessage guard)
      match guard with
      | .initializer _ _ =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.eq
                    (Compiler.CompilationModel.Expr.storage $(strTerm field.name))
                    (Compiler.CompilationModel.Expr.literal 0))
                  $message),
            ← `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm field.name)
                  (Compiler.CompilationModel.Expr.literal 1))
          ]
      | .reinitializer _ _ version =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.lt
                    (Compiler.CompilationModel.Expr.storage $(strTerm field.name))
                    (Compiler.CompilationModel.Expr.literal $(initGuardVersionTerm version)))
                  $message),
            ← `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm field.name)
                  (Compiler.CompilationModel.Expr.literal $(initGuardVersionTerm version)))
          ]

def mkInitGuardedBody
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM Term := do
  match fn.initGuard? with
  | none => pure fn.body
  | some guard =>
      let field ← resolveInitGuardField fields guard fn.ident
      let currentVersion := mkIdent (Name.mkSimple s!"__verity_init_version_{field.name}")
      let message := strTerm (initGuardRequireMessage guard)
      match fn.body with
      | `(term| do $[$elems:doElem]*) =>
          match guard with
          | .initializer _ _ =>
              `(do
                  let $currentVersion ← getStorage $field.ident
                  require ($currentVersion == 0) $message
                  setStorage $field.ident 1
                  $[$elems:doElem]*)
          | .reinitializer _ _ version =>
              `(do
                  let $currentVersion ← getStorage $field.ident
                  require ($currentVersion < $(initGuardVersionTerm version)) $message
                  setStorage $field.ident $(initGuardVersionTerm version)
                  $[$elems:doElem]*)
      | _ => throwErrorAt fn.body "function body must be a do block"

/-- Classifies a `requires(role)` annotation by the shape of the named storage
    field. `scalarAddress` is the canonical `onlyOwner` shape — a scalar
    Address-typed slot; the macro injects `require (caller == storage[slot])`.
    `mappingAddress` is the role-as-mapping shape (e.g. `onlyRelayer`,
    `onlyMinter`) — a `mapping(address => uint256)` slot used as a 0/1 flag;
    the macro injects `require (storage[slot][caller] != 0)`. (verity#1837) -/
inductive ResolvedRoleKind where
  | scalarAddress
  | mappingAddress

/-- Resolve the storage field referenced by a `requires(role)` annotation.
    Accepts either an Address-typed scalar field (`onlyOwner`-style) or an
    `Address → Uint256` mapping field (`onlyRelayer`-style, verity#1837). -/
def resolveRoleField
    (fields : Array StorageFieldDecl) (roleDecls : Array RoleDecl) (roleIdent : Ident) (fnIdent : Ident)
    : CommandElabM (StorageFieldDecl × ResolvedRoleKind × String) := do
  let roleName := toString roleIdent.getId
  let resolveField (fieldName : String) (diagName : String) := do
    match fields.find? (fun f => f.name == fieldName) with
    | none =>
        throwErrorAt roleIdent s!"function '{toString fnIdent.getId}': requires({diagName}) references role backing field '{fieldName}', but no such storage field exists; known fields: {(fields.map (·.name)).toList}"
    | some field =>
        match field.ty with
        | .scalar .address | .scalar (.newtype _ .address) =>
            pure (field, .scalarAddress, diagName)
        | .mappingAddressToUint256 =>
            pure (field, .mappingAddress, diagName)
        | _ => throwErrorAt roleIdent s!"function '{toString fnIdent.getId}': requires({diagName}) must reference an explicit role or an Address-typed scalar / Address→Uint256 role field, but backing field '{fieldName}' has an unsupported role shape"
  match roleDecls.find? (fun r => r.name == roleName) with
  | some role => resolveField role.fieldName role.name
  | none =>
      match fields.find? (fun f => f.name == roleName) with
      | some _ => resolveField roleName roleName
      | none =>
          throwErrorAt roleIdent s!"function '{toString fnIdent.getId}': requires references unknown role '{roleName}'; known roles: {(roleDecls.map (·.name)).toList}; legacy storage fields: {(fields.map (·.name)).toList}"

/-- Generate IR-level prelude statements for a `requires(role)` annotation.
    Scalar Address: injects `Stmt.require (Expr.eq Expr.caller (Expr.storageAddr roleField)) message`.
    Address→Uint256 mapping: injects `Stmt.require (Expr.mapping roleField Expr.caller) message`
    (the truthy check works because the value is 0 or non-zero).
    (#1728, Axis 2 Step 2c; mapping-keyed extension verity#1837) -/
def roleGuardPreludeStmtTerms
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.requiresRole with
  | none => pure #[]
  | some roleIdent =>
      let (field, kind, roleName) ← resolveRoleField fields roleDecls roleIdent fn.ident
      let message := strTerm s!"Access denied: caller is not {roleName}"
      match kind with
      | .scalarAddress =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.eq
                    (Compiler.CompilationModel.Expr.caller)
                    (Compiler.CompilationModel.Expr.storageAddr $(strTerm field.name)))
                  $message)
          ]
      | .mappingAddress =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.mapping $(strTerm field.name)
                    Compiler.CompilationModel.Expr.caller)
                  $message)
          ]

/-- Transform the source-level do-block body to inject a role access control check
    at the start. Scalar Address: `let __sender ← msgSender; let __roleHolder ← getStorageAddr field;
    require (__sender == __roleHolder) message`. Address→Uint256 mapping:
    `let __sender ← msgSender; let __roleValue ← getMapping field __sender;
    require (__roleValue != 0) message`.
    (#1728, Axis 2 Step 2c; mapping-keyed extension verity#1837) -/
def mkRoleGuardedBody
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (fn : FunctionDecl) : CommandElabM Term := do
  match fn.requiresRole with
  | none => pure fn.body
  | some roleIdent =>
      let (field, kind, roleName) ← resolveRoleField fields roleDecls roleIdent fn.ident
      let senderVar := mkIdent (Name.mkSimple s!"__verity_role_sender_{field.name}")
      let message := strTerm s!"Access denied: caller is not {roleName}"
      match fn.body with
      | `(term| do $[$elems:doElem]*) =>
          match kind with
          | .scalarAddress =>
              let holderVar := mkIdent (Name.mkSimple s!"__verity_role_holder_{field.name}")
              `(do
                  let $senderVar ← msgSender
                  let $holderVar ← getStorageAddr $field.ident
                  require ($senderVar == $holderVar) $message
                  $[$elems:doElem]*)
          | .mappingAddress =>
              let valueVar := mkIdent (Name.mkSimple s!"__verity_role_value_{field.name}")
              `(do
                  let $senderVar ← msgSender
                  let $valueVar ← getMapping $field.ident $senderVar
                  require ($valueVar != 0) $message
                  $[$elems:doElem]*)
      | _ => throwErrorAt fn.body "function body must be a do block"

def mkImmutableBoundBody
    (fields : Array StorageFieldDecl)
    (immutableDecls : Array ImmutableDecl)
    (fn : FunctionDecl)
    (body : Term) : CommandElabM Term := do
  let visibleImmutables := immutableDecls.filter fun imm =>
    !fn.params.any (fun p => p.name == imm.name)
  match body with
  | `(term| do $[$elems:doElem]*) =>
      let preludeElemGroups ← visibleImmutables.zipIdx.mapM fun (imm, idx) => do
        let slotField := immutableStorageFieldDecl fields imm idx
        match imm.ty with
        | .uint256 | .uint8 | .bytes32 =>
            pure #[← `(doElem| let $(imm.ident) ← getStorage $(slotField.ident))]
        | .uintN bits =>
            pure #[← `(doElem| let $(imm.ident) := narrowUInt $(natTerm bits) (← getStorage $(slotField.ident)))]
        | .int256 =>
            pure #[← `(doElem| let $(imm.ident) := toInt256 (← getStorage $(slotField.ident)))]
        | .intN bits =>
            pure #[← `(doElem| let $(imm.ident) := narrowInt $(natTerm bits) (← getStorage $(slotField.ident)))]
        | .bytesN bytes =>
            pure #[← `(doElem| let $(imm.ident) := narrowBytes $(natTerm bytes) (← getStorage $(slotField.ident)))]
        | .bool =>
            let rawName := mkIdent (Name.mkSimple s!"__verity_immutable_raw_{imm.name}")
            pure #[
              ← `(doElem| let $rawName ← getStorage $(slotField.ident)),
              ← `(doElem| let $(imm.ident) := ($rawName != 0))
            ]
        | .address =>
            pure #[← `(doElem| let $(imm.ident) ← getStorageAddr $(slotField.ident))]
        | _ => throwErrorAt imm.ident s!"immutable '{imm.name}' uses unsupported type"
      let preludeElems := preludeElemGroups.foldl (· ++ ·) #[]
      `(do $[$preludeElems:doElem]* $[$elems:doElem]*)
  | _ => throwErrorAt body "function body must be a do block"

def expectStringLiteral (stx : Term) : CommandElabM String :=
  match (stripParens stx).raw.isStrLit? with
  | some s => pure s
  | none => throwErrorAt stx "expected string literal"

def expectStringOrIdent (stx : Term) : CommandElabM String := do
  match stripParens stx with
  | `(term| $id:ident) => pure (toString id.getId)
  | other => expectStringLiteral other

def expectStringList (stx : Term) : CommandElabM (Array String) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      xs.mapM expectStringOrIdent
  | _ => throwErrorAt stx "expected list literal [..]"

def tupleBinderNames? (stx : Syntax) : Option (Array (Option String)) := do
  let elems ← tupleElemsFromSyntax? stx
  elems.mapM fun elem =>
    match elem with
    | .ident _ raw _ _ => some raw.toString
    | .node _ `Lean.Parser.Term.hole _ => some none
    | _ => none

def ensureFreshLocalNames
    (locals : Array String)
    (names : Array (Option String))
    (stx : Syntax) : CommandElabM Unit := do
  let boundNames := names.filterMap id
  let rec firstDuplicate (seen : Array String) (rest : Array String) (idx : Nat) : Option String :=
    if h : idx < rest.size then
      let name := rest[idx]
      if seen.contains name then
        some name
      else
        firstDuplicate (seen.push name) rest (idx + 1)
    else
      none
  match firstDuplicate #[] boundNames 0 with
  | some dup => throwErrorAt stx s!"duplicate local variable '{dup}'"
  | none => pure ()
  for name in boundNames do
    if locals.contains name then
      throwErrorAt stx s!"duplicate local variable '{name}'"

def freshDiscardName (usedNames : List String) (idx : Nat) : String :=
  let base := s!"__tuple_discard_{idx}"
  if !usedNames.contains base then
    base
  else
    let rec go (suffix : Nat) (remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      if !usedNames.contains candidate then
        candidate
      else
        match remaining with
        | 0 => s!"{base}_fresh"
        | n + 1 => go (suffix + 1) n
    go 1 usedNames.length

def tupleParamElemExprs?
    (params : Array ParamDecl)
    (name : String) : CommandElabM (Option (Array Term)) := do
  match params.find? (fun p => p.name == name) with
  | some p =>
      match p.ty with
      | .tuple elemTys => do
          let exprs ← (elemTys.toArray.zipIdx).mapM fun (_ty, idx) =>
            `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_{idx}"))
          pure (some exprs)
      | _ => pure none
  | none => pure none

def isTupleComponentRef (params : Array ParamDecl) (name : String) : Bool :=
  -- Check if `name` matches `<paramName>_<digit>` for a tuple-typed param
  match name.splitOn "_" with
  | [baseName, indexStr] =>
      match indexStr.toNat? with
      | some idx =>
          params.any fun p =>
            p.name == baseName &&
            match p.ty with
            | .tuple elemTys => idx < elemTys.length
            | _ => false
      | none => false
  | _ => false

def lookupVarExpr (params : Array ParamDecl) (locals : Array String) (name : String) : CommandElabM Term := do
  if params.any (fun p => p.name == name) then
    `(Compiler.CompilationModel.Expr.param $(strTerm name))
  else if isTupleComponentRef params name then
    `(Compiler.CompilationModel.Expr.param $(strTerm name))
  else if locals.contains name then
    `(Compiler.CompilationModel.Expr.localVar $(strTerm name))
  else
    throwError s!"unknown variable '{name}'"

inductive LocalSource where
  | value
  | arrayElement (paramName : String) (index : Term) (elemTy : ValueType)
  | memoryArray
  | externalStaticStruct (fields : List (String × String))

structure TypedLocal where
  name : String
  ty : ValueType
  source : LocalSource := .value
  interfaceName? : Option String := none

def mkTypedLocal (name : String) (ty : ValueType) (interfaceName? : Option String := none) : TypedLocal :=
  { name, ty, interfaceName? }

def memoryArrayDataOffsetName (name : String) : String :=
  s!"{name}_data_offset"

def memoryArrayLengthName (name : String) : String :=
  s!"{name}_length"

def typedLocalNames (locals : Array TypedLocal) : Array String :=
  locals.map (·.name)

def matchesBareName (actual bare : String) : Bool :=
  actual == bare || actual.endsWith s!".{bare}"

def declaredNameMatches (query declared : String) : Bool :=
  matchesBareName query declared || matchesBareName declared query

def contextAccessorBareName? (name : String) : Option String :=
  if matchesBareName name "msgSender" then some "msgSender"
  else if matchesBareName name "msgValue" then some "msgValue"
  else if matchesBareName name "selfBalance" then some "selfBalance"
  else if matchesBareName name "blockTimestamp" then some "blockTimestamp"
  else if matchesBareName name "blockNumber" then some "blockNumber"
  else if matchesBareName name "blobbasefee" then some "blobbasefee"
  else if matchesBareName name "contractAddress" then some "contractAddress"
  else if matchesBareName name "txOrigin" then some "txOrigin"
  else if matchesBareName name "chainid" then some "chainid"
  else none

def findContextAccessorShadowName?
    (params : Array ParamDecl) (locals : Array String) (name : String) : Option String :=
  match params.find? (fun p => matchesBareName p.name name) with
  | some param => some param.name
  | none => locals.find? (fun localName => matchesBareName localName name)

def isSignedWordValueType : ValueType → Bool
  | .int256 | .intN _ => true
  | .newtype _ baseType => isSignedWordValueType baseType
  | _ => false

def isWordLikeValueType : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 => true
  | .newtype _ baseType => isWordLikeValueType baseType
  | _ => false

def isSingleWordStaticValueType : ValueType → Bool
  | .bool => true
  | .newtype _ baseType => isSingleWordStaticValueType baseType
  | ty => isWordLikeValueType ty

def externalCallDynamicArgSupported (ty : ValueType) : Bool :=
  match ty with
  | .array elemTy => isSingleWordStaticValueType elemTy
  | .bytes | .string => true
  | _ => false

partial def staticAbiWordCount? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => some 1
  | .fixedArray elemTy size => do
      let elemWords ← staticAbiWordCount? elemTy
      some (size * elemWords)
  | .tuple elemTys =>
      elemTys.foldl
        (fun acc ty =>
          match acc, staticAbiWordCount? ty with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .struct _ fields =>
      fields.foldl
        (fun acc field =>
          match acc, staticAbiWordCount? field.snd with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .newtype _ baseType => staticAbiWordCount? baseType
  | _ => none

partial def staticAbiLeafNames? : ValueType → Option (List String)
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => some [""]
  | .fixedArray elemTy size => do
      let elemNames ← staticAbiLeafNames? elemTy
      let mut out : List String := []
      for idx in List.range size do
        for suffix in elemNames do
          out := out ++ [if suffix == "" then toString idx else s!"{idx}_{suffix}"]
      some out
  | .tuple elemTys => do
      let mut out : List String := []
      for (ty, idx) in elemTys.zipIdx do
        let elemNames ← staticAbiLeafNames? ty
        for suffix in elemNames do
          out := out ++ [if suffix == "" then toString idx else s!"{idx}_{suffix}"]
      some out
  | .struct _ fields => do
      let mut out : List String := []
      for (fieldName, fieldTy) in fields do
        let fieldNames ← staticAbiLeafNames? fieldTy
        for suffix in fieldNames do
          out := out ++ [if suffix == "" then fieldName else s!"{fieldName}_{suffix}"]
      some out
  | .newtype _ baseType => staticAbiLeafNames? baseType
  | _ => none

partial def staticStructDirectFieldLocals?
    (baseName : String) (ty : ValueType) : Option (List (String × String)) := do
  let .struct _ fields := ty | none
  let mut out : List (String × String) := []
  for (fieldName, fieldTy) in fields do
    unless isSingleWordStaticValueType fieldTy do
      failure
    out := out ++ [(fieldName, s!"{baseName}_{fieldName}")]
  some out

def flattenExternalResultNames
    (baseName : String) (ty : ValueType) : CommandElabM (List String) := do
  match staticAbiLeafNames? ty with
  | some [""] => pure [baseName]
  | some suffixes => pure (suffixes.map fun suffix => s!"{baseName}_{suffix}")
  | none =>
      throwError s!"external result '{baseName}' has a dynamic type; bind dynamic external returns explicitly"

partial def abiLocalHeadWordCount? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool
  | .string | .bytes | .array _ => some 1
  | .fixedArray elemTy size => do
      match staticAbiWordCount? elemTy with
      | some elemWords => some (size * elemWords)
      | none => some size
  | .tuple elemTys =>
      elemTys.foldl
        (fun acc ty =>
          match acc, abiLocalHeadWordCount? ty with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .struct _ fields =>
      fields.foldl
        (fun acc field =>
          match acc, abiLocalHeadWordCount? field.snd with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .newtype _ baseType => abiLocalHeadWordCount? baseType
  | .adt _ _ | .unit => none

partial def valueTypeUsesDynamicData : ValueType → Bool
  | .string | .bytes | .array _ => true
  | .fixedArray elemTy _ => valueTypeUsesDynamicData elemTy
  | .tuple elemTys => elemTys.any valueTypeUsesDynamicData
  | .struct _ fields => fields.any (fun field => valueTypeUsesDynamicData field.snd)
  | .newtype _ baseType => valueTypeUsesDynamicData baseType
  | .adt _ _ => false  -- ADTs are stored as tag + fixed-width slots, not dynamic
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool | .unit => false

partial def abiParentHeadWordCount? (ty : ValueType) : Option Nat :=
  match ty with
  | .string | .bytes | .array _ => some 1
  | .fixedArray elemTy size =>
      if valueTypeUsesDynamicData (.fixedArray elemTy size) then
        some 1
      else
        abiLocalHeadWordCount? (.fixedArray elemTy size)
  | .tuple _ | .struct _ _ =>
      if valueTypeUsesDynamicData ty then
        some 1
      else
        abiLocalHeadWordCount? ty
  | .newtype _ baseType => abiParentHeadWordCount? baseType
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => some 1
  | .adt _ _ | .unit => none

def classifyWordArithmeticResultType
    (stx : Syntax)
    (context : String)
    (lhsTy rhsTy : ValueType) : CommandElabM ValueType := do
  unless isWordLikeValueType lhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr lhsTy}"
  unless isWordLikeValueType rhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr rhsTy}"
  if lhsTy == rhsTy then
    match lhsTy with
    | .uintN _ | .intN _ => return lhsTy
    | _ => pure ()
  if isSignedWordValueType lhsTy || isSignedWordValueType rhsTy then
    if lhsTy == .int256 && rhsTy == .int256 then
      pure .int256
    else
      throwErrorAt stx
        s!"{context} requires explicit casts when mixing Int256 with non-Int256 words; got {reprStr lhsTy} and {reprStr rhsTy}"
  else
    pure .uint256

def classifyUnsignedWordArithmeticResultType
    (stx : Syntax)
    (context : String)
    (lhsTy rhsTy : ValueType) : CommandElabM ValueType := do
  unless isWordLikeValueType lhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr lhsTy}"
  unless isWordLikeValueType rhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr rhsTy}"
  pure .uint256

def isNatLiteralTerm (stx : Term) : Bool :=
  match stripParens stx with
  | `(term| $_n:num) => true
  | _ => false

def numericLiteralCompatibleValueType : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _ => true
  | .newtype _ baseType => numericLiteralCompatibleValueType baseType
  | _ => false

def argumentTypeMatchesParam (arg : Term) (argTy paramTy : ValueType) : Bool :=
  argTy == paramTy ||
    (argTy == .uint256 && paramTy == .bytes32) ||
    (argTy == .bytes32 && paramTy == .uint256) ||
    (argTy == .uint256 && isNatLiteralTerm arg && numericLiteralCompatibleValueType paramTy)

def argumentTypesMatchParams (args : Array Term) (argTypes : Array ValueType)
    (params : Array ParamDecl) : Bool :=
  args.size == params.size && Id.run do
    for idx in [:args.size] do
      let some arg := args[idx]? | return false
      let some argTy := argTypes[idx]? | return false
      let some param := params[idx]? | return false
      unless argumentTypeMatchesParam arg argTy param.ty do
        return false
    return true

def preferSignedNumericLiteralPeer
    (lhs rhs : Term)
    (lhsTy rhsTy : ValueType) : ValueType × ValueType :=
  let lhsTy :=
    if lhsTy == .uint256 && rhsTy == .int256 && isNatLiteralTerm lhs then .int256 else lhsTy
  let rhsTy :=
    if rhsTy == .uint256 && lhsTy == .int256 && isNatLiteralTerm rhs then .int256 else rhsTy
  (lhsTy, rhsTy)

def preferNarrowNumericLiteralPeer
    (lhs rhs : Term)
    (lhsTy rhsTy : ValueType) : ValueType × ValueType :=
  let lhsTy :=
    if lhsTy == .uint256 && isNatLiteralTerm lhs then
      match rhsTy with
      | .uintN _ | .intN _ => rhsTy
      | _ => lhsTy
    else lhsTy
  let rhsTy :=
    if rhsTy == .uint256 && isNatLiteralTerm rhs then
      match lhsTy with
      | .uintN _ | .intN _ => lhsTy
      | _ => rhsTy
    else rhsTy
  preferSignedNumericLiteralPeer lhs rhs lhsTy rhsTy

def lookupTypedLocalType? (locals : Array TypedLocal) (name : String) : Option ValueType :=
  locals.findSome? fun localTy =>
    if localTy.name == name then some localTy.ty else none

def lookupInterfaceName?
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (name : String) : Option String :=
  params.findSome? (fun p =>
    if p.name == name then p.interfaceName? else none)
  <|> locals.findSome? (fun localTy =>
    if localTy.name == name then localTy.interfaceName? else none)

def interfaceNameOfTerm?
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option String) := do
  match stripParens stx with
  | `(term| $ident:ident) => pure (lookupInterfaceName? params locals (toString ident.getId))
  | _ => pure none

def tupleParamElemType? (params : Array ParamDecl) (name : String) : Option ValueType :=
  match name.splitOn "_" with
  | [baseName, indexStr] =>
      match indexStr.toNat? with
      | some idx =>
          params.findSome? fun p =>
            if p.name == baseName then
              match p.ty with
              | .tuple elemTys => elemTys.toArray[idx]?
              | _ => none
            else
              none
      | none => none
  | _ => none

partial def structProjectionPath? (stx : Term) : Option (Term × List String) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      match (toString id.getId).splitOn "." with
      | root :: field :: rest =>
          some (mkIdent (Name.mkSimple root), field :: rest)
      | _ => none
  | `(term| $base:term.$field:ident) =>
      let fieldPath := (toString field.getId).splitOn "."
      match structProjectionPath? base with
      | some (root, path) => some (root, path ++ fieldPath)
      | none => some (base, fieldPath)
  | _ => none

partial def structFieldPath?
    (ty : ValueType)
    (path : List String)
    (indices : List Nat := []) : Option (ValueType × List Nat) :=
  -- The returned indices are the recursive tuple binding path used by
  -- ParamLoading.staticParamBindingNames, not flattened ABI word offsets.
  match path with
  | [] => some (ty, indices)
  | fieldName :: rest =>
      match ty with
      | .struct _ fields =>
          fields.zipIdx.findSome? fun (field, idx) =>
            if field.fst == fieldName then
              structFieldPath? field.snd rest (indices ++ [idx])
            else
              none
      | _ => none

partial def structFieldHeadOffset?
    (ty : ValueType)
    (path : List String)
    (baseOffset : Nat := 0) : Option (ValueType × Nat) :=
  match path with
  | [] => none
  | fieldName :: rest =>
      match ty with
      | .struct _ fields =>
          let rec go (remaining : List (String × ValueType)) (curOffset : Nat) : Option (ValueType × Nat) :=
            match remaining with
            | [] => none
            | (name, fieldTy) :: more =>
                if name == fieldName then
                  match rest with
                  | [] => some (fieldTy, curOffset)
                  | _ =>
                      if valueTypeUsesDynamicData fieldTy then
                        none
                      else
                        structFieldHeadOffset? fieldTy rest curOffset
                else
                  match abiParentHeadWordCount? fieldTy with
                  | some n => go more (curOffset + n)
                  | none => none
          go fields baseOffset
      | _ => none

def paramStructProjectionResolved?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType × ValueType) := do
  let resolve (rootName : String) (path : List String) := do
    let param ← params.find? (fun p => p.name == rootName)
    let (fieldTy, indices) ← structFieldPath? param.ty path
    if indices.isEmpty then
      none
    else
      some (String.intercalate "_" (rootName :: indices.map toString), fieldTy, param.ty)
  match (stripParens stx).raw with
  | .ident _ raw _ _ =>
      let parts := raw.toString.splitOn "."
      let rec findParamPath : List String → Option (String × List String)
        | [] | [_] => none
        | rootName :: fieldName :: rest =>
            if params.any (fun p => p.name == rootName) then
              some (rootName, fieldName :: rest)
            else
              findParamPath (fieldName :: rest)
      match findParamPath parts with
      | some (rootName, path) => resolve rootName path
      | none => none
  | _ =>
      let (root, path) ← structProjectionPath? stx
      match stripParens root with
      | `(term| $id:ident) => resolve (toString id.getId) path
      | _ => none

def arrayElementStructProjectionResolved?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let (root, path) ← structProjectionPath? stx
  match stripParens root with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName ←
        match stripParens name with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      let elemTy ← match param.ty with
        | .array elemTy => some elemTy
        | _ => none
      let (fieldTy, wordOffset) ← structFieldHeadOffset? elemTy path
      some (paramName, index, fieldTy, elemTy, wordOffset)
  | _ => none

def arrayElementStructProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← arrayElementStructProjectionResolved? params stx
  if isSingleWordStaticValueType fieldTy then
    some resolved
  else
    none

/-- Resolve `(arrayElement <param> <i>).<dynamicField>` projections whose
    projected field is a dynamically-sized member (`Array<T>`, `bytes`,
    `string`). Returns `(paramName, index, fieldTy, elemTy, wordOffset)`
    just like `arrayElementStructProjection?`, but with the dynamic-leaf
    type test inverted: this helper succeeds exactly when the projected
    field is dynamic (so the macro can lower into
    `Expr.arrayElementDynamicMemberLength` / future G2 element-indexing
    constructors). (verity#1849, G1) -/
def arrayElementDynamicMemberProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← arrayElementStructProjectionResolved? params stx
  match fieldTy with
  | .array _ | .bytes | .string => some resolved
  | _ => none

def paramStructProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) := do
  let (paramName, fieldTy, rootTy) ← paramStructProjectionResolved? params stx
  if isSingleWordStaticValueType fieldTy && !valueTypeUsesDynamicData rootTy then
    some (paramName, fieldTy)
  else
    none

/-- Resolve a `param.field[.field2…]` projection where `param` is a struct
    parameter whose ABI encoding is dynamic (carries nested dynamic
    members) and the projected leaf is a single-word static value at a
    fixed head offset. Returns `(paramName, fieldTy, wordOffset)`. The
    word offset is the head-word index relative to the parameter's
    `{name}_data_offset`, which after verity#1839 points at the first
    head word of the encoded tuple (no length prefix). (verity#1832) -/
def paramDynamicHeadProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType × Nat) := do
  let (root, path) ←
    match (stripParens stx).raw with
    | .ident _ raw _ _ =>
        let parts := raw.toString.splitOn "."
        let rec findParamPath : List String → Option (String × List String)
          | [] | [_] => none
          | rootName :: fieldName :: rest =>
              if params.any (fun p => p.name == rootName) then
                some (rootName, fieldName :: rest)
              else
                findParamPath (fieldName :: rest)
        findParamPath parts
    | _ =>
        let (rootStx, path) ← structProjectionPath? stx
        match stripParens rootStx with
        | `(term| $id:ident) => some (toString id.getId, path)
        | _ => none
  let param ← params.find? (fun p => p.name == root)
  if !valueTypeUsesDynamicData param.ty then
    none
  else
    let (fieldTy, wordOffset) ← structFieldHeadOffset? param.ty path
    if isSingleWordStaticValueType fieldTy then
      some (root, fieldTy, wordOffset)
    else
      none

def paramDynamicMemberProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType × Nat) := do
  let (root, path) ←
    match (stripParens stx).raw with
    | .ident _ raw _ _ =>
        let parts := raw.toString.splitOn "."
        let rec findParamPath : List String → Option (String × List String)
          | [] | [_] => none
          | rootName :: fieldName :: rest =>
              if params.any (fun p => p.name == rootName) then
                some (rootName, fieldName :: rest)
              else
                findParamPath (fieldName :: rest)
        findParamPath parts
    | _ =>
        let (rootStx, path) ← structProjectionPath? stx
        match stripParens rootStx with
        | `(term| $id:ident) => some (toString id.getId, path)
        | _ => none
  let param ← params.find? (fun p => p.name == root)
  if !valueTypeUsesDynamicData param.ty then
    none
  else
    let (fieldTy, wordOffset) ← structFieldHeadOffset? param.ty path
    match fieldTy with
    | .array _ | .bytes | .string => some (root, fieldTy, wordOffset)
    | _ => none

def paramDynamicStaticCompositeProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType × Nat) := do
  let (root, path) ←
    match (stripParens stx).raw with
    | .ident _ raw _ _ =>
        let parts := raw.toString.splitOn "."
        let rec findParamPath : List String → Option (String × List String)
          | [] | [_] => none
          | rootName :: fieldName :: rest =>
              if params.any (fun p => p.name == rootName) then
                some (rootName, fieldName :: rest)
              else
                findParamPath (fieldName :: rest)
        findParamPath parts
    | _ =>
        let (rootStx, path) ← structProjectionPath? stx
        match stripParens rootStx with
        | `(term| $id:ident) => some (toString id.getId, path)
        | _ => none
  let param ← params.find? (fun p => p.name == root)
  let (fieldTy, wordOffset) ← structFieldHeadOffset? param.ty path
  if !valueTypeUsesDynamicData fieldTy && !isSingleWordStaticValueType fieldTy then
    some (root, fieldTy, wordOffset)
  else
    none

def arrayElementDynamicTupleArg?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType) := do
  match stripParens stx with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName ←
        match stripParens name with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      let elemTy ← match param.ty with
        | .array elemTy => some elemTy
        | _ => none
      if valueTypeUsesDynamicData elemTy then
        some (paramName, index, elemTy)
      else
        none
  | _ => none

def arrayElementAliasSource?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType) := do
  match stripParens stx with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName ←
        match stripParens name with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      let elemTy ← match param.ty with
        | .array elemTy => some elemTy
        | _ => none
      if valueTypeUsesDynamicData elemTy then
        some (paramName, index, elemTy)
      else
        none
  | _ => none

def localArrayElementAlias?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × Term × ValueType) := do
  let name ←
    match stripParens stx with
    | `(term| $id:ident) => some (toString id.getId)
    | _ => none
  let localDecl ← locals.find? (fun localDecl => localDecl.name == name)
  match localDecl.source with
  | .arrayElement paramName index elemTy => some (paramName, index, elemTy)
  | .value => none
  | .memoryArray => none
  | .externalStaticStruct _ => none

def localExternalStaticStructProjection?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × ValueType) := do
  let (rootName, path) ←
    match (stripParens stx).raw with
    | .ident _ raw _ _ =>
        let parts := raw.toString.splitOn "."
        let rec findLocalPath : List String → Option (String × List String)
          | [] | [_] => none
          | rootName :: fieldName :: rest =>
              if locals.any (fun localDecl => localDecl.name == rootName) then
                some (rootName, fieldName :: rest)
              else
                findLocalPath (fieldName :: rest)
        findLocalPath parts
    | _ =>
        let (root, path) ← structProjectionPath? stx
        match stripParens root with
        | `(term| $id:ident) => some (toString id.getId, path)
        | _ => none
  let localDecl ← locals.find? (fun localDecl => localDecl.name == rootName)
  let .externalStaticStruct fieldLocals := localDecl.source | none
  let fieldName ←
    match path with
    | [field] => some field
    | _ => none
  let localName ← fieldLocals.findSome? fun (field, localName) =>
    if field == fieldName then some localName else none
  let fieldTy ←
    match localDecl.ty with
    | .struct _ fields => fields.findSome? fun (field, ty) =>
        if field == fieldName then some ty else none
    | _ => none
  some (localName, fieldTy)

def localMemoryArray?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × ValueType) := do
  let name ←
    match stripParens stx with
    | `(term| $id:ident) => some (toString id.getId)
    | _ => none
  let localDecl ← locals.find? (fun localDecl => localDecl.name == name)
  match localDecl.source, localDecl.ty with
  | .memoryArray, .array elemTy => some (name, elemTy)
  | _, _ => none

def requireSupportedMemoryArrayLocal
    (stx : Term)
    (context : String)
    (locals : Array TypedLocal) : CommandElabM (String × ValueType) := do
  match localMemoryArray? locals stx with
  | some (name, elemTy) => pure (name, elemTy)
  | none => throwErrorAt stx s!"{context} requires a memory-backed Array local"

def localArrayElementStructProjectionResolved?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let (root, path) ← structProjectionPath? stx
  let (paramName, index, elemTy) ← localArrayElementAlias? locals root
  let (fieldTy, wordOffset) ← structFieldHeadOffset? elemTy path
  some (paramName, index, fieldTy, elemTy, wordOffset)

def localArrayElementStructProjection?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← localArrayElementStructProjectionResolved? locals stx
  if isSingleWordStaticValueType fieldTy then
    some resolved
  else
    none

def localArrayElementDynamicMemberProjection?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← localArrayElementStructProjectionResolved? locals stx
  match fieldTy with
  | .array _ | .bytes | .string => some resolved
  | _ => none

def localArrayElementStaticCompositeProjection?
    (locals : Array TypedLocal)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← localArrayElementStructProjectionResolved? locals stx
  if !valueTypeUsesDynamicData fieldTy && !isSingleWordStaticValueType fieldTy then
    some resolved
  else
    none

def abiHeadWordTarget?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Option Term × ValueType) := do
  match stripParens stx with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName ←
        match stripParens name with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      let elemTy ← match param.ty with
        | .array elemTy => some elemTy
        | _ => none
      some (paramName, some index, elemTy)
  | _ => do
      let paramName ←
        match stripParens stx with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      some (paramName, none, param.ty)

def isParamStructNonLeafProjection (params : Array ParamDecl) (stx : Term) : Bool :=
  match paramStructProjectionResolved? params stx with
  | some (_, fieldTy, _) => !isSingleWordStaticValueType fieldTy
  | none => false

def throwStructNonLeafProjectionError (stx : Term) : CommandElabM α :=
  throwErrorAt stx
    "non-leaf struct parameter projection is not supported; project a scalar or static single-word leaf field instead (#1832)"

def renderValueType (ty : ValueType) : String :=
  reprStr ty

def requireTypedInterfaceStaticParams
    (stx : Syntax) (externalName : String) (params : Array ValueType) : CommandElabM Unit := do
  for h : i in [:params.size] do
    let ty := params[i]
    -- #1982 progress: accept static composites (tuples / fixed-arrays of
    -- word-likes) on typed interface params. Only true dynamic shapes are
    -- still rejected here (the lowering helper already has the word-count
    -- path and produces the #1982 error for dynamic cases).
    if staticAbiWordCount? ty |>.isNone then
      throwErrorAt stx
        s!"typed interface call '{externalName}' currently supports only static (single-word or composite) parameters; argument {i + 1} has {renderValueType ty}. Dynamic and composite ABI parameters require ABI-frame typed-interface lowering, which is not implemented yet (#1982)."

/-- Companion of `requireTypedInterfaceStaticParams` for the return-type
    side. Progress on #1982: we now accept static composites (tuples,
    fixed-arrays of word-likes) as typed-interface return shapes.
    True dynamic returns (bytes/string, arrays with dynamic elements) are
    still rejected here with the #1982 error until full ABI-frame
    typed-interface lowering exists. -/
def requireTypedInterfaceStaticReturns
    (stx : Syntax) (externalName : String) (returnTys : Array ValueType) : CommandElabM Unit := do
  for h : i in [:returnTys.size] do
    let ty := returnTys[i]
    if staticAbiWordCount? ty |>.isNone then
      throwErrorAt stx
        s!"typed interface call '{externalName}' currently supports only static (single-word or composite) returns; return {i + 1} has {renderValueType ty}. Dynamic and composite ABI returns require ABI-frame typed-interface lowering, which is not implemented yet (#1982)."

/-- verity#1849, G3: allow `Array <wordLike>` and `bytes` / `string` as
    external-call / event / custom-error argument types when the argument
    is a direct param reference. The lowering still happens through
    `Expr.param`, which becomes `YulExpr.ident name`; for `Array <T>` /
    `bytes` / `string` direct-param leaves the resulting Yul ident is
    really the `{name}_data_offset` / `{name}_length` pair that the
    dynamic-data param loader already binds, so callers can forward
    pre-decoded dynamic-data leaves directly. The CompilationModel's
    `Expr.externalCall` Yul-call lowering accepts this shape verbatim
    (one Yul arg per `Expr` arg) — the actual ABI encoding for downstream
    Solidity targets is handled by the ECM / `Stmt.externalCallBind`
    family, not by `Expr.externalCall`. -/
def isWordOrDirectArrayType (ty : ValueType) : Bool :=
  match ty with
  | .array elemTy => isSingleWordStaticValueType elemTy
  | .bytes | .string => true
  | _ => isWordLikeValueType ty

def requireWordOrDirectArrayType (stx : Syntax) (context : String) (ty : ValueType) : CommandElabM Unit := do
  unless isWordOrDirectArrayType ty do
    throwErrorAt stx
      s!"{context} requires a word-like value or a direct `Array <wordLike>`/`bytes`/`string` parameter reference, got {renderValueType ty}"

def requireWordLikeType (stx : Syntax) (context : String) (ty : ValueType) : CommandElabM Unit := do
  unless isWordLikeValueType ty do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {renderValueType ty}"

def requireBoolType (stx : Syntax) (context : String) (ty : ValueType) : CommandElabM Unit := do
  unless ty == .bool do
    throwErrorAt stx s!"{context} requires Bool, got {renderValueType ty}"

def requireSupportedReturnArrayType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  match ty with
  | .array elemTy =>
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt stx
          s!"{context} currently supports only arrays with single-word static elements on the compilation-model path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx s!"{context} requires an Array value, got {renderValueType ty}"

def requireSupportedArrayElementSourceType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM ValueType := do
  match ty with
  | .array elemTy =>
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt stx
          s!"{context} currently supports only arrays with single-word static elements on the compilation-model path, got {renderValueType ty}"
      pure elemTy
  | _ =>
      throwErrorAt stx s!"{context} requires an Array parameter, got {renderValueType ty}"

def requireSupportedArrayElementTupleSourceType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM ValueType := do
  match ty with
  | .array elemTy@(.tuple _) =>
      match staticAbiWordCount? elemTy, abiLocalHeadWordCount? elemTy with
      | some _, _ => pure elemTy
      | none, some _ => pure elemTy
      | none, none =>
          throwErrorAt stx
            s!"{context} currently supports only arrays with ABI-decodable tuple elements, got {renderValueType ty}"
  | .array elemTy =>
      match staticAbiWordCount? elemTy with
      | some _ => pure elemTy
      | none =>
          throwErrorAt stx
            s!"{context} currently supports only arrays with static ABI-word elements on the tuple arrayElement path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx s!"{context} requires an Array parameter, got {renderValueType ty}"

def directParamNameWithType?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      let name := toString id.getId
      params.findSome? fun p =>
        if p.name == name then
          some (name, p.ty)
        else
          none
  | _ => none

def requireDirectParamRef
    (stx : Term)
    (context : String)
    (params : Array ParamDecl) : CommandElabM ValueType := do
  match directParamNameWithType? params stx with
  | some (_, paramTy) => pure paramTy
  | none =>
      throwErrorAt stx
        s!"{context} currently requires a direct parameter reference on the compilation-model path"

def requireSupportedReturnBytesType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  unless ty == .bytes || ty == .string do
    throwErrorAt stx
      s!"{context} requires a Bytes or String parameter on the compilation-model path, got {renderValueType ty}"

def requireSupportedReturnStorageWordsType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  match ty with
  | .array elemTy =>
      if isSingleWordStaticValueType elemTy then
        pure ()
      else
        throwErrorAt stx
          s!"{context} requires an array with single-word static elements on the compilation-model path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx
        s!"{context} requires an Array parameter on the compilation-model path, got {renderValueType ty}"

def requireEqComparableTypes (stx : Syntax) (lhsTy rhsTy : ValueType) : CommandElabM Unit := do
  let bothWordLike := isWordLikeValueType lhsTy && isWordLikeValueType rhsTy
  let bothBool := lhsTy == .bool && rhsTy == .bool
  let bothDynamicBytes := (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes)
  unless bothWordLike || bothBool || bothDynamicBytes do
    throwErrorAt stx
      s!"equality is currently supported only for Bool, matching bytes/string params, and word-like values (Uint256, Int256, Uint8, Address, Bytes32); got {renderValueType lhsTy} and {renderValueType rhsTy}"

def directDynamicComparableParamName?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      let name := toString id.getId
      params.findSome? fun p =>
        if p.name == name && (p.ty == .string || p.ty == .bytes) then
          some (name, p.ty)
        else
          none
  | _ => none

def dynamicEqParamNames
    (stx : Syntax)
    (params : Array ParamDecl)
    (lhs rhs : Term)
    (lhsTy rhsTy : ValueType) : CommandElabM (String × String) := do
  match directDynamicComparableParamName? params lhs, directDynamicComparableParamName? params rhs with
  | some (lhsName, lhsParamTy), some (rhsName, rhsParamTy) =>
      if lhsParamTy == lhsTy && rhsParamTy == rhsTy && lhsTy == rhsTy then
        pure (lhsName, rhsName)
      else
        throwErrorAt stx
          s!"bytes/string equality requires matching direct parameter references, got {renderValueType lhsTy} and {renderValueType rhsTy}"
  | _, _ =>
      throwErrorAt stx
        "bytes/string equality currently requires direct parameter references on the compilation-model path"

def requireSameOrWordLikeTypes (stx : Syntax) (context : String) (lhsTy rhsTy : ValueType) : CommandElabM Unit := do
  unless lhsTy == rhsTy || (isWordLikeValueType lhsTy && isWordLikeValueType rhsTy) do
    throwErrorAt stx
      s!"{context} requires matching branch types, got {renderValueType lhsTy} and {renderValueType rhsTy}"

def requireDeclaredValueType
    (stx : Syntax)
    (context : String)
    (expectedTy actualTy : ValueType) : CommandElabM Unit := do
  unless actualTy == expectedTy || (isWordLikeValueType actualTy && isWordLikeValueType expectedTy) do
    throwErrorAt stx
      s!"{context} expects {renderValueType expectedTy}, got {renderValueType actualTy}"

def localBindingUsesDynamicData : ValueType → Bool :=
  valueTypeUsesDynamicData

def requireSupportedLocalBindingType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  if localBindingUsesDynamicData ty then
    throwErrorAt stx
      s!"{context} currently cannot bind dynamic values ({renderValueType ty}) to local variables on the compilation-model path; use the parameter directly"

unsafe def qualifiedTupleBindTypedLocals
    (stx : Syntax)
    (fnName : Name)
    (names : Array (Option String)) : CommandElabM (Array TypedLocal) := do
  let valueTys ← unsafe qualifiedFunctionReturnTypes stx fnName
  if names.size != valueTys.size then
    throwErrorAt stx
      s!"tuple destructuring binds {names.size} names, but qualified helper '{qualifiedFunctionDisplayName fnName}' returns {valueTys.size} values"
  for (name?, ty) in names.zip valueTys do
    if let some name := name? then
      requireSupportedLocalBindingType stx s!"local binding '{name}'" ty
  pure <| (names.zip valueTys).filterMap fun (name?, ty) =>
    name?.map (fun name => mkTypedLocal name ty)

unsafe def qualifiedSingleBindType
    (stx : Syntax)
    (fnName : Name) : CommandElabM ValueType := do
  let valueTys ← unsafe qualifiedFunctionReturnTypes stx fnName
  match valueTys.toList with
  | [] =>
      throwErrorAt stx
        s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns Unit and cannot be bound"
  | [retTy] =>
      pure retTy
  | _ =>
      throwErrorAt stx
        s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns multiple values; use tuple destructuring"

def customErrorRequiresDirectParamRef : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => false
  | .newtype _ baseType => customErrorRequiresDirectParamRef baseType
  | _ => true

def directParamRefName? (stx : Term) : Option String :=
  match stripParens stx with
  | `(term| $id:ident) => some (toString id.getId)
  | _ => none

def validateDirectParamCustomErrorArg
    (arg : Term)
    (fnName errorName : String)
    (params : Array ParamDecl)
    (expectedTy : ValueType)
    (argIdx : Nat) : CommandElabM Unit := do
  match directParamRefName? arg with
  | some name =>
      match params.find? (·.name == name) with
      | some param =>
          unless param.ty == expectedTy do
            throwErrorAt arg
              s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' expects direct parameter reference of type {renderValueType expectedTy}, got parameter '{name}' of type {renderValueType param.ty}"
      | none =>
          throwErrorAt arg
            s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' references unknown parameter '{name}' on the compilation-model path"
  | none =>
      throwErrorAt arg
        s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' currently requires direct parameter reference of type {renderValueType expectedTy} on the compilation-model path"

def validateCustomErrorArg
    (arg : Term)
    (actualTy : ValueType)
    (fnName errorName : String)
    (params : Array ParamDecl)
    (expectedTy : ValueType)
    (argIdx : Nat) : CommandElabM Unit := do
  requireDeclaredValueType arg
    s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}'"
    expectedTy actualTy
  if customErrorRequiresDirectParamRef expectedTy then
    validateDirectParamCustomErrorArg arg fnName errorName params expectedTy argIdx

def validateCustomErrorCall
    (fnName errorName : String)
    (params : Array ParamDecl)
    (errorDecls : Array ErrorDecl)
    (args : Array Term)
    (argTypes : Array ValueType) : CommandElabM Unit := do
  let errorDecl ←
    match errorDecls.find? (·.name == errorName) with
    | some decl => pure decl
    | none => throwError s!"unknown custom error '{errorName}'"
  unless errorDecl.params.size == args.size && args.size == argTypes.size do
    throwError s!"custom error '{errorName}' expects {errorDecl.params.size} args, got {args.size}"
  for (((expectedTy, arg), actualTy), argIdx) in errorDecl.params.zip args |>.zip argTypes |>.zipIdx do
    validateCustomErrorArg arg actualTy fnName errorName params expectedTy argIdx

def throwPureContextAccessorError (stx : Syntax) (name : String) : CommandElabM α :=
  throwErrorAt stx
    s!"context accessor '{name}' is monadic; use `let x ← {name}` before using it in a pure expression"

mutual
partial def leanExprAppFnArgs (expr : Expr) : Expr × Array Expr :=
  let rec go (fn : Expr) (argsRev : Array Expr) : Expr × Array Expr :=
    match fn.consumeMData with
    | .app f arg => go f (argsRev.push arg)
    | other => (other, argsRev.reverse)
  go expr #[]

partial def leanConstName? (expr : Expr) : Option Name :=
  match expr.consumeMData with
  | .const name _ => some name
  | _ => none

partial def leanConstNameMatches (expr : Expr) (names : List Name) : Bool :=
  match leanConstName? expr with
  | some name => names.contains name
  | none => false

partial def leanConstNameMatchesStringOrSuffix
    (expr : Expr)
    (names : List String)
    (suffixes : List String) : Bool :=
  match leanConstName? expr with
  | some name =>
      let nameString := name.toString
      names.contains nameString || suffixes.any (fun suffix => nameString.endsWith s!".{suffix}")
  | none => false

partial def valueTypeFromLeanTypeExpr? (expr : Expr) : Option ValueType :=
  match expr.consumeMData with
  | .const name _ =>
      let nameString := name.toString
      if nameString == "Verity.Uint256" || nameString == "Verity.Core.Uint256" ||
          nameString.endsWith ".Uint256" then
        some .uint256
      else if nameString == "Verity.Int256" || nameString == "Verity.Core.Int256" ||
          nameString.endsWith ".Int256" then
        some .int256
      else if nameString == "Verity.Address" || nameString == "Verity.Core.Address" ||
          nameString.endsWith ".Address" then
        some .address
      else if nameString == "Bool" then
        some .bool
      else if nameString == "String" then
        some .string
      else if nameString == "ByteArray" then
        some .bytes
      else
        none
  | _ => none

partial def peelForallTypes (type : Expr) : List Expr × Expr :=
  let rec go (remaining : Expr) (acc : List Expr) : List Expr × Expr :=
    match remaining.consumeMData with
    | .forallE _ domain body _ => go body (domain :: acc)
    | other => (acc.reverse, other)
  go type []

partial def peelLambdaBody (value : Expr) (arity : Nat) : Option Expr :=
  match arity with
  | 0 => some value
  | n + 1 =>
      match value.consumeMData with
      | .lam _ _ body _ => peelLambdaBody body n
      | _ => none

partial def leanDefAppSyntax? (stx : Term) : Option (Syntax × String × Array Term) :=
  let stx := stripParens stx
  match stx.raw with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | head@(.ident _ _ raw _) =>
          if isQualifiedFunctionName raw then
            none
          else
            let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
            some (head, raw.toString, argTerms)
      | _ => none
  | _ => none

partial def resolveLeanDefName? (head : Syntax) : CommandElabM (Option Name) := do
  try
    pure (some (← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo head none))
  catch _ =>
    pure none

partial def leanDefInfo? (name : Name) : CommandElabM (Option DefinitionVal) := do
  match (← getEnv).find? name with
  | some (.defnInfo info) => pure (some info)
  | _ => pure none

partial def checkLeanDefCallArgs
    (stx : Syntax)
    (fnDisplay : String)
    (argTerms : Array Term)
    (paramTypeExprs : List Expr)
    (argTypes : Array ValueType) : CommandElabM Unit := do
  unless argTerms.size == paramTypeExprs.length do
    throwErrorAt stx
      s!"Lean helper '{fnDisplay}' expects {paramTypeExprs.length} argument(s), got {argTerms.size}"
  for ((argTerm, argTy), expectedExpr) in argTerms.zip argTypes |>.zip paramTypeExprs.toArray do
    let expectedTy ←
      match valueTypeFromLeanTypeExpr? expectedExpr with
      | some ty => pure ty
      | none =>
          throwErrorAt stx
            s!"Lean helper '{fnDisplay}' uses an unsupported parameter type; supported pure helper parameters are Uint256, Int256, Address, Bytes32/Uint256, Bool, String, and Bytes"
    unless argTy == expectedTy || (isNatLiteralTerm argTerm && numericLiteralCompatibleValueType expectedTy) do
      throwErrorAt argTerm
        s!"Lean helper '{fnDisplay}' argument expects {renderValueType expectedTy}, got {renderValueType argTy}"

partial def inferLeanDefCallType?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String) : CommandElabM (Option ValueType) := do
  let some (head, fnDisplay, argTerms) := leanDefAppSyntax? stx
    | pure none
  let some fnName ← resolveLeanDefName? head
    | pure none
  let some info ← leanDefInfo? fnName
    | pure none
  let (paramTypeExprs, resultTypeExpr) := peelForallTypes info.type
  let argTypes ← argTerms.mapM
    (inferPureExprType fields constDecls immutableDecls externalDecls params locals · visitingConstants)
  checkLeanDefCallArgs stx.raw fnDisplay argTerms paramTypeExprs argTypes
  match valueTypeFromLeanTypeExpr? resultTypeExpr with
  | some ty =>
      requireSupportedLocalBindingType stx.raw s!"Lean helper '{fnDisplay}' return" ty
      pure (some ty)
  | none =>
      throwErrorAt stx
        s!"Lean helper '{fnDisplay}' uses an unsupported return type; supported pure helper returns are Uint256, Int256, Address, Bytes32/Uint256, and Bool"

partial def inferPureExprType
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM ValueType := do
  let stx := stripParens stx
  let inferContextAccessorOrLocal (name : String) : CommandElabM ValueType := do
    match locals.findSome? (fun localDecl =>
        if matchesBareName localDecl.name name then some localDecl.ty else none)
        <|> params.findSome? (fun p =>
          if matchesBareName p.name name then some p.ty else none) with
    | some ty => pure ty
    | none => throwPureContextAccessorError stx name
  if let some (_, index, fieldTy, _, _) := arrayElementStructProjection? params stx then
    requireWordLikeType index "arrayElement index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if let some (_, index, fieldTy, _, _) := localArrayElementStructProjection? locals stx then
    requireWordLikeType index "arrayElement alias index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if let some (_, index, fieldTy, _, _) := arrayElementDynamicMemberProjection? params stx then
    requireWordLikeType index "arrayElement index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if let some (_, index, fieldTy, _, _) := localArrayElementDynamicMemberProjection? locals stx then
    requireWordLikeType index "arrayElement alias index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if let some (_, index, fieldTy, _, _) := localArrayElementStaticCompositeProjection? locals stx then
    requireWordLikeType index "arrayElement alias index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if let some (_, fieldTy, _) := paramDynamicHeadProjection? params stx then
    pure fieldTy
  else
  if let some (_, fieldTy, _) := paramDynamicStaticCompositeProjection? params stx then
    pure fieldTy
  else
  if let some (_, fieldTy, _) := paramDynamicMemberProjection? params stx then
    pure fieldTy
  else
  if isParamStructNonLeafProjection params stx then
    throwStructNonLeafProjectionError stx
  else
  if let some (_, ty) := paramStructProjection? params stx then
    pure ty
  else
  if let some (_, ty) := localExternalStaticStructProjection? locals stx then
    pure ty
  else
  match stx with
  | `(term| true) | `(term| false) => pure .bool
  | `(term| constructorArg $idx:num) =>
      match params[(← natFromSyntax idx)]? with
      | some param => pure param.ty
      | none => throwErrorAt stx s!"constructorArg index {idx.raw.reprint.getD ""} is out of bounds"
  | `(term| abiHeadWord $target:term $wordOffset:num) => do
      let offset ← natFromSyntax wordOffset
      let (index?, ty) ←
        match abiHeadWordTarget? params target with
        | some (_, index?, ty) => pure (index?, ty)
        | none =>
            match localArrayElementAlias? locals target with
            | some (_, index, ty) => pure (some index, ty)
            | none => throwErrorAt target "abiHeadWord requires a direct parameter, dynamic local alias, or `arrayElement <param> <index>` target"
      if let some index := index? then
        requireWordLikeType index "arrayElement index"
          (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
      let headWords? :=
        if valueTypeUsesDynamicData ty then
          abiLocalHeadWordCount? ty
        else
          staticAbiWordCount? ty
      match headWords? with
      | some headWords =>
          unless offset < headWords do
            throwErrorAt stx s!"abiHeadWord offset {offset} is out of bounds for target with {headWords} ABI head word(s)"
      | none =>
          throwErrorAt target s!"abiHeadWord target type has no ABI head-word layout: {renderValueType ty}"
      pure .uint256
  | `(term| abiEncode $target:term) => do
      let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals target visitingConstants
      match staticAbiWordCount? ty with
      | some _ => pure .uint256
      | none => throwErrorAt target s!"abiEncode requires a static ABI value, got {renderValueType ty}"
  | `(term| Verity.msgSender) =>
      throwPureContextAccessorError stx "msgSender"
  | `(term| Verity.msgValue) =>
      throwPureContextAccessorError stx "msgValue"
  | `(term| Verity.selfBalance) =>
      throwPureContextAccessorError stx "selfBalance"
  | `(term| Verity.blockTimestamp) =>
      throwPureContextAccessorError stx "blockTimestamp"
  | `(term| Verity.blockNumber) =>
      throwPureContextAccessorError stx "blockNumber"
  | `(term| Verity.blobbasefee) =>
      throwPureContextAccessorError stx "blobbasefee"
  | `(term| Verity.chainid) =>
      throwPureContextAccessorError stx "chainid"
  | `(term| Verity.contractAddress) =>
      throwPureContextAccessorError stx "contractAddress"
  | `(term| Verity.txOrigin) =>
      throwPureContextAccessorError stx "txOrigin"
  | `(term| $id:ident) =>
      let name := toString id.getId
      match params.findSome? (fun p => if p.name == name then some p.ty else none)
          <|> tupleParamElemType? params name
          <|> lookupTypedLocalType? locals name
          <|> immutableDecls.findSome? (fun imm =>
                if declaredNameMatches name imm.name then some imm.ty else none)
          <|> constDecls.findSome? (fun constant =>
                if declaredNameMatches name constant.name then some constant.ty else none) with
      | some ty => pure ty
      | none =>
          if matchesBareName name "calldatasize" || matchesBareName name "returndataSize" then
            pure .uint256
          else if matchesBareName name "zeroAddress" then
            pure .address
          else
            match contextAccessorBareName? name with
            | some accessor => inferContextAccessorOrLocal accessor
            | none => throwErrorAt stx s!"unknown variable '{name}'"
  | `(term| calldatasize) | `(term| returndataSize) =>
      pure .uint256
  | `(term| zeroAddress) =>
      match lookupTypedLocalType? locals "zeroAddress" <|> params.findSome? (fun p =>
        if p.name == "zeroAddress" then some p.ty else none) with
      | some ty => pure ty
      | none => pure .address
  | `(term| isZeroAddress $a:term) =>
      requireWordLikeType a "isZeroAddress" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .bool
  | `(term| wordToAddress $a:term) =>
      requireWordLikeType a "wordToAddress" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .address
  | `(term| addressToWord $a:term) =>
      let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      unless ty == .address do
        throwErrorAt a s!"addressToWord requires Address, got {renderValueType ty}"
      pure .uint256
  | `(term| toInt256 $a:term) => do
      requireWordLikeType a "toInt256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .int256
  | `(term| toUint256 $a:term) => do
      requireWordLikeType a "toUint256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| narrowUInt $bits:num $a:term) => do
      let width ← natFromSyntax bits
      requireWordLikeType a "narrowUInt" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure (.uintN width)
  | `(term| narrowInt $bits:num $a:term) => do
      let width ← natFromSyntax bits
      requireWordLikeType a "narrowInt" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure (.intN width)
  | `(term| narrowBytes $bytes:num $a:term) => do
      let width ← natFromSyntax bytes
      requireWordLikeType a "narrowBytes" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure (.bytesN width)
  | `(term| boolToWord $a:term) =>
      requireBoolType a "boolToWord" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| $n:num) =>
      pure .uint256
  | `(term| add $a $b) | `(term| $a + $b)
    | `(term| sub $a $b) | `(term| $a - $b)
    | `(term| mul $a $b) | `(term| $a * $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      classifyWordArithmeticResultType stx "word arithmetic" lhsTy rhsTy
  | `(term| bitAnd $a $b)
    | `(term| bitOr $a $b) | `(term| bitXor $a $b) | `(term| and $a $b)
    | `(term| or $a $b) | `(term| xor $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "bitwise word arithmetic" lhsTy rhsTy
  | `(term| pow $a $b) | `(term| $a ^ $b)
  | `(term| min $a $b) | `(term| max $a $b) | `(term| wMulDown $a $b) | `(term| wDivUp $a $b)
  | `(term| ceilDiv $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "unsigned word arithmetic" lhsTy rhsTy
  | `(term| div $a $b) | `(term| $a / $b) | `(term| mod $a $b) | `(term| $a % $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      classifyWordArithmeticResultType stx "division/modulo" lhsTy rhsTy
  | `(term| sdiv $a $b) | `(term| smod $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "signed builtin arithmetic" lhsTy rhsTy
  | `(term| bitNot $a) | `(term| not $a) => do
      let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      requireWordLikeType a "bitwise not" ty
      pure .uint256
  | `(term| shl $shift $value) | `(term| shr $shift $value) | `(term| sar $shift $value)
    | `(term| signextend $shift $value) => do
      requireWordLikeType shift "shift" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals shift visitingConstants)
      let valueTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value visitingConstants
      requireWordLikeType value "shift" valueTy
      pure .uint256
  | `(term| byte $index $value) => do
      requireWordLikeType index "byte index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
      let valueTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value visitingConstants
      requireWordLikeType value "byte value" valueTy
      pure .uint256
  | `(term| slt $a $b) | `(term| sgt $a $b) => do
      requireWordLikeType a "signed ordering comparison" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireWordLikeType b "signed ordering comparison" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .bool
  | `(term| $a == $b) | `(term| $a != $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      requireEqComparableTypes stx lhsTy rhsTy
      pure .bool
  | `(term| $a >= $b) | `(term| $a > $b) | `(term| $a < $b) | `(term| $a <= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      discard <| classifyWordArithmeticResultType stx "ordering comparison" lhsTy rhsTy
      pure .bool
  | `(term| $a && $b) | `(term| $a || $b) => do
      requireBoolType a "logical operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireBoolType b "logical operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .bool
  | `(term| logicalAnd $a $b) | `(term| logicalOr $a $b) => do
      requireWordLikeType a "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireWordLikeType b "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .uint256
  | `(term| logicalNot $a) => do
      requireWordLikeType a "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| ! $a) => do
      requireBoolType a "logical not" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .bool
  | `(term| mload $offset) | `(term| tload $offset) | `(term| calldataload $offset)
    | `(term| extcodesize $offset) => do
      requireWordLikeType offset "word offset expression" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset visitingConstants)
      pure .uint256
  | `(term| keccak256 $offset $size) => do
      requireWordLikeType offset "keccak256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset visitingConstants)
      requireWordLikeType size "keccak256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals size visitingConstants)
      pure .uint256
  -- Compile-time Keccak-256 of a string literal (#1973). The hash is
  -- computed during contract translation, so the result is unconditionally
  -- a `uint256` regardless of the literal content.
  | `(term| keccakString $_s:str) => pure .uint256
  | `(term| call $gas $target $value $inOffset $inSize $outOffset $outSize) => do
      for arg in [gas, target, value, inOffset, inSize, outOffset, outSize] do
        requireWordLikeType arg "low-level call" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| staticcall $gas $target $inOffset $inSize $outOffset $outSize)
    | `(term| delegatecall $gas $target $inOffset $inSize $outOffset $outSize) => do
      for arg in [gas, target, inOffset, inSize, outOffset, outSize] do
        requireWordLikeType arg "low-level call" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| arrayLength $name:term) =>
      -- verity#1849, G1: accept `arrayLength (arrayElement <param> <i>).<dynField>`
      -- projections where `dynField` is a dynamic member of the struct-array
      -- element type. Lowers through `Expr.arrayElementDynamicMemberLength`.
      if let some _ := arrayElementDynamicMemberProjection? params name then
        pure .uint256
      else if let some _ := localArrayElementDynamicMemberProjection? locals name then
        pure .uint256
      else if let some _ := localMemoryArray? locals name then
        pure .uint256
      else if let some _ := paramDynamicMemberProjection? params name then
        pure .uint256
      else
        match lookupNamedValueType? constDecls immutableDecls params locals (← expectStringOrIdent name) with
        | some (.array _) => pure .uint256
        | some ty => throwErrorAt name s!"arrayLength expects an Array value, got {renderValueType ty}"
        | none => throwErrorAt name "unknown array value"
  | `(term| arrayElement $name:term $index:term) => do
      requireWordLikeType index "arrayElement index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
      -- verity#1849, G2: accept `arrayElement (arrayElement <param> <i>).<dynField> <k>`
      -- when `<dynField>` is `Array <wordLike>`. Returns the word-like element type.
      if let some (_, _, fieldTy, _, _) := arrayElementDynamicMemberProjection? params name then
        match fieldTy with
        | .array elemTy =>
            if isSingleWordStaticValueType elemTy then
              pure elemTy
            else
              throwErrorAt name s!"arrayElement on a dynamic member of a struct-array element currently supports only Array<wordLike> members, got Array {renderValueType elemTy}"
        | _ =>
            throwErrorAt name s!"arrayElement on a struct-array element projection requires an Array-typed dynamic member, got {renderValueType fieldTy}"
      else if let some (_, _, fieldTy, _, _) := localArrayElementDynamicMemberProjection? locals name then
        match fieldTy with
        | .array elemTy =>
            if isSingleWordStaticValueType elemTy then
              pure elemTy
            else
              throwErrorAt name s!"arrayElement on a dynamic member of an aliased struct-array element currently supports only Array<wordLike> members, got Array {renderValueType elemTy}"
        | _ =>
            throwErrorAt name s!"arrayElement on an aliased struct-array element projection requires an Array-typed dynamic member, got {renderValueType fieldTy}"
      else if let some (_, fieldTy, _) := paramDynamicMemberProjection? params name then
        match fieldTy with
        | .array elemTy =>
            if isSingleWordStaticValueType elemTy then
              pure elemTy
            else
              throwErrorAt name s!"arrayElement on a dynamic member of a struct parameter currently supports only Array<wordLike> members, got Array {renderValueType elemTy}"
        | _ =>
            throwErrorAt name s!"arrayElement on a struct parameter projection requires an Array-typed dynamic member, got {renderValueType fieldTy}"
      else if let some (_, elemTy) := localMemoryArray? locals name then
        if isSingleWordStaticValueType elemTy then
          pure elemTy
        else
          throwErrorAt name s!"arrayElement on a memory array local currently supports only Array<wordLike> values, got Array {renderValueType elemTy}"
      else
        let sourceTy ← requireDirectParamRef name "arrayElement" params
        match sourceTy with
        | .array elemTy =>
            match elemTy with
            | .struct _ _ | .tuple _ =>
              if valueTypeUsesDynamicData elemTy then
                pure elemTy
              else
                requireSupportedArrayElementSourceType name "arrayElement" sourceTy
            | _ =>
              requireSupportedArrayElementSourceType name "arrayElement" sourceTy
        | _ =>
            requireSupportedArrayElementSourceType name "arrayElement" sourceTy
  | `(term| mulDivDown $a $b $c) | `(term| mulDivUp $a $b $c) => do
      for arg in [a, b, c] do
        requireWordLikeType arg "mulDiv" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| mulDiv512Down $a $b $c) | `(term| mulDiv512Up $a $b $c) => do
      for arg in [a, b, c] do
        requireWordLikeType arg "mulDiv512" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| ite $cond $thenVal $elseVal) => do
      requireBoolType cond "ite condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond visitingConstants)
      let thenTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals thenVal visitingConstants
      let elseTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals elseVal visitingConstants
      requireSameOrWordLikeTypes stx "ite" thenTy elseTy
      pure thenTy
  | `(term| externalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            -- verity#1849, G3: accept `Array <wordLike>` / `bytes` / `string`
            -- direct param refs alongside word-like args.
            if let some (_, _, fieldTy, _elemTy, _) := arrayElementDynamicMemberProjection? params x then
              unless externalCallDynamicArgSupported fieldTy do
                throwErrorAt x s!"externalCall '{extName}' dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else if let some (_, _, fieldTy, _elemTy, _) := localArrayElementDynamicMemberProjection? locals x then
              unless externalCallDynamicArgSupported fieldTy do
                throwErrorAt x s!"externalCall '{extName}' dynamic-member alias argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else if let some (_, fieldTy, _) := paramDynamicMemberProjection? params x then
              unless externalCallDynamicArgSupported fieldTy do
                throwErrorAt x s!"externalCall '{extName}' dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else
              requireWordOrDirectArrayType x s!"externalCall '{extName}' argument" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x visitingConstants)
      | _ => throwErrorAt args "expected list literal [..]"
      match externalDecls.find? (fun ext => ext.name == extName) with
      | some ext =>
          match ext.returnTys.toList with
          | [retTy] => pure retTy
          | [] => throwErrorAt name s!"externalCall '{extName}' returns no values; use `let success ← tryExternalCall \"{extName}\" [...]` instead"
          | _ => throwErrorAt name s!"externalCall '{extName}' returns {ext.returnTys.size} values; use `let (success, ...) ← tryExternalCall \"{extName}\" [...]` for multi-return"
      | none => pure .uint256
  | `(term| intrinsic_cancun $name:term $_lowering:term $args:term)
  | `(term| intrinsic_prague $name:term $_lowering:term $args:term)
  | `(term| intrinsic_fusaka $name:term $_lowering:term $args:term)
  | `(term| intrinsic_osaka $name:term $_lowering:term $args:term)
  | `(term| intrinsic $name:term $_lowering:term $args:term) =>
      let _ := ← expectStringOrIdent name
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            requireWordLikeType x "intrinsic argument"
              (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x visitingConstants)
          pure .uint256
      | _ => throwErrorAt args "expected list literal [..]"
  | `(term| clz $x:term) | `(term| msb $x:term) =>
      requireWordLikeType x "bitmap primitive argument"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x visitingConstants)
      pure .uint256
  | `(term| fork_if_at_least $fork:ident then $thenExpr:term else $elseExpr:term) =>
      let thenTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals thenExpr visitingConstants
      let elseTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals elseExpr visitingConstants
      unless thenTy == elseTy do
        throwErrorAt elseExpr
          s!"fork_if_at_least branches must have the same type, got {renderValueType thenTy} and {renderValueType elseTy}"
      let _ ← hardForkTermFromIdent fork
      pure thenTy
  | `(term| structMember $field:term $key:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let memberDecl ← lookupStructMemberDecl fields fieldName memberName false
      requireWordLikeType key "structMember key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key visitingConstants)
      pure memberDecl.ty
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let memberDecl ← lookupStructMemberDecl fields fieldName memberName true
      requireWordLikeType key1 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1 visitingConstants)
      requireWordLikeType key2 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2 visitingConstants)
      pure memberDecl.ty
  -- `Verity.keccak256_lit "literal"` / `keccak256_lit "literal"` —
  -- compile-time Keccak-256 of a UTF-8 string literal.  Always
  -- `.uint256` (the hash is 256 bits, fits exactly).  Validated +
  -- lowered to `Expr.literal n` later in the same file.
  | `(term| Verity.keccak256_lit $_:str) | `(term| keccak256_lit $_:str) =>
      pure .uint256
  | _ =>
      match qualifiedFunctionAppSyntax? stx with
      | some (fnName, _) =>
          if (nameComponents fnName).head? == some "Verity" then
            throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"
          else
            throwErrorAt stx
              s!"qualified library helper call '{qualifiedFunctionDisplayName fnName}' is only supported as a monadic bind source; use `let x ← {qualifiedFunctionDisplayName fnName} ...` or tuple destructuring bind syntax"
      | none =>
          match ← inferLeanDefCallType? fields constDecls immutableDecls externalDecls params locals stx visitingConstants with
          | some ty => pure ty
          | none => throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"

partial def lookupNamedValueType?
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (name : String) : Option ValueType :=
  params.findSome? (fun p => if p.name == name then some p.ty else none)
    <|> lookupTypedLocalType? locals name
    <|> immutableDecls.findSome? (fun imm => if imm.name == name then some imm.ty else none)
    <|> constDecls.findSome? (fun constant => if constant.name == name then some constant.ty else none)

partial def inferBindSourceType
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM ValueType := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| callResult $name:term $_args:term) =>
      let extName := ← expectStringOrIdent name
      let ext ←
        match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext => pure ext
        | none => throwErrorAt rhs s!"unknown external function '{extName}'"
      let fields :=
        match ext.returnTys.toList with
        | [] => [("success", .bool)]
        | [retTy] => [("success", .bool), ("returndata", retTy)]
        | retTys =>
            ("success", .bool) ::
              retTys.zipIdx.map (fun (retTy, idx) => (s!"returndata{idx}", retTy))
      pure (.struct "Call.Result" fields)
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 => pure .uint256
      | .scalar .int256 => pure .int256
      | .scalar (.newtype ntName (.uint256)) => pure (.newtype ntName .uint256)
      | .scalar (.adt name maxFields) => pure (.adt name maxFields)
      | .scalar (.newtype _ (.address)) => throwErrorAt rhs s!"field '{f.name}' is Address-based newtype; use getStorageAddr"
      | .scalar .address => throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; encode as Uint256 and use getStorage"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address => pure .address
      | .scalar (.newtype ntName (.address)) => pure (.newtype ntName .address)
      | .scalar (.newtype _ (.uint256)) => throwErrorAt rhs s!"field '{f.name}' is Uint256-based newtype; use getStorage"
      | .scalar .uint256 => throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; use getStorage"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageArrayLength $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ => pure .uint256
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getStorageArrayElement $field:ident $index:term) => do
      requireWordLikeType index "storage array index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray .uint256 => pure .uint256
      | .dynamicArray .address => pure .address
      | .dynamicArray .bool => pure .bool
      | .dynamicArray .uint8 => pure .uint8
      | .dynamicArray .bytes32 => pure .bytes32
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getMapping $field:ident $key:term) | `(term| getMappingUint $field:ident $key:term)
    | `(term| getMappingWord $field:ident $key:term $_wordOffset:num) => do
      requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 => pure .uint256
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingAddr $field:ident $key:term) | `(term| getMappingUintAddr $field:ident $key:term) => do
      requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 => pure .address
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) => do
      requireWordLikeType key1 "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
      requireWordLikeType key2 "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 => pure .uint256
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| getMappingN $field:ident $keys:term) => do
      let keyTerms ← expectMappingKeyTerms keys
      for key in keyTerms do
        requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size == keyTypes.length then
            pure .uint256
          else
            throwErrorAt rhs s!"field '{f.name}' expects {keyTypes.length} mapping keys, but getMappingN received {keyTerms.size}"
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
          | _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| structMember $field:term $key:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let memberDecl ← lookupStructMemberDecl fields fieldName memberName false
      requireWordLikeType key "structMember key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      pure memberDecl.ty
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let memberDecl ← lookupStructMemberDecl fields fieldName memberName true
      requireWordLikeType key1 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
      requireWordLikeType key2 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
      pure memberDecl.ty
  | `(term| msgSender) | `(term| Verity.msgSender) =>
      pure .address
  | `(term| msgValue) | `(term| Verity.msgValue) | `(term| selfBalance)
    | `(term| Verity.selfBalance) | `(term| blockTimestamp)
    | `(term| Verity.blockTimestamp) | `(term| blockNumber) | `(term| Verity.blockNumber)
    | `(term| blobbasefee) | `(term| Verity.blobbasefee) | `(term| chainid)
    | `(term| Verity.chainid) =>
      pure .uint256
  | `(term| contractAddress) | `(term| Verity.contractAddress) =>
      pure .address
  | `(term| txOrigin) | `(term| Verity.txOrigin) =>
      pure .address
  | `(term| tload $offset:term) => do
      requireWordLikeType offset "tload offset" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset)
      pure .uint256
  | `(term| ecrecover $hash:term $v:term $r:term $s:term) => do
      for arg in [hash, v, r, s] do
        requireWordLikeType arg "ecrecover" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .address
  | `(term| balanceOf $token:term $owner:term) =>
      for arg in [token, owner] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .uint256
  | `(term| allowance $token:term $owner:term $spender:term) =>
      for arg in [token, owner, spender] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .uint256
  | `(term| totalSupply $token:term) => do
      requireWordLikeType token "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals token)
      pure .uint256
  | `(term| ecmCall $_moduleFactory:term $args:term) => do
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            requireWordOrDirectArrayType x "ECM argument"
              (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
      | _ => throwErrorAt args "expected list literal [..]"
      pure .uint256
  | `(term| tryExternalCall $name:term $args:term) => do
      let extName := ← expectStringOrIdent name
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            -- verity#1849, G3: accept `Array <wordLike>` / `bytes` / `string`
            -- direct param refs alongside word-like args.
            if let some (_, _, fieldTy, _elemTy, _) := arrayElementDynamicMemberProjection? params x then
              match fieldTy with
              | .array elemTy =>
                  unless externalCallDynamicArgSupported (.array elemTy) do
                    throwErrorAt x s!"tryExternalCall '{extName}' dynamic-member argument currently supports only Array<wordLike> members, got {renderValueType fieldTy}"
              | _ =>
                  throwErrorAt x s!"tryExternalCall '{extName}' dynamic-member argument requires an Array-typed member, got {renderValueType fieldTy}"
            else if let some (_, _, fieldTy, _elemTy, _) := localArrayElementDynamicMemberProjection? locals x then
              match fieldTy with
              | .array elemTy =>
                  unless externalCallDynamicArgSupported (.array elemTy) do
                    throwErrorAt x s!"tryExternalCall '{extName}' dynamic-member alias argument currently supports only Array<wordLike> members, got {renderValueType fieldTy}"
              | _ =>
                  throwErrorAt x s!"tryExternalCall '{extName}' dynamic-member alias argument requires an Array-typed member, got {renderValueType fieldTy}"
            else
              requireWordOrDirectArrayType x s!"tryExternalCall '{extName}' argument"
                (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
      | _ => throwErrorAt args "expected list literal [..]"
      match externalDecls.find? (fun ext => ext.name == extName) with
      | some ext =>
          if ext.returnTys.size > 0 then
            throwErrorAt rhs s!"tryExternalCall '{extName}' returns {ext.returnTys.size} value(s); use tuple destructuring: `let (success, ...) ← tryExternalCall ...`"
          -- Zero-return external: success flag only
          pure .bool
      | none =>
          throwErrorAt rhs s!"unknown external function '{extName}'"
  | `(term| requireSomeUint $optExpr:term $_msg:term) =>
      match stripParens optExpr with
      | `(term| safeAdd $a:term $b:term)
      | `(term| safeSub $a:term $b:term)
      | `(term| safeMul $a:term $b:term)
      | `(term| safeDiv $a:term $b:term) => do
          requireWordLikeType a "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a)
          requireWordLikeType b "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b)
          pure .uint256
      | _ => throwErrorAt rhs "unsupported requireSomeUint source; expected safeAdd, safeSub, safeMul, or safeDiv"
  | `(term| narrowAddPanic $a:term $b:term)
  | `(term| narrowSubPanic $a:term $b:term)
  | `(term| narrowMulPanic $a:term $b:term) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b
      match lhsTy, rhsTy with
      | .uintN lhsBits, .uintN rhsBits =>
          if lhsBits == rhsBits then pure (.uintN lhsBits)
          else throwErrorAt rhs "narrow panic arithmetic requires operands of the same width"
      | _, _ =>
          throwErrorAt rhs "narrow panic arithmetic requires UIntN operands"
  -- Typed-error counterpart to `requireSomeUint`. `requireSomeUintError
  -- (safeXxx a b) ErrName(args)` validates the same `safeXxx` source shape
  -- and result type; argument-type validation against the contract's
  -- `errors` block happens in the do-element walk before the lowering pass.
  | `(term| requireSomeUintError $optExpr:term $_errorName:ident($_args,*)) =>
      match stripParens optExpr with
      | `(term| safeAdd $a:term $b:term)
      | `(term| safeSub $a:term $b:term)
      | `(term| safeMul $a:term $b:term)
      | `(term| safeDiv $a:term $b:term) => do
          requireWordLikeType a "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a)
          requireWordLikeType b "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b)
          pure .uint256
      | _ => throwErrorAt rhs "unsupported requireSomeUintError source; expected safeAdd, safeSub, safeMul, or safeDiv"
  -- Solidity-0.8 default-revert arithmetic (verity#1752). `addPanic`,
  -- `subPanic`, `mulPanic`, `divPanic` are ergonomic shorthands for the
  -- corresponding `requireSomeUint (safeXxx a b) <fixed Panic-style message>`
  -- pattern.  They match the surface of Solidity's `a + b` / `a - b` / `a * b`
  -- / `a / b` operators on `uint256`, where overflow / underflow / division
  -- by zero reverts with `Panic(0x11)` / `Panic(0x12)` rather than wrapping
  -- mod 2^256.
  | `(term| addPanic $a:term $b:term)
  | `(term| subPanic $a:term $b:term)
  | `(term| mulPanic $a:term $b:term)
  | `(term| divPanic $a:term $b:term) => do
      requireWordLikeType a "panic uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a)
      requireWordLikeType b "panic uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b)
      pure .uint256
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
      | some (fn, _argTerms) =>
          ensureCallableAsInternalHelper rhs fn
          match fn.returnTy with
          | .tuple _ =>
              throwErrorAt rhs
                s!"helper call '{fn.name}' returns multiple values; use tuple destructuring"
          | .unit =>
              throwErrorAt rhs
                s!"helper call '{fn.name}' returns Unit and cannot be bound"
          | retTy =>
              pure retTy
      | none =>
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              unsafe qualifiedSingleBindType rhs.raw qualifiedName
          | none =>
              throwErrorAt rhs
                "unsupported bind source; expected getStorage/getStorageAddr/getStorageArrayLength/getStorageArrayElement/getMapping/getMappingAddr/getMappingUint/getMappingUintAddr/getMappingWord/getMapping2/getMappingN/structMember/structMember2/msgSender/msgValue/selfBalance/tload/ecrecover/ecmCall, a direct internal helper call, or a qualified library helper call"

partial def inferTupleSourceTypes?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array ValueType)) := do
  let structCtorTypes? : CommandElabM (Option (Array ValueType)) := do
    match qualifiedFunctionAppSyntax? (stripParens rhs) with
    | some (name, ctorArgs) =>
        if name.toString.endsWith ".mk" then
          pure (some (← ctorArgs.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals)))
        else
          pure none
    | none =>
        match (stripParens rhs).raw with
        | .node _ `Lean.Parser.Term.app args =>
            match args.getD 0 Syntax.missing with
            | .ident _ raw _ _ =>
                if raw.toString.endsWith ".mk" then
                  let ctorArgs := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
                  pure (some (← ctorArgs.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals)))
                else
                  pure none
            | _ => pure none
        | _ => pure none
  match tupleElemsFromTerm? rhs with
  | some elems =>
      pure <| some (← elems.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals))
  | none =>
      match ← structCtorTypes? with
      | some tys => pure (some tys)
      | none =>
        match stripParens rhs with
        | `(term| $id:ident) =>
            match params.find? (fun p => p.name == toString id.getId) with
            | some p =>
                match p.ty with
                | .tuple elemTys => pure (some elemTys.toArray)
                | _ => pure none
            | none => pure none
        | `(term| structMembers $field:term $key:term $members:term) => do
            let fieldName := ← expectStringOrIdent field
            let memberNames := ← expectStringList members
            let memberDecls ← memberNames.mapM fun memberName =>
              lookupStructMemberDecl fields fieldName memberName false
            requireWordLikeType key "structMembers key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
            pure (some (memberDecls.map (·.ty)))
        | `(term| structMembers2 $field:term $key1:term $key2:term $members:term) => do
            let fieldName := ← expectStringOrIdent field
            let memberNames := ← expectStringList members
            let memberDecls ← memberNames.mapM fun memberName =>
              lookupStructMemberDecl fields fieldName memberName true
            requireWordLikeType key1 "structMembers2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
            requireWordLikeType key2 "structMembers2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
            pure (some (memberDecls.map (·.ty)))
        | `(term| arrayElement $name:term $index:term) => do
            requireWordLikeType index "arrayElement index"
              (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
            -- verity#1849, G2: `arrayElement (arrayElement <param> <i>).<dynField> <k>`
            -- never destructures into a tuple — fall through to the scalar
            -- return path. The compound projection's name isn't a direct param
            -- ref so `requireDirectParamRef` would throw if invoked here.
            if (arrayElementDynamicMemberProjection? params name).isSome ||
                (localArrayElementDynamicMemberProjection? locals name).isSome then
              pure none
            else
              match directParamNameWithType? params name with
              | none => pure none
              | some _ =>
                  let sourceTy ← requireDirectParamRef name "arrayElement" params
                  match sourceTy with
                  | .array (.tuple elemTys) =>
                      let _ ← requireSupportedArrayElementTupleSourceType name "arrayElement tuple destructuring" sourceTy
                      pure (some elemTys.toArray)
                  | _ => pure none
        | `(term| tryExternalCall $name:term $args:term) =>
            let extName := ← expectStringOrIdent name
            match stripParens args with
            | `(term| [ $[$xs],* ]) =>
                for x in xs do
                  requireWordOrDirectArrayType x s!"tryExternalCall '{extName}' argument"
                    (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
            | _ => throwErrorAt args "expected list literal [..]"
            match externalDecls.find? (fun ext => ext.name == extName) with
            | some ext =>
                -- tryExternalCall returns (success : Bool, result₁ : T₁, ..., resultₙ : Tₙ)
                pure (some (#[.bool] ++ ext.returnTys))
            | none =>
                -- When called from translation path with empty externalDecls, return none
                -- to let the tryExternalCallBindStmt? helper handle translation.
                -- The validation path (with real externalDecls) catches actual errors.
                pure none
        | other =>
            match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals other with
            | some (fn, _argTerms) =>
                ensureCallableAsInternalHelper rhs fn
                match fn.returnTy with
                | .tuple elemTys => pure (some elemTys.toArray)
                | _ => pure none
            | none => pure none

partial def resolveLocalFunctionApp?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (FunctionDecl × Array Term)) := do
  let some (fnName, argTerms) := localFunctionAppSyntax? stx
    | pure none
  let candidates := functions.filter (fun fn => fn.name == fnName && fn.params.size == argTerms.size)
  if candidates.isEmpty then
    pure none
  else
    let argTypes ← argTerms.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
    let exactMatchedFns := candidates.filter (fun fn =>
      fn.params.map (fun param => param.ty) == argTypes)
    let literalCompatibleFns :=
      if exactMatchedFns.isEmpty then
        candidates.filter (fun fn => argumentTypesMatchParams argTerms argTypes fn.params)
      else
        exactMatchedFns
    match literalCompatibleFns.toList with
    | [fn] => pure (some (fn, argTerms))
    | [] =>
        let expected :=
          String.intercalate ", "
            (candidates.toList.map functionSignatureKey)
        let actual :=
          fnName ++ "(" ++ String.intercalate "," (argTypes.toList.map renderValueType) ++ ")"
        throwErrorAt stx
          s!"no overload of '{fnName}' matches argument types {actual}; candidates: {expected}"
    | _ =>
        throwErrorAt stx
          s!"ambiguous overload resolution for '{fnName}'"

partial def localInternalArrayReturnBind?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (FunctionDecl × Array Term × ValueType)) := do
  match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
  | some (fn, argTerms) =>
      unless fn.name != "fallback" &&
          fn.name != "receive" &&
          fn.params.all (fun param => supportsInternalHelperParamType param.ty) do
        throwErrorAt rhs
          s!"helper call '{fn.name}' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs"
      match fn.returnTy with
      | .array elemTy =>
          if isSingleWordStaticValueType elemTy then
            pure (some (fn, argTerms, elemTy))
          else
            throwErrorAt rhs
              s!"local binding from helper '{fn.name}' returning Array currently supports only static ABI-word elements, got Array {renderValueType elemTy}"
      | _ => pure none
  | none => pure none

partial def resolveQualifiedFunctionApp?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (Name × Array Term)) := do
  let some (fnName, argTerms) := qualifiedFunctionAppSyntax? stx
    | pure none
  if (nameComponents fnName).head? == some "Verity" then
    pure none
  else
    for arg in argTerms do
      requireWordLikeType arg s!"qualified helper '{qualifiedFunctionDisplayName fnName}' argument"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
    pure (some (fnName, argTerms))
end

mutual
partial def validateConstantBody
    (constDecls : Array ConstantDecl)
    (stx : Term)
    (visiting : List String := []) : CommandElabM Unit := do
  let stx := stripParens stx
  match stx with
  | `(term| true) => pure ()
  | `(term| false) => pure ()
  | `(term| constructorArg $idx:num) => throwNonCompileTimeConstantError idx "constructorArg"
  | `(term| msgValue) => throwNonCompileTimeConstantError stx "msgValue"
  | `(term| selfBalance) => throwNonCompileTimeConstantError stx "selfBalance"
  | `(term| blockTimestamp) => throwNonCompileTimeConstantError stx "blockTimestamp"
  | `(term| blockNumber) => throwNonCompileTimeConstantError stx "blockNumber"
  | `(term| blobbasefee) | `(term| Verity.blobbasefee) =>
      throwNonCompileTimeConstantError stx "blobbasefee"
  | `(term| contractAddress) => throwNonCompileTimeConstantError stx "contractAddress"
  | `(term| txOrigin) => throwNonCompileTimeConstantError stx "txOrigin"
  | `(term| chainid) => throwNonCompileTimeConstantError stx "chainid"
  | `(term| calldatasize) => throwNonCompileTimeConstantError stx "calldatasize"
  | `(term| returndataSize) => throwNonCompileTimeConstantError stx "returndataSize"
  | `(term| zeroAddress) => pure ()
  | `(term| isZeroAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| wordToAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| addressToWord $a:term) => validateConstantBody constDecls a visiting
  | `(term| toInt256 $a:term) => validateConstantBody constDecls a visiting
  | `(term| toUint256 $a:term) => validateConstantBody constDecls a visiting
  | `(term| boolToWord $a:term) => validateConstantBody constDecls a visiting
  | `(term| $id:ident) =>
      let name := toString id.getId
      match constDecls.find? (fun c => c.name == name) with
      | none => throwErrorAt stx s!"unknown variable '{name}'"
      | some constant =>
          if visiting.contains name then
            throwErrorAt stx s!"constant '{name}' depends on itself recursively"
          validateConstantBody constDecls constant.body (name :: visiting)
  | `(term| $n:num) => pure ()
  | `(term| add $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sub $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| mul $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| div $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sdiv $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| mod $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| smod $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitAnd $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitOr $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitXor $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitNot $a) => validateConstantBody constDecls a visiting
  | `(term| shl $shift $value) => validateConstantBody constDecls shift visiting *> validateConstantBody constDecls value visiting
  | `(term| shr $shift $value) => validateConstantBody constDecls shift visiting *> validateConstantBody constDecls value visiting
  | `(term| $a == $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a != $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a >= $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a > $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a < $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a <= $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a && $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a || $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalAnd $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalOr $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalNot $a) => validateConstantBody constDecls a visiting
  | `(term| and $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| or $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| xor $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| not $a) => validateConstantBody constDecls a visiting
  | `(term| mload $offset) => throwNonCompileTimeConstantError offset "mload"
  | `(term| tload $offset) => throwNonCompileTimeConstantError offset "tload"
  | `(term| calldataload $offset) => throwNonCompileTimeConstantError offset "calldataload"
  | `(term| extcodesize $addr) => throwNonCompileTimeConstantError addr "extcodesize"
  | `(term| keccak256 $offset $_size) => throwNonCompileTimeConstantError offset "keccak256"
  -- Compile-time Keccak-256 of a string literal (#1973). Allowed in
  -- `constants`: the digest is evaluated at contract translation time.
  | `(term| keccakString $_s:str) => pure ()
  | `(term| call $gas $_target $_value $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "call"
  | `(term| staticcall $gas $_target $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "staticcall"
  | `(term| delegatecall $gas $_target $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "delegatecall"
  | `(term| byte $index $word) => validateConstantBody constDecls index visiting *> validateConstantBody constDecls word visiting
  | `(term| addmod $a $b $c) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting *> validateConstantBody constDecls c visiting
  | `(term| mulmod $a $b $c) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting *> validateConstantBody constDecls c visiting
  | `(term| signextend $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sar $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| slt $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sgt $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| min $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| max $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| ceilDiv $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| ite $cond $thenVal $elseVal) =>
      validateConstantBody constDecls cond visiting *>
      validateConstantBody constDecls thenVal visiting *>
      validateConstantBody constDecls elseVal visiting
  -- Native Lean `if cond then thenVal else elseVal` term.  Validated
  -- the same way as `ite`; lowered identically in the corresponding
  -- branch of `translatePureExprWithTypes`.
  | `(term| if $cond:term then $thenVal:term else $elseVal:term) =>
      validateConstantBody constDecls cond visiting *>
      validateConstantBody constDecls thenVal visiting *>
      validateConstantBody constDecls elseVal visiting
  -- `Verity.keccak256_lit "literal"` / `keccak256_lit "literal"` —
  -- compile-time Keccak-256 of a UTF-8 string literal.  Backed by the
  -- in-tree Keccak engine (see `Verity/Macro/KeccakLit.lean`); no
  -- runtime cost, deterministic at elaboration time.  Required for
  -- EIP-712 type/name/version hashes to bind the *exact* strings
  -- Solidity does, rather than opaque placeholder constants.
  | `(term| Verity.keccak256_lit $_:str) => pure ()
  | `(term| keccak256_lit $_:str) => pure ()
  | _ => throwErrorAt stx "unsupported expression in contract constant"

partial def translateConstantExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (visiting : List String)
    (name : String) : CommandElabM Term := do
  match constDecls.find? (fun c => c.name == name) with
  | none => throwError s!"unknown variable '{name}'"
  | some constant =>
      if visiting.contains name then
        throwError s!"constant '{name}' depends on itself recursively"
      translatePureExprWithTypes fields constDecls immutableDecls #[] #[] constant.body (name :: visiting)

partial def translateLeanExprFromDef
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (origin : Syntax)
    (fnDisplay : String)
    (argExprs : Array Term)
    (expr : Expr) : CommandElabM Term := do
  match expr.consumeMData with
  | .bvar idx =>
      if idx < argExprs.size then
        let argIdx := argExprs.size - 1 - idx
        match argExprs[argIdx]? with
        | some arg => pure arg
        | none => throwErrorAt origin s!"Lean helper '{fnDisplay}' body references an out-of-scope argument"
      else
        throwErrorAt origin s!"Lean helper '{fnDisplay}' body references an out-of-scope argument"
  | .lit (.natVal n) =>
      `(Compiler.CompilationModel.Expr.literal $(natTerm n))
  | .const ``Bool.true _ =>
      `(Compiler.CompilationModel.Expr.literal 1)
  | .const ``Bool.false _ =>
      `(Compiler.CompilationModel.Expr.literal 0)
  | other =>
      let (fn, args) := leanExprAppFnArgs other
      if leanConstNameMatches fn [``OfNat.ofNat] then
        match args.toList with
        | [_ty, .lit (.natVal n), _inst] =>
            `(Compiler.CompilationModel.Expr.literal $(natTerm n))
        | _ =>
            throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported numeric literal form"
      else if leanConstNameMatches fn [``ite] then
        match args.toList with
        | [_ty, cond, _dec, thenExpr, elseExpr] =>
            `(Compiler.CompilationModel.Expr.ite
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs cond)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs thenExpr)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs elseExpr))
        | _ =>
            throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported if/ite form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.toInt256", "Verity.toUint256", "Verity.wordToAddress", "Verity.addressToWord"]
          ["toInt256", "toUint256", "wordToAddress", "addressToWord"] then
        match args.toList with
        | [arg] => translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs arg
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported cast form"
      else if leanConstNameMatches fn [``Neg.neg] then
        match args.toList with
        | [_ty, _inst, arg] =>
            `(Compiler.CompilationModel.Expr.sub
                (Compiler.CompilationModel.Expr.literal 0)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs arg))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported negation form"
      else if leanConstNameMatches fn [``Eq] then
        match args.toList with
        | [_tyExpr, lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.eq
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported equality form"
      else if leanConstNameMatches fn [``LT.lt, ``LE.le, ``GT.gt, ``GE.ge] then
        match args.toList with
        | [tyExpr, _inst, lhs, rhs] =>
            let lhsExpr ← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs
            let rhsExpr ← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs
            match leanConstName? fn with
            | some ``LT.lt =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.slt $lhsExpr $rhsExpr)
                else
                  `(Compiler.CompilationModel.Expr.lt $lhsExpr $rhsExpr)
            | some ``GT.gt =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.sgt $lhsExpr $rhsExpr)
                else
                  `(Compiler.CompilationModel.Expr.gt $lhsExpr $rhsExpr)
            | some ``GE.ge =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.logicalNot
                      (Compiler.CompilationModel.Expr.slt $lhsExpr $rhsExpr))
                else
                  `(Compiler.CompilationModel.Expr.ge $lhsExpr $rhsExpr)
            | _ =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.logicalNot
                      (Compiler.CompilationModel.Expr.sgt $lhsExpr $rhsExpr))
                else
                  `(Compiler.CompilationModel.Expr.le $lhsExpr $rhsExpr)
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported comparison form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.add", "Verity.EVM.Int256.add",
           "Verity.Core.Uint256.add", "Verity.Core.Int256.add"]
          ["add"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.add
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported add form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.sub", "Verity.EVM.Int256.sub",
           "Verity.Core.Uint256.sub", "Verity.Core.Int256.sub"]
          ["sub"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.sub
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported sub form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.mul", "Verity.EVM.Int256.mul",
           "Verity.Core.Uint256.mul", "Verity.Core.Int256.mul"]
          ["mul"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.mul
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported mul form"
      else
        throwErrorAt origin
          s!"Lean helper '{fnDisplay}' body contains unsupported expression '{fn}'; inline it or rewrite the helper using supported pure Verity operations"

partial def translateLeanDefCall?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String) : CommandElabM (Option Term) := do
  let some (head, fnDisplay, argTerms) := leanDefAppSyntax? stx
    | pure none
  let some fnName ← resolveLeanDefName? head
    | pure none
  let some info ← leanDefInfo? fnName
    | pure none
  let (paramTypeExprs, resultTypeExpr) := peelForallTypes info.type
  let argTypes ← argTerms.mapM
    (inferPureExprType fields constDecls immutableDecls externalDecls params locals · visitingConstants)
  checkLeanDefCallArgs stx.raw fnDisplay argTerms paramTypeExprs argTypes
  match valueTypeFromLeanTypeExpr? resultTypeExpr with
  | some ty => requireSupportedLocalBindingType stx.raw s!"Lean helper '{fnDisplay}' return" ty
  | none =>
      throwErrorAt stx
        s!"Lean helper '{fnDisplay}' uses an unsupported return type; supported pure helper returns are Uint256, Int256, Address, Bytes32/Uint256, and Bool"
  let some body := peelLambdaBody info.value argTerms.size
    | throwErrorAt stx s!"Lean helper '{fnDisplay}' body is not a transparent function definition"
  let argExprs ← argTerms.mapM
    (translatePureExprWithTypes fields constDecls immutableDecls params locals · visitingConstants)
  pure (some (← translateLeanExprFromDef fields constDecls immutableDecls params locals stx.raw fnDisplay argExprs body))

partial def translatePureExprWithTypes
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM Term := do
  let stx := stripParens stx
  let localNames := typedLocalNames locals
  let translateIntrinsic (name lowering args minForkTerm : Term) : CommandElabM Term := do
    let intrinsicName := ← expectStringOrIdent name
    let argsExprs ←
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          xs.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals · visitingConstants)
      | _ => throwErrorAt args "expected list literal [..]"
    `(Compiler.CompilationModel.Expr.intrinsic $(strTerm intrinsicName) $lowering
        $minForkTerm [ $[$argsExprs],* ])
  if let some (paramName, index, _fieldTy, elemTy, wordOffset) := arrayElementStructProjection? params stx then
    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
    if valueTypeUsesDynamicData elemTy then
      `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm wordOffset))
    else
      let elementWords ←
        match staticAbiWordCount? elemTy with
        | some n => pure n
        | none => throwErrorAt stx "arrayElement struct projection requires a static or dynamic ABI-decodable element"
      `(Compiler.CompilationModel.Expr.arrayElementWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm elementWords)
        $(natTerm wordOffset))
  else
  if let some (paramName, index, _fieldTy, elemTy, wordOffset) := localArrayElementStructProjection? locals stx then
    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
    if valueTypeUsesDynamicData elemTy then
      `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm wordOffset))
    else
      let elementWords ←
        match staticAbiWordCount? elemTy with
        | some n => pure n
        | none => throwErrorAt stx "arrayElement alias struct projection requires a static or dynamic ABI-decodable element"
      `(Compiler.CompilationModel.Expr.arrayElementWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm elementWords)
        $(natTerm wordOffset))
  else
  -- Direct dynamic-tuple parameter leaf projection (verity#1832): read a
  -- single-word static field at a fixed head offset from a dynamically
  -- encoded struct parameter.
  if let some (paramName, fieldTy, wordOffset) := paramDynamicHeadProjection? params stx then
    let raw ← `(Compiler.CompilationModel.Expr.paramDynamicHeadWord
      $(strTerm paramName)
      $(natTerm wordOffset))
    normalizeTranslatedExprForType fieldTy stx raw
  else
  if (paramDynamicMemberProjection? params stx).isSome then
    throwErrorAt stx "dynamic struct parameter member cannot be used as a scalar expression; pass it to a helper/external expecting an Array or use arrayLength/arrayElement"
  else
  if isParamStructNonLeafProjection params stx then
    throwStructNonLeafProjectionError stx
  else
  if let some (paramName, _ty) := paramStructProjection? params stx then
    `(Compiler.CompilationModel.Expr.param $(strTerm paramName))
  else
  if let some (localName, _ty) := localExternalStaticStructProjection? locals stx then
    `(Compiler.CompilationModel.Expr.localVar $(strTerm localName))
  else
  match stx with
  | `(term| true) => `(Compiler.CompilationModel.Expr.literal 1)
  | `(term| false) => `(Compiler.CompilationModel.Expr.literal 0)
  -- `Verity.keccak256_lit "literal"` / `keccak256_lit "literal"`:
  -- elaborate the in-tree `keccak256_nat` at macro-expansion time and
  -- emit the result as a `literal` constant.  Used for EIP-712 type
  -- hashes, ERC-7201 storage namespaces, event topic constants, etc.
  | `(term| Verity.keccak256_lit $s:str) | `(term| keccak256_lit $s:str) =>
      let n := KeccakEngine.keccak256_str_nat s.getString
      `(Compiler.CompilationModel.Expr.literal $(natTerm n))
  | `(term| constructorArg $idx:num) =>
      `(Compiler.CompilationModel.Expr.constructorArg $idx)
  | `(term| abiHeadWord $target:term $wordOffset:num) => do
      let offset ← natFromSyntax wordOffset
      let (paramName, index?, ty) ←
        match abiHeadWordTarget? params target with
        | some resolved => pure resolved
        | none =>
            match localArrayElementAlias? locals target with
            | some (paramName, index, ty) => pure (paramName, some index, ty)
            | none => throwErrorAt target "abiHeadWord requires a direct parameter, dynamic local alias, or `arrayElement <param> <index>` target"
      match index? with
      | some index =>
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
          if valueTypeUsesDynamicData ty then
            `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm offset))
          else
            let elementWords ←
              match staticAbiWordCount? ty with
              | some n => pure n
              | none => throwErrorAt target "abiHeadWord array element target requires a static ABI word layout"
            `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm elementWords)
              $(natTerm offset))
      | none =>
          unless valueTypeUsesDynamicData ty do
            throwErrorAt target "abiHeadWord direct parameter targets must have dynamic ABI head layout"
          `(Compiler.CompilationModel.Expr.paramDynamicHeadWord
            $(strTerm paramName)
            $(natTerm offset))
  | `(term| Verity.msgSender) =>
      throwPureContextAccessorError stx "msgSender"
  | `(term| Verity.msgValue) =>
      throwPureContextAccessorError stx "msgValue"
  | `(term| Verity.selfBalance) =>
      throwPureContextAccessorError stx "selfBalance"
  | `(term| Verity.blockTimestamp) =>
      throwPureContextAccessorError stx "blockTimestamp"
  | `(term| Verity.blockNumber) =>
      throwPureContextAccessorError stx "blockNumber"
  | `(term| Verity.blobbasefee) =>
      throwPureContextAccessorError stx "blobbasefee"
  | `(term| Verity.contractAddress) =>
      throwPureContextAccessorError stx "contractAddress"
  | `(term| Verity.txOrigin) =>
      throwPureContextAccessorError stx "txOrigin"
  | `(term| Verity.chainid) =>
      throwPureContextAccessorError stx "chainid"
  | `(term| $id:ident) =>
      let name := toString id.getId
      if params.any (fun p => p.name == name) || isTupleComponentRef params name || localNames.contains name then
        lookupVarExpr params localNames name
      else if let some actualName := findContextAccessorShadowName? params localNames name then
        lookupVarExpr params localNames actualName
      else if matchesBareName name "calldatasize" then
        `(Compiler.CompilationModel.Expr.calldatasize)
      else if matchesBareName name "returndataSize" then
        `(Compiler.CompilationModel.Expr.returndataSize)
      else if matchesBareName name "zeroAddress" then
        `(Compiler.CompilationModel.Expr.literal 0)
      else if let some imm := immutableDecls.find? (fun imm => declaredNameMatches name imm.name) then
        match imm.ty with
        | .uint256 | .int256 | .uint8 | .uint16 | .bytes32 | .bool =>
            `(Compiler.CompilationModel.Expr.immutable $(strTerm imm.name))
        | .address => `(Compiler.CompilationModel.Expr.immutable $(strTerm imm.name))
        | _ => throwErrorAt stx s!"immutable '{name}' uses unsupported type"
      else if let some constant := constDecls.find? (fun constant => declaredNameMatches name constant.name) then
        translateConstantExpr fields constDecls immutableDecls visitingConstants constant.name
      else if let some accessor := contextAccessorBareName? name then
        throwPureContextAccessorError stx accessor
      else
        translateConstantExpr fields constDecls immutableDecls visitingConstants name
  | `(term| calldatasize) => `(Compiler.CompilationModel.Expr.calldatasize)
  | `(term| returndataSize) => `(Compiler.CompilationModel.Expr.returndataSize)
  | `(term| zeroAddress) =>
      if params.any (fun p => p.name == "zeroAddress") || localNames.contains "zeroAddress" then
        lookupVarExpr params localNames "zeroAddress"
      else
        `(Compiler.CompilationModel.Expr.literal 0)
  | `(term| isZeroAddress $a:term) =>
      `(Compiler.CompilationModel.Expr.eq
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| wordToAddress $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| addressToWord $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| toInt256 $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| toUint256 $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| narrowUInt $bits:num $a:term) => do
      let width ← natFromSyntax bits
      unless width >= 8 && width < 256 && width % 8 == 0 do
        throwErrorAt bits "narrowUInt width must be a byte multiple from 8 through 248"
      `(Compiler.CompilationModel.Expr.bitAnd
        $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
        (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ width - 1))))
  | `(term| narrowInt $bits:num $a:term) => do
      let width ← natFromSyntax bits
      unless width >= 8 && width < 256 && width % 8 == 0 do
        throwErrorAt bits "narrowInt width must be a byte multiple from 8 through 248"
      `(Compiler.CompilationModel.Expr.signextend
        (Compiler.CompilationModel.Expr.literal $(natTerm (width / 8 - 1)))
        $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| narrowBytes $bytes:num $a:term) => do
      let width ← natFromSyntax bytes
      unless width >= 1 && width < 32 do
        throwErrorAt bytes "narrowBytes width must be from 1 through 31"
      let mask := (2 ^ (8 * width) - 1) * 2 ^ (8 * (32 - width))
      `(Compiler.CompilationModel.Expr.bitAnd
        $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
        (Compiler.CompilationModel.Expr.literal $(natTerm mask)))
  | `(term| boolToWord $a:term) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 1)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| $n:num) => `(Compiler.CompilationModel.Expr.literal $n)
  | `(term| add $a $b) | `(term| $a + $b)
    | `(term| sub $a $b) | `(term| $a - $b)
    | `(term| mul $a $b) | `(term| $a * $b) => do
      let resultTy ← inferPureExprType fields constDecls immutableDecls #[] params locals stx visitingConstants
      let lhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
      let rhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants
      let raw ← match stx with
        | `(term| add $_ $_) | `(term| $_ + $_) => `(Compiler.CompilationModel.Expr.add $lhs $rhs)
        | `(term| sub $_ $_) | `(term| $_ - $_) => `(Compiler.CompilationModel.Expr.sub $lhs $rhs)
        | _ => `(Compiler.CompilationModel.Expr.mul $lhs $rhs)
      match resultTy with
      | .uintN bits =>
          `(Compiler.CompilationModel.Expr.bitAnd $raw
              (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1))))
      | .intN bits =>
          `(Compiler.CompilationModel.Expr.signextend
              (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $raw)
      | _ => pure raw
  | `(term| pow $a $b) | `(term| $a ^ $b) =>
      `(Compiler.CompilationModel.Expr.externalCall Compiler.CompilationModel.builtinExpName
          [$(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants),
           $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)])
  | `(term| div $a $b) | `(term| $a / $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        let raw ← `(Compiler.CompilationModel.Expr.sdiv $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
        match lhsTy with
        | .intN bits =>
            `(Compiler.CompilationModel.Expr.signextend
                (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $raw)
        | _ => pure raw
      else
        `(Compiler.CompilationModel.Expr.div $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sdiv $a $b) => `(Compiler.CompilationModel.Expr.sdiv $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mod $a $b) | `(term| $a % $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        let raw ← `(Compiler.CompilationModel.Expr.smod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
        match lhsTy with
        | .intN bits =>
            `(Compiler.CompilationModel.Expr.signextend
                (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $raw)
        | _ => pure raw
      else
        `(Compiler.CompilationModel.Expr.mod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| smod $a $b) => `(Compiler.CompilationModel.Expr.smod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitAnd $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitOr $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitXor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitNot $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| shl $shift $value) => `(Compiler.CompilationModel.Expr.shl $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| shr $shift $value) => `(Compiler.CompilationModel.Expr.shr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| sar $shift $value) => `(Compiler.CompilationModel.Expr.sar $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| byte $index $value) => `(Compiler.CompilationModel.Expr.byte $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| signextend $byteIndex $value) => `(Compiler.CompilationModel.Expr.signextend $(← translatePureExprWithTypes fields constDecls immutableDecls params locals byteIndex visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| $a == $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      if (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes) then
        let (lhsName, rhsName) ← dynamicEqParamNames stx params a b lhsTy rhsTy
        `(Compiler.CompilationModel.Expr.dynamicBytesEq $(strTerm lhsName) $(strTerm rhsName))
      else
        let lhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
        let rhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants
        let lhs ← match rhsTy with
          | .bytesN bytes =>
              if isNatLiteralTerm a then
                `(Compiler.CompilationModel.Expr.shl
                    (Compiler.CompilationModel.Expr.literal $(natTerm (8 * (32 - bytes)))) $lhs)
              else pure lhs
          | _ => pure lhs
        let rhs ← match lhsTy with
          | .bytesN bytes =>
              if isNatLiteralTerm b then
                `(Compiler.CompilationModel.Expr.shl
                    (Compiler.CompilationModel.Expr.literal $(natTerm (8 * (32 - bytes)))) $rhs)
              else pure rhs
          | _ => pure rhs
        `(Compiler.CompilationModel.Expr.eq
          $lhs $rhs)
  | `(term| $a != $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      if (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes) then
        let (lhsName, rhsName) ← dynamicEqParamNames stx params a b lhsTy rhsTy
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.dynamicBytesEq $(strTerm lhsName) $(strTerm rhsName)))
      else
        let lhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
        let rhs ← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants
        let lhs ← match rhsTy with
          | .bytesN bytes =>
              if isNatLiteralTerm a then
                `(Compiler.CompilationModel.Expr.shl
                    (Compiler.CompilationModel.Expr.literal $(natTerm (8 * (32 - bytes)))) $lhs)
              else pure lhs
          | _ => pure lhs
        let rhs ← match lhsTy with
          | .bytesN bytes =>
              if isNatLiteralTerm b then
                `(Compiler.CompilationModel.Expr.shl
                    (Compiler.CompilationModel.Expr.literal $(natTerm (8 * (32 - bytes)))) $rhs)
              else pure rhs
          | _ => pure rhs
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.eq
              $lhs $rhs))
  | `(term| $a >= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.slt
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)))
      else
        `(Compiler.CompilationModel.Expr.ge $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a > $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        `(Compiler.CompilationModel.Expr.sgt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.gt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sgt $a $b) => `(Compiler.CompilationModel.Expr.sgt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a < $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        `(Compiler.CompilationModel.Expr.slt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.lt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| slt $a $b) => `(Compiler.CompilationModel.Expr.slt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a <= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferNarrowNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == rhsTy && isSignedWordValueType lhsTy then
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.sgt
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)))
      else
        `(Compiler.CompilationModel.Expr.le $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a && $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a || $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalAnd $a $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalOr $a $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalNot $a) => `(Compiler.CompilationModel.Expr.logicalNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| and $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| or $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| xor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| not $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| mload $offset) =>
      `(Compiler.CompilationModel.Expr.mload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| tload $offset) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| calldataload $offset) =>
      `(Compiler.CompilationModel.Expr.calldataload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| extcodesize $addr) =>
      `(Compiler.CompilationModel.Expr.extcodesize
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals addr visitingConstants))
  | `(term| keccak256 $offset $size) =>
      `(Compiler.CompilationModel.Expr.keccak256
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size visitingConstants))
  -- Compile-time Keccak-256 of a string literal (#1973): hash the literal
  -- now and emit a plain numeric literal. The parser already rejects
  -- non-literal arguments, so the digest is unconditionally static.
  | `(term| keccakString $s:str) =>
      let digest := KeccakEngine.keccak256_str_nat s.getString
      `(Compiler.CompilationModel.Expr.literal $(natTerm digest))
  | `(term| call $gas $target $value $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.call
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| staticcall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.staticcall
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| delegatecall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.delegatecall
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| arrayLength $name:term) =>
      -- verity#1849, G1: `arrayLength (arrayElement <param> <i>).<dynField>`
      -- lowers through `Expr.arrayElementDynamicMemberLength`, reading the
      -- length word of the dynamic member at the resolved head offset.
      if let some (paramName, index, _fieldTy, _elemTy, wordOffset) :=
          arrayElementDynamicMemberProjection? params name then
        let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
        `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            $(strTerm paramName)
            $indexExpr
            $(natTerm wordOffset))
      else if let some (paramName, index, _fieldTy, _elemTy, wordOffset) :=
          localArrayElementDynamicMemberProjection? locals name then
        let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
        `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            $(strTerm paramName)
            $indexExpr
            $(natTerm wordOffset))
      else if let some (paramName, _fieldTy, wordOffset) :=
          paramDynamicMemberProjection? params name then
        `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
            $(strTerm paramName)
            $(natTerm wordOffset))
      else if let some (name, _) := localMemoryArray? locals name then
        `(Compiler.CompilationModel.Expr.memoryArrayLength $(strTerm name))
      else
        `(Compiler.CompilationModel.Expr.arrayLength $(strTerm (← expectStringOrIdent name)))
  | `(term| arrayElement $name:term $index:term) => do
      let raw ←
      -- verity#1849, G2: `arrayElement (arrayElement <param> <i>).<dynField> <k>`
      -- lowers through `Expr.arrayElementDynamicMemberElement`.
        if let some (paramName, outerIndex, _fieldTy, _elemTy, wordOffset) :=
          arrayElementDynamicMemberProjection? params name then
        let outerIndexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals outerIndex visitingConstants
        let innerIndexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
        `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberElement
            $(strTerm paramName)
            $outerIndexExpr
            $(natTerm wordOffset)
            $innerIndexExpr)
        else if let some (paramName, outerIndex, _fieldTy, _elemTy, wordOffset) :=
          localArrayElementDynamicMemberProjection? locals name then
        let outerIndexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals outerIndex visitingConstants
        let innerIndexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
        `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberElement
            $(strTerm paramName)
            $outerIndexExpr
            $(natTerm wordOffset)
            $innerIndexExpr)
        else if let some (paramName, _fieldTy, wordOffset) :=
          paramDynamicMemberProjection? params name then
        let innerIndexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
        `(Compiler.CompilationModel.Expr.paramDynamicMemberElement
            $(strTerm paramName)
            $(natTerm wordOffset)
            $innerIndexExpr)
        else if let some (name, _) := localMemoryArray? locals name then
        `(Compiler.CompilationModel.Expr.memoryArrayElement
            $(strTerm name)
            $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants))
        else
          `(Compiler.CompilationModel.Expr.arrayElement
              $(strTerm (← expectStringOrIdent name))
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants))
      let elemTy ← inferPureExprType fields constDecls immutableDecls #[] params locals stx visitingConstants
      match elemTy with
      | .uintN bits =>
          `(Compiler.CompilationModel.Expr.bitAnd $raw
              (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1))))
      | .intN bits =>
          `(Compiler.CompilationModel.Expr.signextend
              (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $raw)
      | .bytesN bytes =>
          let mask := (2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))
          `(Compiler.CompilationModel.Expr.bitAnd $raw
              (Compiler.CompilationModel.Expr.literal $(natTerm mask)))
      | _ => pure raw
  | `(term| ceilDiv $a $b) =>
      `(Compiler.CompilationModel.Expr.ceilDiv
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mulDivDown $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivDown
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| mulDivUp $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivUp
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| mulDiv512Down $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDiv512Down
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| mulDiv512Up $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDiv512Up
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| wMulDown $a $b) =>
      `(Compiler.CompilationModel.Expr.wMulDown
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| wDivUp $a $b) =>
      `(Compiler.CompilationModel.Expr.wDivUp
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| min $a $b) => `(Compiler.CompilationModel.Expr.min $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| max $a $b) => `(Compiler.CompilationModel.Expr.max $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| ite $cond $thenVal $elseVal) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals thenVal visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals elseVal visitingConstants))
  -- Native Lean `if ... then ... else ...` term, equivalent to
  -- `ite cond thenVal elseVal` for the macro lowering.  Lets contract
  -- authors write idiomatic expressions like
  -- `let x := if a > b then a else b` directly in `let :=` bindings,
  -- without falling back to per-shape helper functions.
  | `(term| if $cond:term then $thenVal:term else $elseVal:term) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals thenVal visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals elseVal visitingConstants))
  | `(term| externalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argsExprs ←
        match stripParens args with
        | `(term| [ $[$xs],* ]) => do
            let mut out : Array Term := #[]
            for arg in xs do
              match directParamNameWithType? params arg with
              | some (name, ty) =>
                  if externalCallDynamicArgSupported ty then
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_data_offset")))
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_length")))
                  else
                    out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg visitingConstants)
              | none =>
                  if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                      arrayElementDynamicMemberProjection? params arg then
                    if externalCallDynamicArgSupported fieldTy then
                      let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
                      out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                        $(strTerm paramName)
                        $indexExpr
                        $(natTerm wordOffset)))
                      out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                        $(strTerm paramName)
                        $indexExpr
                        $(natTerm wordOffset)))
                    else
                      out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg visitingConstants)
                  else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                      localArrayElementDynamicMemberProjection? locals arg then
                    if externalCallDynamicArgSupported fieldTy then
                      let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
                      out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                        $(strTerm paramName)
                        $indexExpr
                        $(natTerm wordOffset)))
                      out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                        $(strTerm paramName)
                        $indexExpr
                        $(natTerm wordOffset)))
                    else
                      out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg visitingConstants)
                  else if let some (paramName, fieldTy, wordOffset) :=
                      paramDynamicMemberProjection? params arg then
                    if externalCallDynamicArgSupported fieldTy then
                      out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset
                        $(strTerm paramName)
                        $(natTerm wordOffset)))
                      out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
                        $(strTerm paramName)
                        $(natTerm wordOffset)))
                    else
                      out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg visitingConstants)
                  else
                    out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg visitingConstants)
            pure out
        | _ => throwErrorAt args "expected list literal [..]"
      `(Compiler.CompilationModel.Expr.externalCall $(strTerm extName) [ $[$argsExprs],* ])
  | `(term| intrinsic_fusaka $name:term $lowering:term $args:term) =>
      translateIntrinsic name lowering args (← `(Verity.Core.Intrinsics.HardFork.osaka))
  | `(term| intrinsic_osaka $name:term $lowering:term $args:term) =>
      translateIntrinsic name lowering args (← `(Verity.Core.Intrinsics.HardFork.osaka))
  | `(term| intrinsic_prague $name:term $lowering:term $args:term) =>
      translateIntrinsic name lowering args (← `(Verity.Core.Intrinsics.HardFork.prague))
  | `(term| intrinsic_cancun $name:term $lowering:term $args:term) =>
      translateIntrinsic name lowering args (← `(Verity.Core.Intrinsics.HardFork.cancun))
  | `(term| intrinsic $name:term $lowering:term $args:term) =>
      let intrinsicName := ← expectStringOrIdent name
      let registered ← liftIO getRegisteredIntrinsics
      let minFork ←
        match registered.find? (fun decl => decl.name = intrinsicName) with
        | some decl => pure decl.minFork
        | none =>
            throwErrorAt name
              s!"unknown intrinsic '{intrinsicName}'; declare it first with `verity_intrinsic` so the compiler can enforce min_fork"
      let minForkTerm ← hardForkTermFromParsed minFork
      translateIntrinsic name lowering args minForkTerm
  | `(term| clz $x:term) =>
      let xExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals x visitingConstants
      `(Compiler.CompilationModel.Expr.intrinsic "clz"
          (Verity.Core.Intrinsics.YulLowering.verbatim 1 1 "1e")
          Verity.Core.Intrinsics.HardFork.osaka
          [$xExpr])
  | `(term| msb $x:term) =>
      let xExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals x visitingConstants
      let clzExpr ← `(Compiler.CompilationModel.Expr.intrinsic "clz"
          (Verity.Core.Intrinsics.YulLowering.verbatim 1 1 "1e")
          Verity.Core.Intrinsics.HardFork.osaka
          [$xExpr])
      `(Compiler.CompilationModel.Expr.ite
          (Compiler.CompilationModel.Expr.eq $xExpr (Compiler.CompilationModel.Expr.literal 0))
          (Compiler.CompilationModel.Expr.literal 0)
          (Compiler.CompilationModel.Expr.sub (Compiler.CompilationModel.Expr.literal 255) $clzExpr))
  | `(term| fork_if_at_least $fork:ident then $thenExpr:term else $elseExpr:term) =>
      `(Compiler.CompilationModel.Expr.forkIfAtLeast
          $(← hardForkTermFromIdent fork)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals thenExpr visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals elseExpr visitingConstants))
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key visitingConstants)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1 visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2 visitingConstants)
          $(strTerm memberName))
  | _ =>
      match ← translateLeanDefCall? fields constDecls immutableDecls #[] params locals stx visitingConstants with
      | some expr => pure expr
      | none => throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"
end

partial def translatePureExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM Term :=
  translatePureExprWithTypes fields constDecls immutableDecls params
    (locals.map (fun name => mkTypedLocal name .uint256)) stx visitingConstants

def translateAbiEncodeProjection?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (Array Term)) := do
  match stripParens stx with
  | `(term| abiEncode $target:term) =>
      if let some (paramName, index, fieldTy, elemTy, wordOffset) :=
          localArrayElementStructProjectionResolved? locals target then
        let wordCount ←
          match staticAbiWordCount? fieldTy with
          | some n => pure n
          | none => throwErrorAt target "abiEncode projection requires a nested static ABI struct/tuple"
        let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
        let mut exprs : Array Term := #[]
        for offset in List.range wordCount do
          if valueTypeUsesDynamicData elemTy then
            exprs := exprs.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm (wordOffset + offset))))
          else
            let elementWords ←
              match staticAbiWordCount? elemTy with
              | some n => pure n
              | none => throwErrorAt target "abiEncode array-element projection requires static ABI layout"
            exprs := exprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm elementWords)
              $(natTerm (wordOffset + offset))))
        pure (some exprs)
      else if let some (paramName, fieldTy, wordOffset) :=
          paramDynamicStaticCompositeProjection? params target then
        let wordCount ←
          match staticAbiWordCount? fieldTy with
          | some n => pure n
          | none => throwErrorAt target "abiEncode projection requires a nested static ABI struct/tuple"
        let mut exprs : Array Term := #[]
        for offset in List.range wordCount do
          exprs := exprs.push (← `(Compiler.CompilationModel.Expr.paramDynamicHeadWord
            $(strTerm paramName)
            $(natTerm (wordOffset + offset))))
        pure (some exprs)
      else
        let ty ← inferPureExprType fields constDecls immutableDecls #[] params locals target
        let wordCount ←
          match staticAbiWordCount? ty with
          | some n => pure n
          | none => throwErrorAt target "abiEncode requires a static ABI value"
        if wordCount == 1 then
          pure (some #[← translatePureExprWithTypes fields constDecls immutableDecls params locals target])
        else
          throwErrorAt target "abiEncode for this static value is not addressable as ABI head words"
  | _ => pure none

def validateWordLikeExprListLiteral
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (args : Term)
    (context : String) : CommandElabM Unit := do
  match stripParens args with
  | `(term| [ $[$xs],* ]) =>
      for x in xs do
        requireWordLikeType x context
          (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
  | _ => throwErrorAt args "expected list literal [..]"

def validateEcmExprListLiteral
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (args : Term)
    (context : String) : CommandElabM Unit := do
  match stripParens args with
  | `(term| [ $[$xs],* ]) =>
      for x in xs do
        if let some (_, _, fieldTy, _elemTy, _) := arrayElementDynamicMemberProjection? params x then
          unless externalCallDynamicArgSupported fieldTy do
            throwErrorAt x s!"{context} dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
        else if let some (_, _, fieldTy, _elemTy, _) := localArrayElementDynamicMemberProjection? locals x then
          unless externalCallDynamicArgSupported fieldTy do
            throwErrorAt x s!"{context} dynamic-member alias argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
        else if let some (_, fieldTy, _) := paramDynamicMemberProjection? params x then
          unless externalCallDynamicArgSupported fieldTy do
            throwErrorAt x s!"{context} dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
        else
          requireWordOrDirectArrayType x context
            (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
  | _ => throwErrorAt args "expected list literal [..]"

partial def syntaxMentionsIdent (stx : Syntax) (name : String) : Bool :=
  match stx with
  | .ident _ raw _ _ => raw.toString == name
  | .node _ _ args => args.any (fun child => syntaxMentionsIdent child name)
  | _ => false

def freshSyntheticLocalName
    (base : String)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String) : String :=
  let used :=
    ((params.map (·.name)) ++ typedLocalNames locals ++ mutableLocals).toList
  let rec go (remaining : Nat) (suffix : Nat) : String :=
    let candidate :=
      if suffix == 0 then base else s!"{base}_{suffix}"
    if !(used.contains candidate) then
      candidate
    else
      match remaining with
      | 0 => s!"{base}_fresh"
      | n + 1 => go n (suffix + 1)
  go used.length 0

def parseTryCatchHandler
    (handler : Term) : CommandElabM (Option String × Array (TSyntax `doElem)) := do
  match stripParens handler with
  | `(term| fun $name:ident => do $[$elems:doElem]*) =>
      pure (some (toString name.getId), elems)
  | `(term| do $[$elems:doElem]*) =>
      pure (none, elems)
  | _ =>
      throwErrorAt handler
        "tryCatch handler must be `fun _ => do ...` or a direct `do ...` block"

def validateTryCatchHandlerDoesNotUsePayload
    (handler : Term)
    (payloadName? : Option String)
    (elems : Array (TSyntax `doElem)) : CommandElabM Unit := do
  match payloadName? with
  | none => pure ()
  | some payloadName =>
      if elems.any (fun elem => syntaxMentionsIdent elem.raw payloadName) then
        throwErrorAt handler
          s!"tryCatch catch payload '{payloadName}' is not available on the compilation-model path yet; use `_`/ignore it and read returndata explicitly if needed"

unsafe def evalExternalCallModuleTerm
    (moduleTerm : Term) : CommandElabM Compiler.ECM.ExternalCallModule := do
  liftTermElabM do
    let expectedType := mkConst ``Compiler.ECM.ExternalCallModule
    let expr ← Lean.Elab.Term.elabTermEnsuringType moduleTerm expectedType
    Lean.Meta.evalExpr Compiler.ECM.ExternalCallModule expectedType expr .unsafe

def validateEffectOnlyEcmModuleTerm
    (moduleTerm : Term) : CommandElabM Unit := do
  let mod ← unsafe evalExternalCallModuleTerm moduleTerm
  if !mod.resultVars.isEmpty then
    throwErrorAt moduleTerm
      s!"ecmDo requires an effect-only ECM module, but '{mod.name}' binds {mod.resultVars.length} result value(s)"

def validateSingleResultEcmModuleTerm
    (moduleTerm : Term)
    (boundVarName : String) : CommandElabM Unit := do
  let mod ← unsafe evalExternalCallModuleTerm moduleTerm
  if mod.resultVars != [boundVarName] then
    throwErrorAt moduleTerm
      s!"ecmCall must elaborate to an ECM module binding exactly ['{boundVarName}'], but '{mod.name}' binds {repr mod.resultVars}"

def validateResultEcmModuleTerm
    (moduleTerm : Term)
    (boundVarNames : Array String) : CommandElabM Unit := do
  let mod ← unsafe evalExternalCallModuleTerm moduleTerm
  if mod.resultVars != boundVarNames.toList then
    throwErrorAt moduleTerm
      s!"ecmBind must elaborate to an ECM module binding exactly {repr boundVarNames.toList}, but '{mod.name}' binds {repr mod.resultVars}"

def arrayElementTupleElemExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      -- verity#1849, G2: compound projections never destructure into a tuple.
      if (arrayElementDynamicMemberProjection? params name).isSome ||
          (localArrayElementDynamicMemberProjection? locals name).isSome then
        return none
      match directParamNameWithType? params name with
      | none => return none
      | some _ => pure ()
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          let elementWords ←
            match staticAbiWordCount? (.tuple elemTys) with
            | some n => pure n
            | none =>
                throwErrorAt rhs
                  "arrayElement tuple destructuring requires a static ABI-word tuple element type"
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let mut offset := 0
          let mut exprs : Array Term := #[]
          for elemTy in elemTys do
            let elemWords ←
              match staticAbiWordCount? elemTy with
              | some n => pure n
              | none =>
                  throwErrorAt rhs
                    "arrayElement tuple destructuring requires static ABI-word tuple members"
            if elemWords != 1 then
              throwErrorAt rhs
                "arrayElement tuple destructuring currently supports top-level single-word tuple members"
            exprs := exprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm elementWords)
              $(natTerm offset)))
            offset := offset + elemWords
          pure (some exprs)
      | _ => pure none
  | _ => pure none

def arrayElementTupleDestructureStmts?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option (Array Term × TypedLocal)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      -- verity#1849, G2: compound projections never destructure into a tuple.
      if (arrayElementDynamicMemberProjection? params name).isSome ||
          (localArrayElementDynamicMemberProjection? locals name).isSome then
        return none
      match directParamNameWithType? params name with
      | none => return none
      | some _ => pure ()
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          if names.size != elemTys.length then
            throwErrorAt rhs
              s!"tuple destructuring binds {names.size} names, but the source provides {elemTys.length} values"
          let syntheticUsed := mutableLocals ++ names.filterMap id
          let indexName := freshSyntheticLocalName "arrayElement_index" params locals syntheticUsed
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let indexStmt ←
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm indexName) $indexExpr)
          let indexLocal ←
            `(Compiler.CompilationModel.Expr.localVar $(strTerm indexName))
          let mut offset := 0
          let mut valueExprs : Array Term := #[]
          match staticAbiWordCount? (.tuple elemTys) with
          | some elementWords =>
              for elemTy in elemTys do
                let elemWords ←
                  match staticAbiWordCount? elemTy with
                  | some n => pure n
                  | none =>
                      throwErrorAt rhs
                        "arrayElement tuple destructuring requires static ABI-word tuple members"
                if elemWords != 1 then
                  throwErrorAt rhs
                    "arrayElement tuple destructuring currently supports top-level single-word tuple members"
                valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
                  $(strTerm paramName)
                  $indexLocal
                  $(natTerm elementWords)
                  $(natTerm offset)))
                offset := offset + elemWords
          | none =>
              let _ ←
                match abiLocalHeadWordCount? (.tuple elemTys) with
                | some n => pure n
                | none =>
                    throwErrorAt rhs
                      "arrayElement tuple destructuring requires an ABI-decodable tuple element type"
              for (elemTy, name?) in elemTys.zip names.toList do
                if isSingleWordStaticValueType elemTy then
                  valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
                    $(strTerm paramName)
                    $indexLocal
                    $(natTerm offset)))
                else
                  match name? with
                  | none =>
                      valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.literal 0))
                  | some boundName =>
                      throwErrorAt rhs
                        s!"arrayElement tuple destructuring cannot bind dynamic member '{boundName}' yet; use '_' for nested dynamic members"
                let elemHeadWords ←
                  match abiLocalHeadWordCount? elemTy with
                  | some n => pure n
                  | none =>
                      throwErrorAt rhs
                        "arrayElement tuple destructuring requires ABI-decodable tuple members"
                offset := offset + elemHeadWords
          let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
            name?.map (fun name => (name, valueExpr))
          let boundStmts ← boundPairs.mapM fun (name, valueExpr) =>
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
          pure (some (#[indexStmt] ++ boundStmts, mkTypedLocal indexName .uint256))
      | _ => pure none
  | _ => pure none

def arrayElementTupleReturnStmts?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (rhs : Term) : CommandElabM (Option (Array Term × TypedLocal)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      -- verity#1849, G2: compound projections (`(arrayElement <p> <i>).<dynField>`)
      -- never destructure into a tuple return — bail out without throwing on
      -- the non-ident name. The scalar return path will pick this up.
      if (arrayElementDynamicMemberProjection? params name).isSome ||
          (localArrayElementDynamicMemberProjection? locals name).isSome then
        return none
      match directParamNameWithType? params name with
      | none => return none
      | some _ => pure ()
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          let elementWords ←
            match staticAbiWordCount? (.tuple elemTys) with
            | some n => pure n
            | none =>
                throwErrorAt rhs
                  "arrayElement tuple return requires a static ABI-word tuple element type"
          let indexName := freshSyntheticLocalName "arrayElement_index" params locals mutableLocals
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let indexStmt ←
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm indexName) $indexExpr)
          let indexLocal ←
            `(Compiler.CompilationModel.Expr.localVar $(strTerm indexName))
          let mut offset := 0
          let mut valueExprs : Array Term := #[]
          for elemTy in elemTys do
            let elemWords ←
              match staticAbiWordCount? elemTy with
              | some n => pure n
              | none =>
                  throwErrorAt rhs
                    "arrayElement tuple return requires static ABI-word tuple members"
            if elemWords != 1 then
              throwErrorAt rhs
                "arrayElement tuple return currently supports top-level single-word tuple members"
            valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexLocal
              $(natTerm elementWords)
              $(natTerm offset)))
            offset := offset + elemWords
          let returnStmt ←
            `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ])
          pure (some (#[indexStmt, returnStmt], mkTypedLocal indexName .uint256))
      | _ => pure none
  | _ => pure none

def tupleLiteralOrStructValueExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let structCtorValueExprs? : CommandElabM (Option (Array Term)) := do
    match qualifiedFunctionAppSyntax? (stripParens rhs) with
    | some (name, ctorArgs) =>
        if name.toString.endsWith ".mk" then
          pure (some (← ctorArgs.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)))
        else
          pure none
    | none =>
        match (stripParens rhs).raw with
        | .node _ `Lean.Parser.Term.app args =>
            match args.getD 0 Syntax.missing with
            | .ident _ raw _ _ =>
                if raw.toString.endsWith ".mk" then
                  let ctorArgs := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
                  pure (some (← ctorArgs.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)))
                else
                  pure none
            | _ => pure none
        | _ => pure none
  let structValueExprs? : CommandElabM (Option (Array Term)) := do
    match stripParens rhs with
    | `(term| structMembers $field:term $key:term $members:term) => do
        let fieldName := ← expectStringOrIdent field
        let memberNames := ← expectStringList members
        let exprs ← memberNames.mapM fun memberName => do
          let _ ← lookupStructMemberDecl fields fieldName memberName false
          `(Compiler.CompilationModel.Expr.structMember
              $(strTerm fieldName)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(strTerm memberName))
        pure (some exprs)
    | `(term| structMembers2 $field:term $key1:term $key2:term $members:term) => do
        let fieldName := ← expectStringOrIdent field
        let memberNames := ← expectStringList members
        let exprs ← memberNames.mapM fun memberName => do
          let _ ← lookupStructMemberDecl fields fieldName memberName true
          `(Compiler.CompilationModel.Expr.structMember2
              $(strTerm fieldName)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
              $(strTerm memberName))
        pure (some exprs)
    | _ => pure none
  match tupleElemsFromTerm? rhs with
  | some elems =>
      pure (some (← elems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)))
  | none =>
      match ← arrayElementTupleElemExprs? fields constDecls immutableDecls params locals rhs with
      | some exprs => pure (some exprs)
      | none =>
          match ← structCtorValueExprs? with
          | some exprs => pure (some exprs)
          | none => structValueExprs?

def tupleValueExprs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Array Term) := do
  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
  | some exprs => pure exprs
  | none =>
      match stripParens rhs with
      | `(term| $id:ident) =>
          match (← tupleParamElemExprs? params (toString id.getId)) with
          | some exprs => pure exprs
          | none => throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, or structMembers/structMembers2 source"
      | _ =>
          throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, or structMembers/structMembers2 source"

def tupleReturnValueExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
  | some exprs => pure (some exprs)
  | none =>
      match stripParens rhs with
      | `(term| $id:ident) =>
          tupleParamElemExprs? params (toString id.getId)
      | _ =>
          pure none

partial def staticInternalHelperBindingNames (name : String) (ty : ValueType) : List String :=
  match ty with
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => [name]
  | .fixedArray elemTy size =>
      (List.range size).flatMap fun idx =>
        staticInternalHelperBindingNames s!"{name}_{idx}" elemTy
  | .tuple elemTys =>
      let rec goTuple (tys : List ValueType) (idx : Nat) : List String :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticInternalHelperBindingNames s!"{name}_{idx}" elemTy ++ goTuple rest (idx + 1)
      goTuple elemTys 0
  | .struct _ fields =>
      let rec goStruct (fs : List (String × ValueType)) (idx : Nat) : List String :=
        match fs with
        | [] => []
        | field :: rest =>
            staticInternalHelperBindingNames s!"{name}_{idx}" field.snd ++ goStruct rest (idx + 1)
      goStruct fields 0
  | .newtype _ baseTy => staticInternalHelperBindingNames name baseTy
  | _ => []

def isStaticCompositeInternalHelperType : ValueType → Bool
  | .tuple _ | .struct _ _ | .fixedArray _ _ => true
  | .newtype _ baseTy => isStaticCompositeInternalHelperType baseTy
  | _ => false

def translateInternalHelperCallArgs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (fn : FunctionDecl)
    (argTerms : Array Term) : CommandElabM (Array Term) := do
  let mut out : Array Term := #[]
  for idx in [:argTerms.size] do
    let some arg := argTerms[idx]? | pure ()
    let some fnParam := fn.params[idx]? | pure ()
    match fnParam.ty with
    | .array _ =>
        match directParamNameWithType? params arg with
        | some (name, _) =>
            out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm (memoryArrayDataOffsetName name))))
            out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm (memoryArrayLengthName name))))
        | none =>
            if let some (name, _) := localMemoryArray? locals arg then
              out := out.push (← `(Compiler.CompilationModel.Expr.localVar $(strTerm (memoryArrayDataOffsetName name))))
              out := out.push (← `(Compiler.CompilationModel.Expr.localVar $(strTerm (memoryArrayLengthName name))))
            else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                arrayElementDynamicMemberProjection? params arg then
              match fieldTy with
              | .array _ =>
                  let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
              | _ =>
                  throwErrorAt arg s!"helper call '{fn.name}' Array parameter '{fnParam.name}' requires an Array-typed projected member, got {renderValueType fieldTy}"
            else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                localArrayElementDynamicMemberProjection? locals arg then
              match fieldTy with
              | .array _ =>
                  let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
              | _ =>
                  throwErrorAt arg s!"helper call '{fn.name}' Array parameter '{fnParam.name}' requires an Array-typed projected alias member, got {renderValueType fieldTy}"
            else if let some (paramName, fieldTy, wordOffset) :=
                paramDynamicMemberProjection? params arg then
              match fieldTy with
              | .array _ =>
                  out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset
                    $(strTerm paramName)
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
                    $(strTerm paramName)
                    $(natTerm wordOffset)))
              | _ =>
                  throwErrorAt arg s!"helper call '{fn.name}' Array parameter '{fnParam.name}' requires an Array-typed projected member, got {renderValueType fieldTy}"
            else
              throwErrorAt arg
                s!"helper call '{fn.name}' Array parameter '{fnParam.name}' currently requires a direct Array parameter reference or projected struct-array member"
    | _ =>
        if valueTypeUsesDynamicData fnParam.ty then
          match directParamNameWithType? params arg with
          | some (name, ty) =>
              if valueTypeUsesDynamicData ty then
                match fnParam.ty with
                | .bytes | .string =>
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_data_offset")))
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_length")))
                | _ =>
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_data_offset")))
              else
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
          | none =>
              if let some (paramName, index, _elemTy) := arrayElementDynamicTupleArg? params arg then
                let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicDataOffset
                  $(strTerm paramName)
                  $indexExpr))
              else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                  arrayElementDynamicMemberProjection? params arg then
                match fnParam.ty, fieldTy with
                | .bytes, .bytes | .string, .string =>
                    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                    out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                      $(strTerm paramName)
                      $indexExpr
                      $(natTerm wordOffset)))
                    out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                      $(strTerm paramName)
                      $indexExpr
                      $(natTerm wordOffset)))
                | _, _ =>
                    out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
              else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                  localArrayElementDynamicMemberProjection? locals arg then
                match fnParam.ty, fieldTy with
                | .bytes, .bytes | .string, .string =>
                    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                    out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                      $(strTerm paramName)
                      $indexExpr
                      $(natTerm wordOffset)))
                    out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                      $(strTerm paramName)
                      $indexExpr
                      $(natTerm wordOffset)))
                | _, _ =>
                    out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
              else if let some (paramName, fieldTy, wordOffset) :=
                  paramDynamicMemberProjection? params arg then
                match fnParam.ty, fieldTy with
                | .bytes, .bytes | .string, .string =>
                    out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset
                      $(strTerm paramName)
                      $(natTerm wordOffset)))
                    out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
                      $(strTerm paramName)
                      $(natTerm wordOffset)))
                | _, _ =>
                    out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
              else
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
        else
          if isStaticCompositeInternalHelperType fnParam.ty then
            match directParamNameWithType? params arg with
            | some (name, ty) =>
                let bindingNames := staticInternalHelperBindingNames name ty
                if bindingNames.isEmpty then
                  out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
                else
                  for bindingName in bindingNames do
                    out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm bindingName)))
            | none =>
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
          else
            out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
  pure out

def translateLinkedExternalCallArgs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (argTerms : Array Term) : CommandElabM (Array Term) := do
  let mut out : Array Term := #[]
  for arg in argTerms do
    match ← translateAbiEncodeProjection? fields constDecls immutableDecls params locals arg with
    | some exprs =>
        out := out ++ exprs
    | none =>
        match directParamNameWithType? params arg with
        | some (name, ty) =>
            if externalCallDynamicArgSupported ty then
              out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_data_offset")))
              out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_length")))
            else
              out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
        | none =>
            if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                arrayElementDynamicMemberProjection? params arg then
              if externalCallDynamicArgSupported fieldTy then
                let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                  $(strTerm paramName)
                  $indexExpr
                  $(natTerm wordOffset)))
                out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                  $(strTerm paramName)
                  $indexExpr
                  $(natTerm wordOffset)))
              else
                throwErrorAt arg s!"linked external dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                localArrayElementDynamicMemberProjection? locals arg then
              if externalCallDynamicArgSupported fieldTy then
                let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                  $(strTerm paramName)
                  $indexExpr
                  $(natTerm wordOffset)))
                out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                  $(strTerm paramName)
                  $indexExpr
                  $(natTerm wordOffset)))
              else
                throwErrorAt arg s!"linked external dynamic-member alias argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else if let some (paramName, fieldTy, wordOffset) :=
                paramDynamicMemberProjection? params arg then
              if externalCallDynamicArgSupported fieldTy then
                out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset
                  $(strTerm paramName)
                  $(natTerm wordOffset)))
                out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
                  $(strTerm paramName)
                  $(natTerm wordOffset)))
              else
                throwErrorAt arg s!"linked external dynamic-member argument currently supports only Array<wordLike>/bytes/string members, got {renderValueType fieldTy}"
            else
              out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals arg)
  pure out

def tupleInternalCallAssignStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option Term) := do
  let rhs := stripParens rhs
  let initialUsedNames := (params.toList.map (fun p => p.name)) ++ (typedLocalNames locals).toList ++ (names.filterMap id).toList
  let (_, targetNamesRev) := names.toList.zipIdx.foldl
    (fun (acc : List String × List String) (name?, idx) =>
      let (usedNames, targetNamesRev) := acc
      let targetName := match name? with
        | some name => name
        | none => freshDiscardName usedNames idx
      (targetName :: usedNames, targetName :: targetNamesRev))
    (initialUsedNames, [])
  let targetNames := targetNamesRev.reverse
  let resultNameTerms := targetNames.toArray.map strTerm
  match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
  | some (fn, argTerms) =>
      ensureCallableAsInternalHelper rhs fn
      let argExprs ← translateInternalHelperCallArgs
        fields constDecls immutableDecls params locals fn argTerms
      pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
        [ $[$resultNameTerms],* ]
        $(strTerm (internalHelperSpecNameFor fn))
        [ $[$argExprs],* ])))
  | none =>
      match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
      | some (qualifiedName, argTerms) =>
          let _ ← unsafe qualifiedTupleBindTypedLocals rhs.raw qualifiedName names
          let argExprs ← argTerms.mapM
            (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
            [ $[$resultNameTerms],* ]
            $(strTerm (qualifiedInternalHelperName functions qualifiedName))
            [ $[$argExprs],* ])))
      | none =>
          pure none

/-- Try to translate a tuple‐destructured `tryExternalCall "name" [args]` RHS into
    a `Stmt.tryExternalCallBind` term.  Returns `none` when the RHS is not a
    `tryExternalCall` application.  Returns the statement term and the inferred
    types for each bound name (Bool for success flag, Uint256 for all result
    vars — precise return types require external decl lookup which happens in
    the validation pass).  (#1727, Axis 1 Step 5f) -/
def tryExternalCallBindStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option (Term × Array TypedLocal)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| tryExternalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argExprs ← match stripParens args with
        | `(term| [ $[$xs],* ]) =>
            translateLinkedExternalCallArgs fields constDecls immutableDecls params locals xs
        | _ => throwErrorAt args "expected list literal [..]"
      -- names[0] is the success flag, names[1..] are result vars
      let initialUsedNames := (params.toList.map (fun p => p.name)) ++ (typedLocalNames locals).toList ++ (names.filterMap id).toList
      let (_, targetNamesRev) := names.toList.zipIdx.foldl
        (fun (acc : List String × List String) (name?, idx) =>
          let (usedNames, targetNamesRev) := acc
          let targetName := match name? with
            | some name => name
            | none => freshDiscardName usedNames idx
          (targetName :: usedNames, targetName :: targetNamesRev))
        (initialUsedNames, [])
      let targetNames := targetNamesRev.reverse
      let successVar := match targetNames.head? with
        | some n => n
        | none => "_try_success"
      let resultVars := targetNames.drop 1
      let successVarTerm := strTerm successVar
      let resultTys ←
        match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext =>
            if ext.returnTys.size != resultVars.length then
              throwErrorAt rhs s!"tryExternalCall '{extName}' binds {resultVars.length} result value(s), but the external declaration returns {ext.returnTys.size}"
            pure ext.returnTys
        | none =>
            -- Validation reports the unknown external with full context; keep
            -- translation moving with word-shaped placeholders.
            pure (Array.replicate resultVars.length .uint256)
      let mut flattenedResultVars : Array String := #[]
      let mut visibleLocals : Array TypedLocal := #[mkTypedLocal successVar .bool]
      for (resultVar, resultTy) in resultVars.toArray.zip resultTys do
        let flatNames ← flattenExternalResultNames resultVar resultTy
        flattenedResultVars := flattenedResultVars ++ flatNames.toArray
        let source :=
          match staticStructDirectFieldLocals? resultVar resultTy with
          | some fieldLocals => LocalSource.externalStaticStruct fieldLocals
          | none => LocalSource.value
        visibleLocals := visibleLocals.push { name := resultVar, ty := resultTy, source := source }
      let resultVarTerms := flattenedResultVars.map strTerm
      let stmt ← `(Compiler.CompilationModel.Stmt.tryExternalCallBind
          $successVarTerm
          [ $[$resultVarTerms],* ]
          $(strTerm extName)
          [ $[$argExprs],* ])
      pure (some (stmt, visibleLocals))
  | _ => pure none

/-- Translate `let r ← callResult "name" [args]` into the existing try-call
    lowering while exposing `r.success` and `r.returndata` (or
    `r.returndata0`, `r.returndata1`, ...) as one source-level result value. -/
def callResultBindStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term)
    (resultName : String) : CommandElabM (Option (Term × TypedLocal)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| callResult $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argExprs ← match stripParens args with
        | `(term| [ $[$xs],* ]) =>
            translateLinkedExternalCallArgs fields constDecls immutableDecls params locals xs
        | _ => throwErrorAt args "expected list literal [..]"
      let ext ←
        match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext => pure ext
        | none => throwErrorAt rhs s!"unknown external function '{extName}'"
      for retTy in ext.returnTys do
        unless isSingleWordStaticValueType retTy do
          throwErrorAt rhs
            s!"callResult '{extName}' currently supports only zero or more single-word static return values; got {renderValueType retTy}"
      let successVar := freshSyntheticLocalName s!"{resultName}_success" params locals #[]
      let usedAfterSuccess : Array TypedLocal := locals.push (mkTypedLocal successVar .bool)
      let mut fieldLocals : List (String × String) := [("success", successVar)]
      let mut resultVars : Array String := #[]
      let mut resultFields : List (String × ValueType) := [("success", .bool)]
      match ext.returnTys.toList with
      | [] => pure ()
      | [retTy] =>
          let payloadVar := freshSyntheticLocalName s!"{resultName}_returndata" params usedAfterSuccess #[]
          resultVars := resultVars.push payloadVar
          fieldLocals := fieldLocals ++ [("returndata", payloadVar)]
          resultFields := resultFields ++ [("returndata", retTy)]
      | retTys =>
          let mut indexedLocals := usedAfterSuccess
          for (retTy, idx) in retTys.zipIdx do
            let fieldName := s!"returndata{idx}"
            let payloadVar := freshSyntheticLocalName s!"{resultName}_{fieldName}" params indexedLocals #[]
            indexedLocals := indexedLocals.push (mkTypedLocal payloadVar retTy)
            resultVars := resultVars.push payloadVar
            fieldLocals := fieldLocals ++ [(fieldName, payloadVar)]
            resultFields := resultFields ++ [(fieldName, retTy)]
      let resultVarTerms := resultVars.map strTerm
      let stmt ← `(Compiler.CompilationModel.Stmt.tryExternalCallBind
          $(strTerm successVar)
          [ $[$resultVarTerms],* ]
          $(strTerm extName)
          [ $[$argExprs],* ])
      let resultLocal : TypedLocal :=
        { name := resultName
          ty := .struct "Call.Result" resultFields
          source := .externalStaticStruct fieldLocals }
      pure (some (stmt, resultLocal))
  | _ => pure none

def expectExprList
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Array Term) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      let mut out : Array Term := #[]
      for x in xs do
        match ← translateAbiEncodeProjection? fields constDecls immutableDecls params locals x with
        | some exprs => out := out ++ exprs
        | none => out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
      pure out
  | _ => throwErrorAt stx "expected list literal [..]"

def expectEcmExprList
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Array Term) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      let mut out : Array Term := #[]
      for x in xs do
        match directParamNameWithType? params x with
        | some (name, ty) =>
            if externalCallDynamicArgSupported ty then
              out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_data_offset")))
              out := out.push (← `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_length")))
            else
              match ← translateAbiEncodeProjection? fields constDecls immutableDecls params locals x with
              | some exprs => out := out ++ exprs
              | none => out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
        | none =>
            if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                arrayElementDynamicMemberProjection? params x then
              if externalCallDynamicArgSupported fieldTy then
                  let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
              else
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
            else if let some (paramName, index, fieldTy, _elemTy, wordOffset) :=
                localArrayElementDynamicMemberProjection? locals x then
              if externalCallDynamicArgSupported fieldTy then
                  let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                    $(strTerm paramName)
                    $indexExpr
                    $(natTerm wordOffset)))
              else
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
            else if let some (paramName, fieldTy, wordOffset) :=
                paramDynamicMemberProjection? params x then
              if externalCallDynamicArgSupported fieldTy then
                  out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset
                    $(strTerm paramName)
                    $(natTerm wordOffset)))
                  out := out.push (← `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
                    $(strTerm paramName)
                    $(natTerm wordOffset)))
              else
                out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
            else
              match ← translateAbiEncodeProjection? fields constDecls immutableDecls params locals x with
              | some exprs => out := out ++ exprs
              | none => out := out.push (← translatePureExprWithTypes fields constDecls immutableDecls params locals x)
      pure out
  | _ => throwErrorAt stx "expected list literal [..]"

def translateEmitArgExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Term := do
  if let some (name, _) := localMemoryArray? locals stx then
    `(Compiler.CompilationModel.Expr.memoryArrayLength $(strTerm name))
  else if let some (paramName, index, _fieldTy, _elemTy, wordOffset) :=
      localArrayElementDynamicMemberProjection? locals stx then
    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
    `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
        $(strTerm paramName)
        $indexExpr
        $(natTerm wordOffset))
  else if let some (paramName, index, _fieldTy, _elemTy, wordOffset) :=
      arrayElementDynamicMemberProjection? params stx then
    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
    `(Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
        $(strTerm paramName)
        $indexExpr
        $(natTerm wordOffset))
  else if let some (paramName, _fieldTy, wordOffset) :=
      paramDynamicMemberProjection? params stx then
    `(Compiler.CompilationModel.Expr.paramDynamicMemberLength
        $(strTerm paramName)
        $(natTerm wordOffset))
  else if let some (paramName, _fieldTy, wordOffset) :=
      paramDynamicStaticCompositeProjection? params stx then
    `(Compiler.CompilationModel.Expr.paramDynamicStaticComposite
        $(strTerm paramName)
        $(natTerm wordOffset))
  else
    translatePureExprWithTypes fields constDecls immutableDecls params locals stx

def expectEmitExprList
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Array Term) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      xs.mapM (translateEmitArgExpr fields constDecls immutableDecls params locals)
  | _ => throwErrorAt stx "expected list literal [..]"

def inferEmitArgExprType
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM ValueType := do
  if let some (_, fieldTy, _) := paramDynamicStaticCompositeProjection? params stx then
    pure fieldTy
  else
    inferPureExprType fields constDecls immutableDecls externalDecls params locals stx

def translateBindSource
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM Term := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 | .scalar .int256 | .scalar (.newtype _ .uint256) | .scalar (.adt _ _) =>
          `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; encode as Uint256 and use getStorage"
      | .scalar .address | .scalar (.newtype _ .address) =>
          throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address | .scalar (.newtype _ .address) =>
          `(Compiler.CompilationModel.Expr.storageAddr $(strTerm f.name))
      | .scalar .uint256 | .scalar (.newtype _ .uint256) =>
          throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; use getStorage"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageArrayLength $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Expr.storageArrayLength $(strTerm f.name))
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getStorageArrayElement $field:ident $index:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Expr.storageArrayElement
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index))
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getMapping $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Uint256-keyed; use getMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUint $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUintAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingWord $field:ident $key:term $wordOffset:num) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingWord
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $wordOffset)
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping2
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| getMappingN $field:ident $keys:term) => do
      let f ← lookupStorageField fields (toString field.getId)
      let keyTerms ← expectMappingKeyTerms keys
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size != keyTypes.length then
            throwErrorAt rhs s!"field '{f.name}' expects {keyTypes.length} mapping keys, but getMappingN received {keyTerms.size}"
          let keyExprs ← keyTerms.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Expr.mappingChain
              $(strTerm f.name)
              [ $[$keyExprs],* ])
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
          | _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
          $(strTerm memberName))
  | `(term| msgSender) | `(term| Verity.msgSender) => `(Compiler.CompilationModel.Expr.caller)
  | `(term| msgValue) | `(term| Verity.msgValue) => `(Compiler.CompilationModel.Expr.msgValue)
  | `(term| selfBalance) | `(term| Verity.selfBalance) =>
      `(Compiler.CompilationModel.Expr.selfBalance)
  | `(term| blockTimestamp) | `(term| Verity.blockTimestamp) =>
      `(Compiler.CompilationModel.Expr.blockTimestamp)
  | `(term| blockNumber) | `(term| Verity.blockNumber) =>
      `(Compiler.CompilationModel.Expr.blockNumber)
  | `(term| blobbasefee) | `(term| Verity.blobbasefee) =>
      `(Compiler.CompilationModel.Expr.blobbasefee)
  | `(term| contractAddress) | `(term| Verity.contractAddress) =>
      `(Compiler.CompilationModel.Expr.contractAddress)
  | `(term| txOrigin) | `(term| Verity.txOrigin) =>
      `(Compiler.CompilationModel.Expr.txOrigin)
  | `(term| chainid) | `(term| Verity.chainid) =>
      `(Compiler.CompilationModel.Expr.chainid)
  | `(term| tload $offset:term) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset))
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
      | some (fn, argTerms) =>
          ensureCallableAsInternalHelper rhs fn
          let argExprs ← translateInternalHelperCallArgs
            fields constDecls immutableDecls params locals fn argTerms
          `(Compiler.CompilationModel.Expr.internalCall
              $(strTerm (internalHelperSpecNameFor fn))
              [ $[$argExprs],* ])
      | none =>
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, argTerms) =>
              let argExprs ← argTerms.mapM
                (translatePureExprWithTypes fields constDecls immutableDecls params locals)
              `(Compiler.CompilationModel.Expr.internalCall
                  $(strTerm (qualifiedInternalHelperName functions qualifiedName))
                  [ $[$argExprs],* ])
          | none =>
              throwErrorAt rhs
                "unsupported bind source; expected getStorage/getStorageAddr/getStorageArrayLength/getStorageArrayElement/getMapping/getMappingAddr/getMappingUint/getMappingUintAddr/getMappingWord/getMapping2/getMappingN/structMember/structMember2/msgSender/msgValue/selfBalance/tload/ecrecover, a direct internal helper call, or a qualified library helper call"

def translateSafeRequireBind
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (varName : String)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let narrowBitsOf (term : Term) : CommandElabM Nat := do
    match stripParens term with
    | `(term| $name:ident) =>
        let raw := toString name.getId
        let ty? := lookupTypedLocalType? locals raw <|>
          params.findSome? (fun p => if p.name == raw then some p.ty else none)
        match ty? with
        | some (.uintN bits) => pure bits
        | _ => throwErrorAt term "narrow arithmetic requires a UintN operand"
    | _ => throwErrorAt term "narrow arithmetic currently requires direct UintN operands"
  let translateSafeUintGuardAndValue (optExpr : Term) (label : String) :
      CommandElabM (Term × Term) := do
    match stripParens optExpr with
    | `(term| safeAdd $a:term $b:term) =>
        let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
        let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
        let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
        let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $valueExpr $aExpr)
        pure (guardExpr, valueExpr)
    | `(term| safeSub $a:term $b:term) =>
        let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
        let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
        let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
        let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
        pure (guardExpr, valueExpr)
    | `(term| safeMul $a:term $b:term) =>
        let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
        let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
        let valueExpr : Term ← `(Compiler.CompilationModel.Expr.mul $aExpr $bExpr)
        let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
        let divisorZeroExpr : Term ← `(Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr)
        let quotientExpr : Term ← `(Compiler.CompilationModel.Expr.div $valueExpr $bExpr)
        let noOverflowExpr : Term ← `(Compiler.CompilationModel.Expr.eq $quotientExpr $aExpr)
        let guardExpr : Term ← `(Compiler.CompilationModel.Expr.logicalOr $divisorZeroExpr $noOverflowExpr)
        pure (guardExpr, valueExpr)
    | `(term| safeDiv $a:term $b:term) =>
        let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
        let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
        let valueExpr : Term ← `(Compiler.CompilationModel.Expr.div $aExpr $bExpr)
        let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
        let guardExpr : Term ←
          `(Compiler.CompilationModel.Expr.logicalNot
              (Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr))
        pure (guardExpr, valueExpr)
    | _ =>
        throwErrorAt rhs s!"unsupported {label} source; expected safeAdd, safeSub, safeMul, or safeDiv"
  let rhs := stripParens rhs
  match rhs with
  | `(term| narrowAddPanic $a:term $b:term) =>
      let bits ← narrowBitsOf a
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
      let guardExpr : Term ← `(Compiler.CompilationModel.Expr.lt $valueExpr
        (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits))))
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr "Panic(0x11): narrow arithmetic overflow")),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| narrowSubPanic $a:term $b:term) =>
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
      let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr "Panic(0x11): narrow arithmetic underflow")),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| narrowMulPanic $a:term $b:term) =>
      let bits ← narrowBitsOf a
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.mul $aExpr $bExpr)
      -- Check the mathematical product before evaluating the wrapping EVM `mul`.
      -- Looking only at `valueExpr < 2^bits` is unsound for widths above 128:
      -- a valid pair of narrow operands can overflow 256 bits and wrap to a small
      -- word (for example, `2^128 * 2^128` wraps to zero).
      let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
      let divisorZeroExpr : Term ← `(Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr)
      let maxExpr : Term ←
        `(Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1)))
      let quotientExpr : Term ← `(Compiler.CompilationModel.Expr.div $maxExpr $bExpr)
      let withinWidthExpr : Term ← `(Compiler.CompilationModel.Expr.le $aExpr $quotientExpr)
      let guardExpr : Term ←
        `(Compiler.CompilationModel.Expr.logicalOr $divisorZeroExpr $withinWidthExpr)
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr "Panic(0x11): narrow arithmetic overflow")),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| requireSomeUint $optExpr:term $msg:term) =>
      let msgLit ← strTerm <$> expectStringLiteral msg
      let (guardExpr, valueExpr) ← translateSafeUintGuardAndValue optExpr "requireSomeUint"
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  -- Typed-error counterpart to `requireSomeUint`. The lowering mirrors the
  -- string-message variant exactly, except the guard becomes a
  -- `Stmt.requireError` emitting a 4-byte selector revert with the supplied
  -- error name and argument list.
  | `(term| requireSomeUintError $optExpr:term $errorName:ident($args,*)) =>
      let errorNameLit := strTerm (toString errorName.getId)
      let argExprs ← args.getElems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
      let (guardExpr, valueExpr) ← translateSafeUintGuardAndValue optExpr "requireSomeUintError"
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.requireError $guardExpr $errorNameLit [ $[$argExprs],* ])),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  -- Solidity-0.8 default-revert arithmetic (verity#1752): `let x ← addPanic a b`
  -- lowers to the same IR as
  -- `let x ← requireSomeUint (safeAdd a b) "Panic(0x11): arithmetic overflow"`,
  -- and analogously for `subPanic` / `mulPanic` / `divPanic`. The fixed
  -- message mirrors Solidity 0.8's `Panic(0x11)` (overflow / underflow)
  -- and `Panic(0x12)` (division by zero) opcodes.
  | `(term| addPanic $a:term $b:term) =>
      let msgLit := strTerm "Panic(0x11): arithmetic overflow"
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
      let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $valueExpr $aExpr)
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| subPanic $a:term $b:term) =>
      let msgLit := strTerm "Panic(0x11): arithmetic underflow"
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
      let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| mulPanic $a:term $b:term) =>
      let msgLit := strTerm "Panic(0x11): arithmetic overflow"
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.mul $aExpr $bExpr)
      let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
      let divisorZeroExpr : Term ← `(Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr)
      let quotientExpr : Term ← `(Compiler.CompilationModel.Expr.div $valueExpr $bExpr)
      let noOverflowExpr : Term ← `(Compiler.CompilationModel.Expr.eq $quotientExpr $aExpr)
      let guardExpr : Term ← `(Compiler.CompilationModel.Expr.logicalOr $divisorZeroExpr $noOverflowExpr)
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | `(term| divPanic $a:term $b:term) =>
      let msgLit := strTerm "Panic(0x12): division by zero"
      let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
      let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
      let valueExpr : Term ← `(Compiler.CompilationModel.Expr.div $aExpr $bExpr)
      let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
      let guardExpr : Term ←
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr))
      pure (some #[
        (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
        (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
      ])
  | _ => pure none

def lookupFunctionByNameAndArity
    (functions : Array FunctionDecl)
    (name : String)
    (arity : Nat) : Option FunctionDecl :=
  functions.find? fun fn => fn.name == name && fn.params.size == arity

partial def flattenAppSyntax (stx : Term) : Term × Array Term :=
  let stx := stripParens stx
  match stx.raw with
  | .node _ `Lean.Parser.Term.app appArgs =>
      let head : Term := ⟨appArgs.getD 0 Syntax.missing⟩
      let argTerms := (appArgs.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
      let (head, priorArgs) := flattenAppSyntax head
      (head, priorArgs ++ argTerms)
  | _ => (stx, #[])

partial def typedDotCallSyntax? (stx : Term) : Option (Term × String × Array Term) :=
  let (head, argTerms) := flattenAppSyntax stx
  match head.raw with
  | .ident _ _ raw _ =>
      match nameComponents raw with
      | [targetName, methodName] =>
          let target : Term := mkIdent (Name.mkSimple targetName)
          some (target, methodName, argTerms)
      | _ => none
  | _ => none

partial def resolveTypedInterfaceCall?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (ExternalDecl × Term × Array Term × Option ValueType × Nat)) := do
  let some (target, methodName, argTerms) := typedDotCallSyntax? stx
    | pure none
  let targetName ←
    match stripParens target with
    | `(term| $targetIdent:ident) => pure (toString targetIdent.getId)
    | _ => pure ""
  let some interfaceName := lookupInterfaceName? params locals targetName
    | pure none
  let externalName := interfaceExternalName interfaceName methodName
  let some ext := externalDecls.find? (fun ext => ext.name == externalName)
    | throwErrorAt stx s!"interface '{interfaceName}' has no method '{methodName}'"
  if argTerms.size != ext.params.size then
    throwErrorAt stx s!"interface call '{interfaceName}.{methodName}' expects {ext.params.size} argument(s), got {argTerms.size}"
  for (argTerm, expectedTy) in argTerms.zip ext.params do
    let actualTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals argTerm
    unless actualTy == expectedTy || (isNatLiteralTerm argTerm && numericLiteralCompatibleValueType expectedTy) do
      throwErrorAt argTerm
        s!"interface call '{interfaceName}.{methodName}' argument expects {renderValueType expectedTy}, got {renderValueType actualTy}"
  requireTypedInterfaceStaticParams stx externalName ext.params
  -- the selector is computed from the params only, so a void method's canonical
  -- signature is identical to its non-void counterpart (e.g. aave
  -- `supply(address,uint256,address,uint16)`).
  let selector := Compiler.keccak256_first_4_bytes (interfaceFunctionSignature methodName ext.params)
  match ext.returnTys.toList with
  | [retTy] => pure (some (ext, target, argTerms, some retTy, selector))
  | [] => pure (some (ext, target, argTerms, none, selector))  -- void interface method
  | _ => throwErrorAt stx s!"interface call '{interfaceName}.{methodName}' returns multiple values; typed dot calls currently support one return value"


end Verity.Macro
