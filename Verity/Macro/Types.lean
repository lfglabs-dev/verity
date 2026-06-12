import Lean
import Compiler.CompilationModel.Types
import Compiler.ProofStatus
import Verity.Core.Intrinsics

namespace Verity.Macro

open Lean
open Lean.Elab.Command

abbrev Term := TSyntax `term
abbrev Cmd := TSyntax `command
abbrev Ident := TSyntax `ident
abbrev DoSeq := TSyntax `Lean.Parser.Term.doSeq

inductive ValueType where
  | uint256
  | int256
  | uint8
  | uint16
  | address
  | bytes32
  | bool
  | string
  | bytes
  | array (elemTy : ValueType)
  | fixedArray (elemTy : ValueType) (size : Nat)
  | tuple (elemTys : List ValueType)
  | unit
  | newtype (name : String) (baseType : ValueType)  -- Semantic newtype; erased to baseType (#1727 Steps 3b/3c)
  | struct (name : String) (fields : List (String × ValueType)) -- Named ABI tuple with executable field access (#1750)
  | adt (name : String) (maxFields : Nat)  -- User-defined ADT (tagged union); maxFields = max variant field count (#1727 Step 5b)
  deriving Repr, BEq

inductive MappingKeyType where
  | address
  | uint256
  | bytes32
  deriving BEq

structure StructMemberDecl where
  name : String
  ty : ValueType := .uint256
  wordOffset : Nat
  packed : Option (Nat × Nat) := none
  deriving BEq

inductive StorageType where
  | scalar (ty : ValueType)
  | dynamicArray (elemTy : Compiler.CompilationModel.StorageArrayElemType)
  | mappingAddressToUint256
  | mapping2AddressToAddressToUint256
  | mappingUintToUint256
  | mappingChain (keyTypes : List MappingKeyType)
  | mappingStruct (keyType : MappingKeyType) (members : List StructMemberDecl)
  | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMemberDecl)
  deriving BEq

structure StorageFieldDecl where
  ident : Ident
  name : String
  ty : StorageType
  slotNum : Nat
  isTransient : Bool := false
  adtInfo? : Option (String × Nat) := none
  packedBits : Option (Nat × Nat) := none
  emitDef : Bool := true
  aliases : List String := []

inductive StorageAccessorTree where
  | leaf (name : String) (ty : StorageType) (slotNum : Nat)
  | node (name : String) (children : Array StorageAccessorTree)

structure StorageStructAccessorDecl where
  ident : Ident
  name : String
  tree : StorageAccessorTree

/-- The arrow signature of a function-pointer parameter (#1747).
    Recorded only so that good diagnostics are available; the monomorphization
    pre-pass removes every function-pointer parameter before any model/IR
    lowering, so this signature is never lowered to the CompilationModel. -/
structure FuncPtrSig where
  paramTys : Array ValueType
  returnTy : ValueType

structure ParamDecl where
  ident : Ident
  name : String
  ty : ValueType
  interfaceName? : Option String := none
  /-- When `some sig`, this parameter is a higher-order function pointer
      (e.g. `op : (Uint256) -> Uint256`).  The CompilationModel has no
      first-class function values, so such parameters exist only transiently:
      the monomorphization pre-pass (#1747) specializes every call site to a
      concrete internal helper and drops the parameter.  `ty` is set to `.unit`
      as an inert placeholder that must never reach lowering. -/
  funcPtr? : Option FuncPtrSig := none

structure ErrorDecl where
  ident : Ident
  name : String
  params : Array ValueType

structure EventParamDecl where
  ident : Ident
  name : String
  ty : ValueType
  isIndexed : Bool

structure EventDecl where
  ident : Ident
  name : String
  params : Array EventParamDecl

structure ConstantDecl where
  ident : Ident
  name : String
  ty : ValueType
  body : Term

structure ImmutableDecl where
  ident : Ident
  name : String
  ty : ValueType
  body : Term

structure ExternalDecl where
  ident : Ident
  name : String
  params : Array ValueType
  returnTys : Array ValueType
  linkMode : Compiler.CompilationModel.ForeignLinkMode := .objectLinked
  interfaceName? : Option String := none
  isView : Bool := false

/-- A user-defined semantic newtype declared in the `types` section.
    At the language level the type is distinct from its base type; at the
    EVM/Yul level it is erased to the base type (zero overhead).
    (#1727, Axis 1 Step 3a) -/
structure NewtypeDecl where
  ident : Ident
  name : String
  baseType : ValueType

/-- A named ABI struct declared in the `verity_contract` body.
    It elaborates to a Lean `structure` for executable tests, while the compiler
    lowers it as an ABI tuple with named projection support. -/
structure StructDecl where
  ident : Ident
  name : String
  fields : Array ParamDecl

/-- A single variant (constructor) of a user-defined algebraic data type.
    E.g. `| Ok(value : Uint256)` or `| None`.
    (#1727, Axis 1 Step 5a) -/
structure AdtVariantDecl where
  ident : Ident
  name : String
  fields : Array ParamDecl

/-- A user-defined algebraic data type (tagged union) declared in the `inductive` section.
    E.g. `Result := | Ok(value : Uint256) | Err(code : Uint256)`.
    At the EVM level, ADTs use max-width tagged union encoding.
    (#1727, Axis 1 Step 5a) -/
structure AdtDecl where
  ident : Ident
  name : String
  variants : Array AdtVariantDecl

structure LocalObligationDecl where
  ident : Ident
  name : String
  obligation : String
  proofStatus : Compiler.ProofStatus

inductive InitGuardDecl where
  | initializer (fieldIdent : Ident) (fieldName : String)
  | reinitializer (fieldIdent : Ident) (fieldName : String) (version : Nat)

structure FunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTy : ValueType
  isPayable : Bool := false
  isView : Bool := false
  isPure : Bool := false
  isInternal : Bool := false
  noExternalCalls : Bool := false
  /-- When true, the function is annotated `allow_post_interaction_writes` and
      CEI (Checks-Effects-Interactions) enforcement is bypassed.  This is the
      explicit trust-surface opt-out in the escalation ladder (#1728, Axis 2 Step 2a). -/
  allowPostInteractionWrites : Bool := false
  /-- When `some fieldIdent`, the function is annotated `nonreentrant(field)`.
      The named storage field is used as a reentrancy lock.  CEI enforcement is
      bypassed because the lock prevents reentrant state corruption.
      (#1728, Axis 2 Step 2b — known-safe guard rung) -/
  nonReentrantLock : Option Ident := none
  /-- When true, the function is annotated `cei_safe` — the user asserts CEI
      safety via a machine-checked proof obligation.  CEI enforcement is bypassed
      and a proof obligation is generated.
      (#1728, Axis 2 Step 2b — Lean proof rung) -/
  ceiSafe : Bool := false
  /-- When `some fieldIdent`, the function is annotated `requires(field)`.
      The named Address-typed storage field is an access-control role.
      A `require(caller == roleHolder)` check is auto-injected at the start
      of the function body.  (#1728, Axis 2 Step 2c) -/
  requiresRole : Option Ident := none
  initGuard? : Option InitGuardDecl := none
  /-- Storage field names declared via `modifies(field1, field2)`.
      When non-empty, the compiler validates that the function body only
      writes to fields in this set and auto-generates a `_frame` theorem. -/
  modifies : Array Ident := #[]
  localObligations : Array LocalObligationDecl := #[]
  modifiers : Array Ident := #[]
  body : Term

structure InterfaceFunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTys : Array ValueType
  isView : Bool := false

structure InterfaceDecl where
  ident : Ident
  name : String
  functions : Array InterfaceFunctionDecl

structure ModifierDecl where
  ident : Ident
  name : String
  body : Term

structure ConstructorDecl where
  params : Array ParamDecl
  isPayable : Bool := false
  localObligations : Array LocalObligationDecl := #[]
  body : Term

def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩

def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

partial def expectTermListLiteral (stx : Term) : CommandElabM (Array Term) := do
  match stx with
  | `(term| [ $[$xs],* ]) => pure xs
  | `(term| ($inner:term)) => expectTermListLiteral inner
  | _ => throwErrorAt stx "expected list literal [..]"

partial def collectTupleElems (stx : Syntax) : Array Syntax :=
  if stx.isAtom then
    #[]
  else if stx.getKind == `null then
    stx.getArgs.foldl (fun acc child => acc ++ collectTupleElems child) #[]
  else
    #[stx]

def tupleElemsFromSyntax? (stx : Syntax) : Option (Array Syntax) :=
  if stx.getKind == `Lean.Parser.Term.tuple then
    some (collectTupleElems stx[1])
  else
    none

partial def expectMappingKeyTerms (stx : Term) : CommandElabM (Array Term) := do
  expectTermListLiteral stx

partial def collectArrowChainTypes (stx : Term) : CommandElabM (List Term × Term) := do
  match stx with
  | `(term| $lhs:term → $rhs:term) =>
      let (rest, resultTy) ← collectArrowChainTypes rhs
      pure (lhs :: rest, resultTy)
  | _ => pure ([], stx)

def natFromSyntax (stx : Syntax) : CommandElabM Nat :=
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural literal"

partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(term| ($inner)) => stripParens inner
  | _ => stx

def structValueTypeFields (decl : StructDecl) : List (String × ValueType) :=
  decl.fields.toList.map fun field => (field.name, field.ty)

partial def valueTypeFromSyntax
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (ty : Term) : CommandElabM ValueType := do
  let ty := stripParens ty
  let (arrowArgs, _arrowResult) ← collectArrowChainTypes ty
  if !arrowArgs.isEmpty then
    throwErrorAt ty
      "unsupported function type in verity_contract boundary (#1747); internal function-pointer parameters are not first-class in the CompilationModel yet. Pass an explicit mode/enum and dispatch to direct internal helper calls, or inline the helper call at each call site."
  match ty with
  | `(term| Uint256) => pure .uint256
  | `(term| Int256) => pure .int256
  | `(term| Uint8) => pure .uint8
  | `(term| Uint16) => pure .uint16
  | `(term| Address) => pure .address
  | `(term| Bytes32) => pure .bytes32
  | `(term| Bool) => pure .bool
  | `(term| String) => pure .string
  | `(term| Bytes) => pure .bytes
  | `(term| Array $elemTy:term) =>
      let elem ← valueTypeFromSyntax newtypes structDecls adtDecls elemTy
      match elem with
      | .unit => throwErrorAt ty "unsupported type '{ty}'; Array Unit is not allowed"
      | .array _ => throwErrorAt ty "unsupported type '{ty}'; nested arrays are not supported"
      | _ => pure (.array elem)
  | `(term| FixedArray $elemTy:term $size:num) =>
      let elem ← valueTypeFromSyntax newtypes structDecls adtDecls elemTy
      let n ← natFromSyntax size
      match elem with
      | .unit => throwErrorAt ty "unsupported type '{ty}'; FixedArray Unit is not allowed"
      | .array _ => throwErrorAt ty "unsupported type '{ty}'; FixedArray of dynamic Array is not supported"
      | _ => pure (.fixedArray elem n)
  | `(term| Tuple [ $[$elemTys:term],* ]) =>
      let elems ← elemTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      if elems.size < 2 then
        throwErrorAt ty "tuple types must have at least 2 elements"
      pure (.tuple elems.toList)
  | `(term| Unit) => pure .unit
  | `(term| $id:ident) =>
      let tyName := toString id.getId
      -- Try resolving as a user-defined newtype (#1727, Axis 1 Steps 3a/3b)
      match newtypes.find? (fun nt => nt.name == tyName) with
      | some nt => pure (.newtype nt.name nt.baseType)
      | none =>
        -- Try resolving as a user-defined ADT (#1727, Axis 1 Step 5b)
        match structDecls.find? (fun s => s.name == tyName) with
        | some decl => pure (.struct decl.name (structValueTypeFields decl))
        | none =>
          match adtDecls.find? (fun a => a.name == tyName) with
          | some decl =>
              let maxFields := decl.variants.foldl (fun acc v => max acc v.fields.size) 0
              pure (.adt decl.name maxFields)
          | none => throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Int256, Uint8, Uint16, Address, Bytes32, Bool, String, Bytes, Array <type>, FixedArray <type> <size>, Tuple [...], Unit, a user-defined struct, or a user-defined type from the `types` or `inductive` section"
  | _ =>
      throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Int256, Uint8, Uint16, Address, Bytes32, Bool, String, Bytes, Array <type>, FixedArray <type> <size>, Tuple [...], Unit, a user-defined struct, or a user-defined type from the `types` or `inductive` section"

end Verity.Macro
