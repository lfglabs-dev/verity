import Lean
import Compiler.CompilationModel.Types
import Compiler.ProofStatus
import Verity.Core.Intrinsics

namespace Verity.Macro

open Lean

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

end Verity.Macro
