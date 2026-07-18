/-
  Compiler.CompilationModel: Declarative Compilation Model DSL

  This module defines a declarative way to model contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management

  Features:
  - Storage fields with automatic slot assignment (uint256, address, mapping)
  - Flexible mapping types: Address→Uint256, Uint256→Uint256, nested mappings (#154)
  - Functions with automatic selector computation
  - Guards and access control patterns
  - If/else branching and bounded loops (#179)
  - Array/bytes parameter types and dynamic calldata (#180)
  - Internal function composition (#181)
  - Event emission (#153)
  - Verified external library integration (#184)
-/

import Verity.Core.Model.Constants
import Verity.Core.Model.CodeData
import Verity.Core.Model.ECM
import Verity.Core.Model.ProofStatus
import Verity.Core.Model.Yul.Ast
import Verity.Core.Model.Identifier
import Verity.Core.Intrinsics

namespace Compiler.CompilationModel

export Compiler.Constants (errorStringSelectorWord addressMask selectorShift freeMemoryPointer)

open Compiler
open Compiler.Yul

def builtinExpName : String := "__verity_builtin_exp"

/-!
## Compilation Model DSL

Instead of manually writing IR, contracts provide a high-level model:
- Storage fields with automatic slot assignment
- Functions with automatic selector computation
- Guards and access control patterns
- Control flow: if/else branching, bounded loops
- Array parameters and dynamic calldata
- Internal function calls for modular composition
- Event emission for standards compliance
-/

/-!
### Mapping Key Types (#154)

Support flexible mapping types: single-key, double-key (nested), and uint256 keys.
-/

inductive MappingKeyType
  | address    -- mapping(address => ...)
  | uint256    -- mapping(uint256 => ...)
  | bytes32    -- mapping(bytes32 => ...)
  deriving Repr, BEq

inductive MappingType
  | simple (keyType : MappingKeyType)                          -- mapping(K => uint256)
  | nested (outerKey : MappingKeyType) (innerKey : MappingKeyType)  -- mapping(K1 => mapping(K2 => uint256))
  | chain (keyTypes : List MappingKeyType)                     -- mapping(K1 => ... => mapping(Kn => uint256))
  deriving Repr, BEq

structure PackedBits where
  /-- Least-significant bit offset within the 256-bit storage word. -/
  offset : Nat
  /-- Bit width of this packed subfield. -/
  width : Nat
  deriving Repr, BEq

inductive StructMemberType
  | uint256
  | uint16
  | address
  | bool
  | bytes32
  deriving Repr, BEq

/-- A named member within a struct-valued mapping.
    Each member occupies a specific word within the struct's storage region,
    and may optionally be packed into a subregion of that word. -/
structure StructMember where
  /-- The member name (used in `Expr.structMember` / `Stmt.setStructMember`). -/
  name : String
  /-- Solidity surface type of the packed/full-word member. -/
  ty : StructMemberType := StructMemberType.uint256
  /-- Zero-based word offset from the struct's base slot. -/
  wordOffset : Nat
  /-- Optional packed subfield within the word. When `none`, the member occupies
      the full 256-bit word. -/
  packed : Option PackedBits := none
  deriving Repr, BEq

inductive StorageArrayElemType
  | uint256
  | address
  | bool
  | uint8
  | bytes32
  deriving Repr, BEq

def storageArrayElemUsesOneStorageWord : StorageArrayElemType → Bool
  | .uint256 | .address | .bool | .bytes32 => true
  | .uint8 => false

inductive FieldType
  | uint256
  | address
  /-- Storage-backed tagged union: tag at the canonical slot followed by
      `maxFields` payload slots. -/
  | adt (name : String) (maxFields : Nat)
  | dynamicArray (elemType : StorageArrayElemType)
  | mappingTyped (mt : MappingType)  -- Flexible mapping types (#154)
  /-- A mapping whose value is a multi-word struct with named members.
      `mappingStruct keyType members` defines `mapping(K => Struct)` where
      `Struct` spans `members.map (·.wordOffset) |>.maximum + 1` words.
      Access members via `Expr.structMember` / `Stmt.setStructMember`. -/
  | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
  /-- A nested mapping whose inner value is a multi-word struct with named members.
      `mappingStruct2 outerKey innerKey members` defines
      `mapping(K1 => mapping(K2 => Struct))`.
      Access members via `Expr.structMember2` / `Stmt.setStructMember2`. -/
  | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMember)
  deriving Repr, BEq

structure Field where
  name : String
  ty : FieldType
  /-- Use EIP-1153 transient storage (`TLOAD`/`TSTORE`) for this field.
      Transient fields share the storage field typing and slot discipline, but
      their values are transaction-scoped in `ContractState.transientStorage`. -/
  isTransient : Bool := false
  /-- Optional explicit storage slot override.
      When omitted, the slot defaults to declaration order (legacy behavior). -/
  slot : Option Nat := none
  /-- Optional packed subfield placement within the storage word.
      When present, reads/writes are masked and shifted to this bit range. -/
  packedBits : Option PackedBits := none
  /-- Optional compatibility mirror-write slots.
      Writes to this field also write the same value to each alias slot. -/
  aliasSlots : List Nat := []
  deriving Repr

/-- Contract-level access-control role declaration shape.
    `scalarAddress` models owner/admin-style roles stored as a single address.
    `mappingAddressToUint256` models minter/relayer-style role membership maps
    whose nonzero value grants the role. -/
inductive RoleKind where
  | scalarAddress
  | mappingAddressToUint256
  deriving Repr, BEq

/-- Explicit role declaration used by generated access-control theorems and
    reports. The `field` is the storage field backing this semantic role. -/
structure RoleDecl where
  name : String
  field : String
  kind : RoleKind
  deriving Repr, BEq

structure ReservedSlotRange where
  /-- Inclusive start slot of a reserved storage interval. -/
  start : Nat
  /-- Inclusive end slot of a reserved storage interval. -/
  end_ : Nat
  deriving Repr, BEq

structure SlotAliasRange where
  /-- Inclusive start slot for canonical source slots. -/
  sourceStart : Nat
  /-- Inclusive end slot for canonical source slots. -/
  sourceEnd : Nat
  /-- Alias slot corresponding to sourceStart (sourceStart + i maps to targetStart + i). -/
  targetStart : Nat
  deriving Repr, BEq

/-!
### Parameter Types (#180)

Extended parameter types supporting arrays, bytes, and bytes32.
-/

inductive ParamType
  | uint256
  | int256
  | uint8
  | uint16
  | address
  | bool                                   -- Solidity bool (ABI-encoded as 32-byte 0/1)
  | bytes32                                -- Fixed 32-byte value
  | string                                 -- Dynamic UTF-8 string (ABI-compatible with bytes)
  | tuple (elemTypes : List ParamType)     -- ABI tuple
  | array (elemType : ParamType)           -- Dynamic array: uint256[], address[]
  | fixedArray (elemType : ParamType) (size : Nat)  -- Fixed array: uint256[3]
  | bytes                                  -- Dynamic bytes
  | adt (name : String) (maxFields : Nat)  -- User-defined ADT; maxFields = max variant field count (#1727 Steps 5b/5e)
  | newtypeOf (name : String) (baseType : ParamType)  -- Semantic newtype; erased to baseType at Yul level (zero overhead) (#1727 Steps 3b/3c)
  deriving Repr, BEq

structure Param where
  name : String
  ty : ParamType
  deriving Repr, BEq

-- Convert to IR types
/-!
### Event Definitions (#153)

Events for ERC20/ERC721 compliance and general logging.
-/

inductive EventParamKind
  | indexed     -- Goes into LOG topic (max 3 indexed params per event)
  | unindexed   -- Goes into LOG data
  deriving Repr, BEq

structure EventParam where
  name : String
  ty : ParamType
  kind : EventParamKind
  deriving Repr

structure EventDef where
  name : String
  params : List EventParam
  deriving Repr

structure ErrorDef where
  name : String
  params : List ParamType
  deriving Repr

/-!
### External Function Declarations (#184)

Verified external library integration with axiom documentation.
-/

inductive ForeignLinkMode where
  /-- The dependency remains an ABI boundary and is called through an adapter
      that preserves Solidity-compatible returndata and revert behavior. -/
  | external
  /-- The dependency is provided as Yul/EVM object code and linked into the
      generated artifact at compile time. -/
  | objectLinked
  /-- The dependency is a small pure helper whose body may be inlined by the
      frontend/backend. The compiler still treats it as a declared foreign
      surface for audit visibility. -/
  | inline
  /-- The dependency is owned by the compiler runtime rather than by a protocol
      deployment boundary. -/
  | compilerRuntime
  deriving Repr, BEq

def ForeignLinkMode.toJsonString : ForeignLinkMode → String
  | .external => "external"
  | .objectLinked => "objectLinked"
  | .inline => "inline"
  | .compilerRuntime => "compilerRuntime"

def ForeignLinkMode.humanName : ForeignLinkMode → String
  | .external => "external ABI boundary"
  | .objectLinked => "object-linked Yul"
  | .inline => "inline helper"
  | .compilerRuntime => "compiler runtime"

structure ExternalFunction where
  name : String
  params : List ParamType
  returnType : Option ParamType := none  -- backward compatibility
  returns : List ParamType := []  -- empty for void functions
  /-- Proof-accounting status for this foreign surface.
      `proved` means there is an end-to-end refinement theorem,
      `assumed` means downstream proofs must quantify over the spec explicitly,
      and `unchecked` means the function is available for compilation/testing only. -/
  proofStatus : Compiler.ProofStatus := .assumed
  /-- Names of axioms assumed about this function.
      The actual Lean propositions are stated separately;
      these names are for documentation and audit purposes. -/
  axiomNames : List String
  /-- How the foreign surface is linked into the generated artifact.  Historical
      `linked_externals` declarations default to object-linked Yul because the
      compiler emits a Yul function call and the driver injects matching helper
      definitions from `--link` libraries. -/
  linkMode : ForeignLinkMode := .objectLinked
  deriving Repr

structure YulState where
  vars : List (String × Nat) := []
  memory : Nat → Nat := fun _ => 0
  storage : Nat → Nat := fun _ => 0
  transientStorage : Nat → Nat := fun _ => 0
  returndata : List Nat := []
  reverted : Bool := false

structure FrameSpec where
  localReads : List String := []
  localWrites : List String := []
  memoryReads : List String := []
  memoryWrites : List String := []
  storageReads : List String := []
  storageWrites : List String := []
  transientReads : List String := []
  transientWrites : List String := []
  deriving Repr, BEq, Inhabited

/-- Structured refinement contract for localized unsafe Yul boundaries.
    The predicates give proof code a real target while `summary` remains the
    stable human-readable report text. -/
structure UnsafeYulContract where
  name : String
  summary : String
  pre : YulState → Prop
  post : YulState → YulState → Prop
  frame : FrameSpec := {}

instance : Repr UnsafeYulContract where
  reprPrec contract prec :=
    reprPrec (contract.name, contract.summary, contract.frame) prec

namespace UnsafeYulContract

def rawRevert (name summary : String) : UnsafeYulContract :=
  { name := name
    summary := summary
    pre := fun _ => True
    post := fun _ after => after.reverted = true
    frame := { memoryReads := ["revertPayload"] } }

end UnsafeYulContract

structure LocalObligation where
  name : String
  /-- User-supplied summary of the local refinement contract that must hold
      for this localized unsafe/assembly boundary. -/
  obligation : String
  /-- Proof-accounting status for this local boundary. -/
  proofStatus : Compiler.ProofStatus := .assumed
  deriving Repr

/-- Coarse statement termination classification used by generic statement
    metadata. `mayTerminate` covers handwritten/raw Yul fragments unless a
    caller supplies a more precise contract. -/
inductive StmtTermination where
  | fallsThrough
  | alwaysTerminates
  | mayTerminate
  deriving Repr, BEq

/-- Finer control-flow summary for statements and statement lists.
    This intentionally coexists with `StmtTermination` while callers migrate:
    the old field answers the coarse "can execution continue?" question, while
    this summary records which terminal behaviors may occur. -/
structure ControlFlowSummary where
  mayFallThrough : Bool := true
  mayRevert : Bool := false
  mayReturn : Bool := false
  mayStop : Bool := false
  deriving Repr, BEq, Inhabited

namespace ControlFlowSummary

def fallsThrough : ControlFlowSummary := {}

/-- Empty control-flow set, used as the identity when unioning alternatives. -/
def noPaths : ControlFlowSummary :=
  { mayFallThrough := false, mayRevert := false, mayReturn := false, mayStop := false }

def mayReverting : ControlFlowSummary :=
  { mayFallThrough := true, mayRevert := true }

def reverts : ControlFlowSummary :=
  { mayFallThrough := false, mayRevert := true }

def returns : ControlFlowSummary :=
  { mayFallThrough := false, mayReturn := true }

def stops : ControlFlowSummary :=
  { mayFallThrough := false, mayStop := true }

def unknown : ControlFlowSummary :=
  { mayFallThrough := true, mayRevert := true, mayReturn := true, mayStop := true }

def union (a b : ControlFlowSummary) : ControlFlowSummary :=
  { mayFallThrough := a.mayFallThrough || b.mayFallThrough
    mayRevert := a.mayRevert || b.mayRevert
    mayReturn := a.mayReturn || b.mayReturn
    mayStop := a.mayStop || b.mayStop }

/-- Sequential composition: `b` is reachable only along fall-through paths of `a`. -/
def seq (a b : ControlFlowSummary) : ControlFlowSummary :=
  { mayFallThrough := a.mayFallThrough && b.mayFallThrough
    mayRevert := a.mayRevert || (a.mayFallThrough && b.mayRevert)
    mayReturn := a.mayReturn || (a.mayFallThrough && b.mayReturn)
    mayStop := a.mayStop || (a.mayFallThrough && b.mayStop) }

/-- True when every path terminates specifically through a Solidity-style
return or revert. A raw `stop` also halts execution, but it does not produce the
return data required by functions that declare return values. -/
def alwaysReturnsOrReverts (cf : ControlFlowSummary) : Bool :=
  !cf.mayFallThrough && !cf.mayStop && (cf.mayReturn || cf.mayRevert)

def fromTermination : StmtTermination → ControlFlowSummary
  | .fallsThrough => fallsThrough
  | .alwaysTerminates => unknown
  | .mayTerminate => unknown

end ControlFlowSummary

/-- Scope effects exposed by the generic statement metadata layer. -/
structure StmtScopeEffects where
  bindNames : List String := []
  assignNames : List String := []
  storageWrites : List String := []
  deriving Repr, Inhabited

namespace StmtScopeEffects

def merge (a b : StmtScopeEffects) : StmtScopeEffects :=
  { bindNames := a.bindNames ++ b.bindNames
    assignNames := a.assignNames ++ b.assignNames
    storageWrites := a.storageWrites ++ b.storageWrites }

end StmtScopeEffects

mutual
/-- Conservative scan for storage-like writes inside raw Yul expressions.
    Transient `tstore` is intentionally classified as a storage write for
    effect validation because it mutates EVM transaction-local state. -/
partial def yulExprWritesStorage : YulExpr → Bool
  | .call func args =>
      func == "sstore" || func == "tstore" || yulExprListWritesStorage args
  | _ => false

partial def yulExprListWritesStorage : List YulExpr → Bool
  | [] => false
  | expr :: rest =>
      yulExprWritesStorage expr || yulExprListWritesStorage rest
end

mutual
/-- Conservative scope/effect derivation for embedded Yul AST fragments.
    This is the single source of truth used by both imported-Yul construction
    and unsafe-Yul validation, so generated declarations and validation checks
    cannot drift apart. -/
partial def yulStmtScopeEffects : YulStmt → StmtScopeEffects
  | .comment _ | .leave =>
      {}
  | .let_ name value =>
      { bindNames := [name]
        storageWrites := if yulExprWritesStorage value then ["<raw-yul-storage-write>"] else [] }
  | .letMany names value =>
      { bindNames := names
        storageWrites := if yulExprWritesStorage value then ["<raw-yul-storage-write>"] else [] }
  | .assign name value =>
      { assignNames := [name]
        storageWrites := if yulExprWritesStorage value then ["<raw-yul-storage-write>"] else [] }
  | .exprStmt expr =>
      { storageWrites := if yulExprWritesStorage expr then ["<raw-yul-storage-write>"] else [] }
  | .if_ cond body =>
      let bodyEffects := yulStmtListScopeEffects body
      { bodyEffects with
        storageWrites :=
          (if yulExprWritesStorage cond then ["<raw-yul-storage-write>"] else []) ++
            bodyEffects.storageWrites }
  | .for_ init cond post body =>
      let initEffects := yulStmtListScopeEffects init
      let postEffects := yulStmtListScopeEffects post
      let bodyEffects := yulStmtListScopeEffects body
      { bindNames := initEffects.bindNames ++ postEffects.bindNames ++ bodyEffects.bindNames
        assignNames := initEffects.assignNames ++ postEffects.assignNames ++ bodyEffects.assignNames
        storageWrites :=
          initEffects.storageWrites ++
          (if yulExprWritesStorage cond then ["<raw-yul-storage-write>"] else []) ++
          postEffects.storageWrites ++ bodyEffects.storageWrites }
  | .switch expr cases default =>
      let casesEffects :=
        cases.foldl
          (fun acc (_, body) => StmtScopeEffects.merge acc (yulStmtListScopeEffects body))
          ({} : StmtScopeEffects)
      let defaultEffects :=
        match default with
        | none => ({} : StmtScopeEffects)
        | some body => yulStmtListScopeEffects body
      { bindNames := casesEffects.bindNames ++ defaultEffects.bindNames
        assignNames := casesEffects.assignNames ++ defaultEffects.assignNames
        storageWrites :=
          (if yulExprWritesStorage expr then ["<raw-yul-storage-write>"] else []) ++
          casesEffects.storageWrites ++ defaultEffects.storageWrites }
  | .block stmts =>
      yulStmtListScopeEffects stmts
  | .funcDef name _params _rets body =>
      let bodyEffects := yulStmtListScopeEffects body
      { bindNames := [name]
        assignNames := []
        storageWrites := bodyEffects.storageWrites }

partial def yulStmtListScopeEffects : List YulStmt → StmtScopeEffects
  | [] => {}
  | stmt :: rest =>
      StmtScopeEffects.merge (yulStmtScopeEffects stmt) (yulStmtListScopeEffects rest)
end

mutual
/-- Conservative scan for EVM external-call builtins inside raw Yul ASTs.
    Unsafe-Yul fragments also declare mechanics metadata, but validation should
    not miss a handwritten `call`/`staticcall`/`delegatecall` if the metadata is
    under-declared. -/
partial def yulExprContainsExternalCall : YulExpr → Bool
  | .call func args =>
      func == "call" ||
        func == "staticcall" ||
        func == "delegatecall" ||
        yulExprListContainsExternalCall args
  | _ => false

partial def yulExprListContainsExternalCall : List YulExpr → Bool
  | [] => false
  | expr :: rest =>
      yulExprContainsExternalCall expr || yulExprListContainsExternalCall rest

partial def yulStmtContainsExternalCall : YulStmt → Bool
  | .comment _ | .leave =>
      false
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      yulExprContainsExternalCall value
  | .if_ cond body =>
      yulExprContainsExternalCall cond || yulStmtListContainsExternalCall body
  | .for_ init cond post body =>
      yulStmtListContainsExternalCall init ||
        yulExprContainsExternalCall cond ||
        yulStmtListContainsExternalCall post ||
        yulStmtListContainsExternalCall body
  | .switch discr cases default =>
      yulExprContainsExternalCall discr ||
        cases.any (fun (_, body) => yulStmtListContainsExternalCall body) ||
        match default with
        | none => false
        | some body => yulStmtListContainsExternalCall body
  | .block stmts =>
      yulStmtListContainsExternalCall stmts
  | .funcDef _ _ _ body =>
      yulStmtListContainsExternalCall body

partial def yulStmtListContainsExternalCall : List YulStmt → Bool
  | [] => false
  | stmt :: rest =>
      yulStmtContainsExternalCall stmt || yulStmtListContainsExternalCall rest
end

/-- Typed trust-report mechanics emitted by low-level statements and raw Yul fragments.
    JSON and human-readable reports still render these through `toReportString`,
    preserving the existing public report format while keeping the model boundary
    from depending on ad-hoc string literals. -/
inductive LowLevelMechanic where
  | call
  | staticcall
  | delegatecall
  | returndataSize
  | returndataCopy
  | revertReturndata
  | rawRevert
  | returndataOptionalBoolAt
  | blobbasefee
  | mload
  | mstore
  | calldataload
  | calldatacopy
  | codecopy
  | extcodesize
  | extcodecopy
  | create2
  | tload
  | tstore
  | rawLog
  | contractAddress
  | txOrigin
  | chainid
  | selfBalance
  | blockNumber
  | storageWrite
  deriving Repr, BEq, Inhabited

namespace LowLevelMechanic

def toReportString : LowLevelMechanic → String
  | .call => "call"
  | .staticcall => "staticcall"
  | .delegatecall => "delegatecall"
  | .returndataSize => "returndataSize"
  | .returndataCopy => "returndataCopy"
  | .revertReturndata => "revertReturndata"
  | .rawRevert => "rawRevert"
  | .returndataOptionalBoolAt => "returndataOptionalBoolAt"
  | .blobbasefee => "blobbasefee"
  | .mload => "mload"
  | .mstore => "mstore"
  | .calldataload => "calldataload"
  | .calldatacopy => "calldatacopy"
  | .codecopy => "codecopy"
  | .extcodesize => "extcodesize"
  | .extcodecopy => "extcodecopy"
  | .create2 => "create2"
  | .tload => "tload"
  | .tstore => "tstore"
  | .rawLog => "rawLog"
  | .contractAddress => "contractAddress"
  | .txOrigin => "txOrigin"
  | .chainid => "chainid"
  | .selfBalance => "selfBalance"
  | .blockNumber => "blockNumber"
  | .storageWrite => "storageWrite"

instance : ToString LowLevelMechanic where
  toString := toReportString

end LowLevelMechanic

/-- Typed handwritten Yul fragment. This is intentionally not just a string:
    callers provide an EVMYul AST payload plus explicit proof obligations and
    trust-surface metadata at the same boundary where the raw fragment enters
    the compilation model. -/
structure UnsafeYulFragment where
  label : String
  stmts : List YulStmt
  obligations : List LocalObligation
  contracts : List UnsafeYulContract := []
  mechanics : List LowLevelMechanic := []
  scopeEffects : StmtScopeEffects := {}
  termination : StmtTermination := .mayTerminate
  controlFlow : ControlFlowSummary := .unknown
  deriving Repr

/-- Backwards-friendly name for explicitly trusted raw Yul fragments. -/
abbrev RawYul := UnsafeYulFragment

namespace UnsafeYulFragment

/-- Helper constructor for the single Yul `revert(offset, size)` instruction.

    Prefer this through `Stmt.unsafeYul` for one-off raw instruction escapes.
    Stable typed primitives such as `Stmt.mstore` and `Stmt.calldatacopy`
    remain first-class statements because Verity has explicit semantics and
    proof/audit surfaces for them; ad-hoc raw instructions should carry their
    trust metadata at the `UnsafeYulFragment` boundary instead of growing `Stmt`.
    Raw memory reverts are intentionally modeled as unsafe Yul fragments rather
    than first-class `Stmt` constructors. -/
def rawRevert (offset size : YulExpr) (obligation : LocalObligation)
    (label : String := obligation.name) : UnsafeYulFragment := {
  label := label
  stmts := [YulStmt.exprStmt (YulExpr.call "revert" [offset, size])]
  obligations := [obligation]
  contracts := [UnsafeYulContract.rawRevert obligation.name obligation.obligation]
  mechanics := [.rawRevert]
  termination := .alwaysTerminates
  controlFlow := .reverts
}

end UnsafeYulFragment

/-!
### ADT Type Definitions (#1727, Phase 5 Step 5b)

IR-level representation of user-defined algebraic data types (tagged unions).
Each variant carries a tag byte and typed fields.
-/

/-- A single variant of an ADT at the IR level.
    `tag` is the 0-based index used for storage encoding. -/
structure AdtVariant where
  name : String
  tag : Nat
  fields : List Param
  deriving Repr, BEq

/-- A user-defined algebraic data type at the IR level.
    Storage layout: tag byte (1 slot) + max-width fields in consecutive slots. -/
structure AdtTypeDef where
  name : String
  variants : List AdtVariant
  deriving Repr, BEq

/-!
## Function Body DSL

DSL for expressing contract operations including control flow,
internal calls, and event emission.
-/

inductive Expr
  | literal (n : Nat)
  | param (name : String)
  | constructorArg (index : Nat)  -- Access constructor argument (loaded from bytecode)
  | immutable (name : String)
  | storage (field : String)
  | storageAddr (field : String)
  | mapping (field : String) (key : Expr)
  | mappingWord (field : String) (key : Expr) (wordOffset : Nat)  -- mappingSlot(base,key) + wordOffset
  | mappingPackedWord (field : String) (key : Expr) (wordOffset : Nat) (packed : PackedBits)
  | mapping2 (field : String) (key1 key2 : Expr)  -- Double mapping (#154)
  | mapping2Word (field : String) (key1 key2 : Expr) (wordOffset : Nat)  -- Double mapping + word offset
  | mappingUint (field : String) (key : Expr)  -- Uint256-keyed mapping (#154)
  | mappingChain (field : String) (keys : List Expr)  -- Arbitrary-depth mapping read (#1570)
  /-- Read a named member of a struct-valued mapping.
      Resolves the member's word offset and optional packed bits at compile time.
      `structMember field key memberName` compiles to the same Yul as
      `mappingPackedWord field key member.wordOffset member.packed` (or
      `mappingWord` when unpacked). -/
  | structMember (field : String) (key : Expr) (memberName : String)
  /-- Read a named member of a struct-valued double mapping.
      `structMember2 field key1 key2 memberName` resolves the member's word offset
      and packed bits from the field's struct definition. -/
  | structMember2 (field : String) (key1 key2 : Expr) (memberName : String)
  | caller
  | contractAddress
  /-- `tx.origin` — the EOA at the root of the call chain.  Lowers to
      the EVM `origin()` opcode.  Distinct from `caller` whenever the
      call passes through a contract intermediary. -/
  | txOrigin
  | chainid
  | msgValue
  | selfBalance
  | blockTimestamp
  | blockNumber
  | blobbasefee
  | mload (offset : Expr)
  | tload (offset : Expr)
  | keccak256 (offset size : Expr)
  /-- First-class low-level `call(gas, target, value, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | call (gas target value inOffset inSize outOffset outSize : Expr)
  /-- First-class low-level `staticcall(gas, target, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | staticcall (gas target inOffset inSize outOffset outSize : Expr)
  /-- First-class low-level `delegatecall(gas, target, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | delegatecall (gas target inOffset inSize outOffset outSize : Expr)
  /-- Size in bytes of the current call's calldata (`calldatasize()`). -/
  | calldatasize
  /-- Load a 32-byte word from calldata at the given byte offset (`calldataload(offset)`). -/
  | calldataload (offset : Expr)
  /-- Size in bytes of returndata from the most recent external call frame. -/
  | returndataSize
  /-- Size in bytes of code deployed at the given address (0 for EOAs). -/
  | extcodesize (addr : Expr)
  /-- ERC20-style optional bool return helper:
      true iff `returndatasize() == 0 || (returndatasize() == 32 && mload(outOffset) == 1)`. -/
  | returndataOptionalBoolAt (outOffset : Expr)
  | localVar (name : String)  -- Reference to local variable
  | externalCall (name : String) (args : List Expr)  -- External function call (linked at compile time)
  | internalCall (functionName : String) (args : List Expr)  -- Internal function call (#181)
  | arrayLength (name : String)  -- Length of a dynamic array parameter (#180)
  | arrayElement (name : String) (index : Expr)  -- Checked element access of a dynamic array parameter (revert on out-of-range) (#180)
  /-- Length of a memory-backed dynamic array binding, e.g. an internal helper
      returning `(data_offset, length)`. -/
  | memoryArrayLength (name : String)
  /-- Checked element access for a memory-backed dynamic array binding with
      single-word static elements. -/
  | memoryArrayElement (name : String) (index : Expr)
  /-- Checked word access inside a dynamic array element.  `elementWords` is the
      static ABI word width of one element and `wordOffset` is the word inside
      that element.  This supports arrays of static tuple/struct-like values. -/
  | arrayElementWord (name : String) (index : Expr) (elementWords wordOffset : Nat)
  /-- Checked word access inside the head of a dynamically-sized array element.
      This supports arrays of tuple/struct-like values whose element contains
      nested dynamic members; `wordOffset` indexes the element head after the
      ABI element offset has been resolved. -/
  | arrayElementDynamicWord (name : String) (index : Expr) (wordOffset : Nat)
  /-- Data offset of a dynamically-sized array element.  Given an array
      parameter whose elements are dynamically encoded tuples/structs,
      bounds-checks `index`, resolves the element offset table entry, and
      returns the element head offset.  This is the dynamic-tuple analogue of
      forwarding `(arrayElement <param> <i>)` into an internal helper. -/
  | arrayElementDynamicDataOffset (name : String) (index : Expr)
  /-- Checked word access inside the head of a directly-passed struct/tuple
      parameter whose ABI encoding is dynamic.  `wordOffset` indexes the
      parameter's head section after the outer offset pointer has been
      resolved by the parameter loader.  Used for `param.field` projections
      where `param` is a struct that carries nested dynamic members and the
      projected field is a single-word static leaf at a fixed head offset.
      (verity#1832) -/
  | paramDynamicHeadWord (name : String) (wordOffset : Nat)
  /-- Length of a dynamic member inside a directly-passed dynamic tuple
      parameter.  `wordOffset` points at the member's ABI head word relative to
      `{name}_data_offset`. -/
  | paramDynamicMemberLength (name : String) (wordOffset : Nat)
  /-- Data offset of a dynamic member inside a directly-passed dynamic tuple
      parameter, returning the first element word after the member length. -/
  | paramDynamicMemberDataOffset (name : String) (wordOffset : Nat)
  /-- Element access into an `Array<wordLike>` dynamic member inside a
      directly-passed dynamic tuple parameter. -/
  | paramDynamicMemberElement (name : String) (wordOffset : Nat) (innerIndex : Expr)
  /-- Base pointer for a static composite member inside a directly-passed
      dynamic tuple parameter. Event lowering uses this as the start of the
      projected tuple's ABI words and then encodes each static leaf. -/
  | paramDynamicStaticComposite (name : String) (wordOffset : Nat)
  /-- Length of a dynamic member inside a struct-array element.  Given a
      struct-array parameter `name` indexed at `index`, dereferences the
      head pointer at `wordOffset` (relative to the element's head
      section), then reads the length word at that pointer.  Used for
      `arrayLength (arrayElement <param> <i>).<dynamicField>` projections,
      e.g. `txn.nullifierHashes.length` where `txn` is an element of a
      struct-array parameter.  (verity#1849, G1) -/
  | arrayElementDynamicMemberLength (name : String) (index : Expr) (wordOffset : Nat)
  /-- Data offset of a dynamic word-array member nested inside a
      struct-array element.  The returned word points at the first element
      word (immediately after the member's ABI length word), matching the
      `_data_offset` convention used for direct dynamic-array parameters. -/
  | arrayElementDynamicMemberDataOffset (name : String) (index : Expr) (wordOffset : Nat)
  /-- Element access into a dynamic word-array member nested inside a
      struct-array element.  Given a struct-array parameter `name` indexed
      at `index`, dereferences the head pointer at `wordOffset` (relative
      to the element's head section), then reads the word at offset
      `32 + innerIndex*32` from that pointer after bounds-checking
      `innerIndex` against the member's stored length.  Used for
      `arrayElement (arrayElement <param> <i>).<dynamicField> <k>`
      projections, e.g. `txn.nullifierHashes[k]` where `txn` is an
      element of a struct-array parameter and `nullifierHashes` is an
      `Array Uint256` member.  (verity#1849, G2) -/
  | arrayElementDynamicMemberElement (name : String) (index : Expr) (wordOffset : Nat) (innerIndex : Expr)
  | storageArrayLength (field : String)  -- Read the length word of a storage dynamic array (#1571)
  | storageArrayElement (field : String) (index : Expr)  -- Checked element access of a storage dynamic array (#1571)
  /-- Equality on direct `bytes` / `string` parameters loaded from calldata or memory.
      The names refer to the dynamic parameter base names (`foo`, not `foo_offset`). -/
  | dynamicBytesEq (lhsName rhsName : String)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | sdiv (a b : Expr)
  | mod (a b : Expr)
  | smod (a b : Expr)
  | bitAnd (a b : Expr)
  | bitOr (a b : Expr)
  | bitXor (a b : Expr)
  | bitNot (a : Expr)
  | shl (shift value : Expr)
  | shr (shift value : Expr)
  | sar (shift value : Expr)
  | byte (index value : Expr)
  | signextend (byteIndex value : Expr)
  /-- Consumer-owned opcode intrinsic. Verity lowers using the supplied generic
      Yul descriptor and does not attach opcode-specific semantics. -/
  | intrinsic
      (name : String)
      (lowering : Verity.Core.Intrinsics.YulLowering)
      (minFork : Verity.Core.Intrinsics.HardFork)
      (args : List Expr)
  /-- Compile-time fork selection. `thenExpr` is selected when the compiler
      target fork is at least `required`; otherwise `elseExpr` is selected.
      The unselected branch is removed before intrinsic fork gates and Yul
      lowering run, so this is suitable for explicit opcode/emulation fallback
      pairs without silently weakening `min_fork` on the intrinsic itself. -/
  | forkIfAtLeast
      (required : Verity.Core.Intrinsics.HardFork)
      (thenExpr elseExpr : Expr)
  | eq (a b : Expr)
  | ge (a b : Expr)
  | gt (a b : Expr)  -- Greater than (strict)
  | sgt (a b : Expr)
  | lt (a b : Expr)
  | slt (a b : Expr)
  | le (a b : Expr)  -- Less than or equal
  | logicalAnd (a b : Expr)  -- Logical AND (both operands always evaluated)
  | logicalOr (a b : Expr)   -- Logical OR  (both operands always evaluated)
  | logicalNot (a : Expr)    -- Logical NOT
  /-- `ceilDiv(a, b)` = `a == 0 ? 0 : (a - 1) / b + 1` (overflow-safe ceiling division).
      Matches Solidity's Math256.ceilDiv / OpenZeppelin.
      Compiles to `mul(iszero(iszero(a)), add(div(sub(a, 1), b), 1))`. -/
  | ceilDiv (a b : Expr)
  /-- `mulDivDown(a, b, c)` = `a * b / c` (round toward zero).
      Compiles to `div(mul(a, b), c)`. (#928) -/
  | mulDivDown (a b c : Expr)
  /-- `mulDivUp(a, b, c)` = `(a * b + c - 1) / c` (round away from zero).
      Compiles to `div(add(mul(a, b), sub(c, 1)), c)`. (#928) -/
  | mulDivUp (a b c : Expr)
  /-- `mulDiv512Down(a, b, c)` = full-precision `(a * b) / c` (round toward
      zero). Unlike `mulDivDown`, the intermediate product is handled at
      full 512-bit precision and may exceed `2^256` as long as the final
      quotient fits in `uint256`. Reverts on zero divisor or when the
      quotient does not fit. Matches OpenZeppelin `Math.mulDiv` / Solmate
      `FullMath.mulDiv` semantics (verity#1761). -/
  | mulDiv512Down (a b c : Expr)
  /-- `mulDiv512Up(a, b, c)` = full-precision `ceil(a * b / c)`. Same
      semantics as `mulDiv512Down`, rounded up by 1 when the division is
      not exact. Matches OpenZeppelin `Math.mulDiv(..., Rounding.Ceil)`
      semantics (verity#1761). -/
  | mulDiv512Up (a b c : Expr)
  /-- `wMulDown(a, b)` = `a * b / WAD` (WAD = 1e18, round down).
      Sugar for `mulDivDown a b (literal WAD)`. (#928) -/
  | wMulDown (a b : Expr)
  /-- `wDivUp(a, b)` = `(a * WAD + b - 1) / b` (WAD = 1e18, round up).
      Compiles to `div(add(mul(a, WAD), sub(b, 1)), b)`. (#928) -/
  | wDivUp (a b : Expr)
  /-- `min(a, b)` — unsigned minimum.
      Compiles to `sub(a, mul(sub(a, b), gt(a, b)))`. (#928) -/
  | min (a b : Expr)
  /-- `max(a, b)` — unsigned maximum.
      Compiles to `add(a, mul(sub(b, a), gt(b, a)))`. (#928) -/
  | max (a b : Expr)
  /-- Expression-level conditional: `ite cond thenVal elseVal`.
      Compiles to branchless `add(mul(iszero(iszero(cond)), thenVal), mul(iszero(cond), elseVal))`.
      Both branches are eagerly evaluated; `cond` is evaluated twice.
      For complex conditions with side effects, bind to a local variable first. -/
  | ite (cond thenVal elseVal : Expr)
  /-- Construct an ADT value: `adtConstruct adtName variantName args`.
      Produces the tagged-union encoding for the given variant. (#1727 Step 5b) -/
  | adtConstruct (adtName variantName : String) (args : List Expr)
  /-- Read the tag byte of an ADT value: `adtTag adtName field`.
      Returns the 0-based tag index. (#1727 Step 5b) -/
  | adtTag (adtName field : String)
  /-- Read a field from an ADT value stored in contract storage.
      `storageField` names the contract storage field holding the ADT.
      `fieldIndex` is the 0-based index within the variant's field list,
      pre-resolved at IR construction time. (#1727 Steps 5b/5c) -/
  | adtField (adtName variantName fieldName : String) (fieldIndex : Nat) (storageField : String)
  deriving Repr

namespace Expr

/-- Immediate sub-expressions of an expression, enumerated once for the whole
    AST. Generic traversals (`anyDeep`, `foldDeep`, validator passes) consume
    this surface instead of duplicating constructor-by-constructor walks: a new
    `Expr` constructor fails to compile here (and in `children_sizeOf_lt`)
    rather than silently falling through a dozen independent walkers. -/
def children : Expr → List Expr
  | .literal _ | .param _ | .constructorArg _ | .immutable _ | .storage _ | .storageAddr _
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue
  | .selfBalance | .blockTimestamp | .blockNumber | .blobbasefee
  | .calldatasize | .returndataSize | .localVar _
  | .arrayLength _ | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ | .paramDynamicStaticComposite _ _
  | .storageArrayLength _ | .dynamicBytesEq _ _
  | .adtTag _ _ | .adtField _ _ _ _ _ => []
  | .mapping _ key | .mappingWord _ key _ | .mappingPackedWord _ key _ _
  | .mappingUint _ key | .structMember _ key _ => [key]
  | .mapping2 _ key1 key2 | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ => [key1, key2]
  | .mappingChain _ keys => keys
  | .mload offset | .tload offset | .calldataload offset
  | .extcodesize offset | .returndataOptionalBoolAt offset => [offset]
  | .keccak256 offset size => [offset, size]
  | .call gas target value inOffset inSize outOffset outSize =>
      [gas, target, value, inOffset, inSize, outOffset, outSize]
  | .staticcall gas target inOffset inSize outOffset outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      [gas, target, inOffset, inSize, outOffset, outSize]
  | .externalCall _ args | .internalCall _ args
  | .intrinsic _ _ _ args | .adtConstruct _ _ args => args
  | .arrayElement _ index | .memoryArrayElement _ index
  | .arrayElementWord _ index _ _ | .arrayElementDynamicWord _ index _
  | .arrayElementDynamicDataOffset _ index
  | .arrayElementDynamicMemberLength _ index _
  | .arrayElementDynamicMemberDataOffset _ index _
  | .storageArrayElement _ index => [index]
  | .arrayElementDynamicMemberElement _ index _ innerIndex => [index, innerIndex]
  | .paramDynamicMemberElement _ _ innerIndex => [innerIndex]
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b
  | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b => [a, b]
  | .bitNot a | .logicalNot a => [a]
  | .forkIfAtLeast _ thenExpr elseExpr => [thenExpr, elseExpr]
  | .ite cond thenVal elseVal => [cond, thenVal, elseVal]
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c => [a, b, c]

/-- Every immediate child is structurally smaller, so well-founded traversals
    over `children` terminate. -/
theorem children_sizeOf_lt (e : Expr) :
    ∀ c ∈ children e, sizeOf c < sizeOf e := by
  have step : ∀ (c : Expr) (l : List Expr), c ∈ l → sizeOf c < sizeOf l := by
    intro c l hc
    exact List.sizeOf_lt_of_mem hc
  intro c hc
  cases e <;> simp only [children] at hc <;>
    first
      | exact absurd hc (List.not_mem_nil)
      | (simp at hc
         first
           | subst hc
           | (rcases hc with rfl | rfl)
           | (rcases hc with rfl | rfl | rfl)
           | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl)
           | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
         all_goals (simp <;> omega))
      | (have hlt := step c _ hc; simp <;> omega)

/-- Deep predicate: does `p` hold for this expression or any (transitive)
    sub-expression? Total via the `children_sizeOf_lt` measure, so it can be
    used in proofs as well as compiler passes. -/
def anyDeep (p : Expr → Bool) (e : Expr) : Bool :=
  p e || (children e).attach.any (fun ⟨c, hc⟩ =>
    have := children_sizeOf_lt e c hc
    anyDeep p c)
termination_by sizeOf e

/-- Deep boolean fold over expressions. This is the public validator-facing
    name for expression predicates that should be checked over the whole
    expression tree. -/
def foldBool (p : Expr → Bool) (e : Expr) : Bool :=
  e.anyDeep p

/-- Deep universal: `p` holds for this expression and all sub-expressions. -/
def allDeep (p : Expr → Bool) (e : Expr) : Bool :=
  p e && (children e).attach.all (fun ⟨c, hc⟩ =>
    have := children_sizeOf_lt e c hc
    allDeep p c)
termination_by sizeOf e

/-- Deep monadic check: run `check` on this expression and every (transitive)
    sub-expression in pre-order, short-circuiting on the first error. Total via
    `children_sizeOf_lt`. -/
def forDeepM (check : Expr → Except String Unit) (e : Expr) : Except String Unit := do
  check e
  (children e).attach.forM (fun ⟨c, hc⟩ =>
    have := children_sizeOf_lt e c hc
    forDeepM check c)
termination_by sizeOf e

/-- Deep monadic expression validator fold, in pre-order. -/
def checkRec (check : Expr → Except String Unit) (e : Expr) : Except String Unit :=
  e.forDeepM check

/-- Deep monadic check in post-order: run `check` on every (transitive)
    sub-expression before the expression itself, short-circuiting on the
    first error. Matches validators that check a node's operands before the
    node's own shape. -/
def forDeepPostM (check : Expr → Except String Unit) (e : Expr) : Except String Unit := do
  (children e).attach.forM (fun ⟨c, hc⟩ =>
    have := children_sizeOf_lt e c hc
    forDeepPostM check c)
  check e
termination_by sizeOf e

end Expr

structure ImmutableSpec where
  name : String
  ty : ParamType
  init : Expr
  deriving Repr

inductive Stmt
  | letVar (name : String) (value : Expr)  -- Declare local variable
  | assignVar (name : String) (value : Expr)  -- Reassign existing variable
  | setStorage (field : String) (value : Expr)
  | setStorageAddr (field : String) (value : Expr)
  | setImmutable (name : String) (value : Expr)
  /-- Write a full storage word at `field.slot + wordOffset`.  Intended for
      migration-faithful manual packed-word writes where the source constructs
      the packed word explicitly. -/
  | setStorageWord (field : String) (wordOffset : Nat) (value : Expr)
  | storageArrayPush (field : String) (value : Expr)  -- Append to a storage dynamic array (#1571)
  | storageArrayPop (field : String)  -- Pop from a storage dynamic array (#1571)
  | setStorageArrayElement (field : String) (index : Expr) (value : Expr)  -- Indexed write (#1571)
  | setMapping (field : String) (key : Expr) (value : Expr)
  | setMappingWord (field : String) (key : Expr) (wordOffset : Nat) (value : Expr)  -- mappingSlot(base,key)+wordOffset write
  | setMappingPackedWord (field : String) (key : Expr) (wordOffset : Nat) (packed : PackedBits) (value : Expr)
  | setMapping2 (field : String) (key1 key2 : Expr) (value : Expr)  -- Double mapping write (#154)
  | setMapping2Word (field : String) (key1 key2 : Expr) (wordOffset : Nat) (value : Expr)  -- Double mapping + word offset write
  | setMappingUint (field : String) (key : Expr) (value : Expr)  -- Uint256-keyed mapping write (#154)
  | setMappingChain (field : String) (keys : List Expr) (value : Expr)  -- Arbitrary-depth mapping write (#1570)
  /-- Write to a named member of a struct-valued mapping.
      Resolves the member's word offset and optional packed bits at compile time.
      Generates the same Yul as `setMappingPackedWord` (or `setMappingWord` when
      unpacked), including alias slot mirror writes. -/
  | setStructMember (field : String) (key : Expr) (memberName : String) (value : Expr)
  /-- Write to a named member of a struct-valued double mapping.
      `setStructMember2 field key1 key2 memberName value` resolves the member's
      word offset and packed bits from the field's struct definition. -/
  | setStructMember2 (field : String) (key1 key2 : Expr) (memberName : String) (value : Expr)
  | require (cond : Expr) (message : String)
  | requireError (cond : Expr) (errorName : String) (args : List Expr)
  | revertError (errorName : String) (args : List Expr)
  /-- Revert with Solidity's built-in `Panic(uint256)` ABI payload. -/
  | panicCode (code : Expr)
  | return (value : Expr)
  | returnValues (values : List Expr)  -- ABI-encode multiple static return words
  | returnArray (name : String)        -- ABI-encode dynamic uint256[] parameter loaded from calldata
  | returnBytes (name : String)        -- ABI-encode dynamic bytes parameter loaded from calldata
  | returnStorageWords (name : String) -- ABI-encode dynamic uint256[] from sload over a dynamic word-array parameter
  | returnCodeData (pointer : Expr)    -- Return an ABI payload stored as runtime code at `pointer`.
  | mstore (offset value : Expr)
  | tstore (offset value : Expr)
  /-- First-class `calldatacopy(destOffset, sourceOffset, size)` statement. -/
  | calldatacopy (destOffset sourceOffset size : Expr)
  /-- First-class `returndatacopy(destOffset, sourceOffset, size)` statement. -/
  | returndataCopy (destOffset sourceOffset size : Expr)
  /-- Forward current returndata as revert payload (`returndatacopy` + `revert`). -/
  | revertReturndata
  | stop
  | ite (cond : Expr) (thenBranch : List Stmt) (elseBranch : List Stmt)  -- If/else (#179)
  | forEach (varName : String) (count : Expr) (body : List Stmt)  -- Bounded loop (#179)
  /-- Iterate over the set bits of `bitmap` from most significant to least
      significant.  The loop variable is bound to the current set-bit index.
      Lowering uses the EIP-7939 CLZ/MSB pattern:
      `idx := 255 - clz(bitmap); bitmap := bitmap & ~(1 << idx)`. -/
  | forEachSetBit (varName : String) (bitmap : Expr) (body : List Stmt)
  | emit (eventName : String) (args : List Expr)  -- Emit event (#153)
  | internalCall (functionName : String) (args : List Expr)  -- Internal call as statement (#181)
  | internalCallAssign (names : List String) (functionName : String) (args : List Expr)
  /-- Low-level log emission: `logN(dataOffset, dataSize, topic0, …, topicN-1)`.
      `topics` must contain 0–4 expressions (selects log0–log4).
      The caller is responsible for prior `mstore` calls that populate the data region. (#930) -/
  | rawLog (topics : List Expr) (dataOffset dataSize : Expr)
  /-- Perform an external call and bind ABI-decoded return values to local variables.
      Reverts with forwarded returndata on call failure or insufficient return data. -/
  | externalCallBind
      (resultVars : List String)  -- local vars to bind return values to
      (externalName : String)     -- name of the external function declaration
      (args : List Expr)          -- call arguments
  /-- Perform an external call without auto-reverting on failure.
      Binds a success flag (0/1) to `successVar` and return values to `resultVars`.
      The caller is responsible for checking the success flag and handling failures.
      (#1727, Axis 1 Step 5f) -/
  | tryExternalCallBind
      (successVar : String)       -- local var bound to success flag (0 = failure, 1 = success)
      (resultVars : List String)  -- local vars to bind return values to (only valid if success == 1)
      (externalName : String)     -- name of the external function declaration
      (args : List Expr)          -- call arguments
  /-- Invoke an External Call Module with the given arguments.
      This generic variant delegates validation, compilation, and state analysis
      to the module's metadata and compile function. See Compiler.ECM (#964). -/
  | ecm (mod : ECM.ExternalCallModule) (args : List Expr)
  /-- Unsafe block: `unsafe "reason" do body`.
      Marks a region where restricted operations (Step 6b) are permitted.
      The reason string is preserved for trust reporting (Step 6c). -/
  | unsafeBlock (reason : String) (body : List Stmt)
  /-- Typed handwritten Yul fragment with localized proof obligations and
      trust-surface metadata. Lowering to EVMYul AST is centralized in
      `CompilationModel.unsafeYulToEVMYul`. -/
  | unsafeYul (fragment : UnsafeYulFragment)
  /-- Pattern match on an ADT value: `matchAdt adtName scrutinee branches`.
      Each branch is `(variantName, boundVarNames, body)`.
      Compiles to `YulStmt.switch` on the tag byte. (#1727 Step 5b) -/
  | matchAdt (adtName : String) (scrutinee : Expr)
      (branches : List (String × List String × List Stmt))
  deriving Repr

/-- Common statement metadata. New `Stmt` constructors should be represented
    here once, then generic traversals and collectors can consume this surface
    instead of duplicating constructor-by-constructor walks. -/
structure StmtMetadata where
  subexpressions : List Expr := []
  termination : StmtTermination := .fallsThrough
  controlFlow : ControlFlowSummary := {}
  lowLevelMechanics : List LowLevelMechanic := []
  scopeEffects : StmtScopeEffects := {}
  localObligations : List LocalObligation := []
  unsafeYulContracts : List UnsafeYulContract := []
  unsafeReasons : List String := []
  deriving Repr

namespace Stmt

def childLists : Stmt → List (List Stmt)
  | .ite _ thenBranch elseBranch => [thenBranch, elseBranch]
  | .forEach _ _ body => [body]
  | .forEachSetBit _ _ body => [body]
  | .unsafeBlock _ body => [body]
  | .matchAdt _ _ branches => branches.map (fun (_, _, body) => body)
  | _ => []

def directMetadata : Stmt → StmtMetadata
  | .letVar name value =>
      { subexpressions := [value], scopeEffects := { bindNames := [name] } }
  | .assignVar name value =>
      { subexpressions := [value], scopeEffects := { assignNames := [name] } }
  | .setStorage field value | .setStorageAddr field value =>
      { subexpressions := [value], scopeEffects := { storageWrites := [field] } }
  | .setImmutable _ value =>
      { subexpressions := [value] }
  | .setStorageWord field _ value =>
      { subexpressions := [value], scopeEffects := { storageWrites := [field] } }
  | .storageArrayPush field value =>
      { subexpressions := [value], scopeEffects := { storageWrites := [field] } }
  | .storageArrayPop field =>
      { scopeEffects := { storageWrites := [field] } }
  | .setStorageArrayElement field index value =>
      { subexpressions := [index, value], scopeEffects := { storageWrites := [field] } }
  | .setMapping field key value | .setMappingWord field key _ value
  | .setMappingPackedWord field key _ _ value | .setMappingUint field key value
  | .setStructMember field key _ value =>
      { subexpressions := [key, value], scopeEffects := { storageWrites := [field] } }
  | .setMappingChain field keys value =>
      { subexpressions := keys ++ [value], scopeEffects := { storageWrites := [field] } }
  | .setMapping2 field key1 key2 value | .setMapping2Word field key1 key2 _ value
  | .setStructMember2 field key1 key2 _ value =>
      { subexpressions := [key1, key2, value], scopeEffects := { storageWrites := [field] } }
  | .require cond _ =>
      { subexpressions := [cond], termination := .mayTerminate, controlFlow := .mayReverting }
  | .requireError cond _ args =>
      { subexpressions := cond :: args, termination := .mayTerminate, controlFlow := .mayReverting }
  | .revertError _ args =>
      { subexpressions := args, termination := .alwaysTerminates, controlFlow := .reverts }
  | .panicCode code =>
      { subexpressions := [code], termination := .alwaysTerminates, controlFlow := .reverts }
  | .return value =>
      { subexpressions := [value], termination := .alwaysTerminates, controlFlow := .returns }
  | .returnValues values =>
      { subexpressions := values, termination := .alwaysTerminates, controlFlow := .returns }
  | .returnArray _ | .returnBytes _ | .returnStorageWords _ =>
      { termination := .alwaysTerminates, controlFlow := .returns }
  | .returnCodeData pointer =>
      { subexpressions := [pointer], termination := .alwaysTerminates, controlFlow := .returns }
  | .mstore offset value =>
      { subexpressions := [offset, value], lowLevelMechanics := [.mstore] }
  | .tstore offset value =>
      { subexpressions := [offset, value], lowLevelMechanics := [.tstore] }
  | .calldatacopy destOffset sourceOffset size =>
      { subexpressions := [destOffset, sourceOffset, size], lowLevelMechanics := [.calldatacopy] }
  | .returndataCopy destOffset sourceOffset size =>
      { subexpressions := [destOffset, sourceOffset, size], lowLevelMechanics := [.returndataCopy] }
  | .revertReturndata =>
      { termination := .alwaysTerminates, controlFlow := .reverts, lowLevelMechanics := [.revertReturndata] }
  | .stop =>
      { termination := .alwaysTerminates, controlFlow := .stops }
  | .ite cond _ _ =>
      { subexpressions := [cond], termination := .mayTerminate, controlFlow := .unknown }
  | .forEach varName count _ =>
      { subexpressions := [count], scopeEffects := { bindNames := [varName] } }
  | .forEachSetBit varName bitmap _ =>
      { subexpressions := [bitmap], scopeEffects := { bindNames := [varName] } }
  | .emit _ args =>
      { subexpressions := args }
  | .internalCall _ args =>
      { subexpressions := args }
  | .internalCallAssign names _ args =>
      { subexpressions := args, scopeEffects := { bindNames := names } }
  | .rawLog topics dataOffset dataSize =>
      { subexpressions := topics ++ [dataOffset, dataSize] }
  | .externalCallBind resultVars _ args =>
      { subexpressions := args, scopeEffects := { bindNames := resultVars } }
  | .tryExternalCallBind successVar resultVars _ args =>
      { subexpressions := args, scopeEffects := { bindNames := successVar :: resultVars } }
  | .ecm mod args =>
      { subexpressions := args, scopeEffects := { bindNames := mod.resultVars } }
  | .unsafeBlock reason _ =>
      { unsafeReasons := [reason] }
  | .unsafeYul fragment =>
      { termination := fragment.termination
        controlFlow := fragment.controlFlow
        lowLevelMechanics := fragment.mechanics
        scopeEffects := fragment.scopeEffects
        localObligations := fragment.obligations
        unsafeYulContracts := fragment.contracts
        unsafeReasons := [fragment.label] }
  | .matchAdt _ scrutinee branches =>
      { subexpressions := [scrutinee]
        termination := .mayTerminate
        controlFlow := .unknown
        scopeEffects := { bindNames := branches.flatMap (fun (_, names, _) => names) } }

partial def fold (f : α → Stmt → StmtMetadata → α) (init : α) (stmt : Stmt) : α :=
  let md := stmt.directMetadata
  let acc := f init stmt md
  stmt.childLists.foldl
    (fun acc childList => childList.foldl (fun inner child => child.fold f inner) acc)
    acc

partial def foldList (f : α → Stmt → StmtMetadata → α) (init : α) (stmts : List Stmt) : α :=
  stmts.foldl (fun acc stmt => stmt.fold f acc) init

/-- Every statement in a child list is structurally smaller than its parent,
    so well-founded deep traversals over `childLists` terminate. -/
theorem childLists_sizeOf_lt (s : Stmt) :
    ∀ l ∈ childLists s, ∀ c ∈ l, sizeOf c < sizeOf l ∧ sizeOf l < sizeOf s := by
  intro l hl c hc
  refine ⟨List.sizeOf_lt_of_mem hc, ?_⟩
  cases s <;> simp only [childLists] at hl <;>
    first
      | exact absurd hl (List.not_mem_nil)
      | (simp at hl;
         (first
           | subst hl
           | (rcases hl with rfl | rfl)) <;>
         (simp <;> omega))
      | (rename_i branches
         simp only [List.mem_map] at hl
         obtain ⟨branch, hbranch, rfl⟩ := hl
         have h1 := List.sizeOf_lt_of_mem hbranch
         obtain ⟨name, vars, body⟩ := branch
         simp at h1 ⊢
         omega)

/-- Deep statement predicate: does `p` hold for this statement or any
    statement nested inside it (if/loop/unsafe-block/match bodies)? Total via
    `childLists_sizeOf_lt`, so usable in both compiler passes and proofs.
    Expression-level conditions are expressed inside `p` via
    `directMetadata.subexpressions`. -/
def anyDeep (p : Stmt → Bool) (s : Stmt) : Bool :=
  p s || (childLists s).attach.any (fun ⟨l, hl⟩ =>
    l.attach.any (fun ⟨c, hc⟩ =>
      have := childLists_sizeOf_lt s l hl c hc
      anyDeep p c))
termination_by sizeOf s
decreasing_by exact Nat.lt_trans this.1 this.2

/-- Deep statement predicate over a statement list. -/
def anyDeepList (p : Stmt → Bool) (stmts : List Stmt) : Bool :=
  stmts.any (anyDeep p)

/-- Deep boolean fold over statements. Expression-level conditions should be
    expressed by the node predicate using `Stmt.directMetadata.subexpressions`
    or `Expr.foldBool`. -/
def foldBool (p : Stmt → Bool) (s : Stmt) : Bool :=
  s.anyDeep p

/-- Deep boolean fold over a statement list. -/
def foldBoolList (p : Stmt → Bool) (stmts : List Stmt) : Bool :=
  Stmt.anyDeepList p stmts

/-- Deep monadic check: run `check` on this statement and every statement
    nested inside it (pre-order; child lists in declaration order),
    short-circuiting on the first error. Statement-local expression conditions
    are expressed inside `check` via `directMetadata.subexpressions`. -/
def forDeepM (check : Stmt → Except String Unit) (s : Stmt) : Except String Unit := do
  check s
  (childLists s).attach.forM (fun ⟨l, hl⟩ =>
    l.attach.forM (fun ⟨c, hc⟩ =>
      have := childLists_sizeOf_lt s l hl c hc
      forDeepM check c))
termination_by sizeOf s
decreasing_by exact Nat.lt_trans this.1 this.2

/-- Deep monadic check over a statement list. -/
def forDeepListM (check : Stmt → Except String Unit) (stmts : List Stmt) :
    Except String Unit :=
  stmts.forM (forDeepM check)

/-- Deep monadic statement validator fold, in pre-order. -/
def checkRec (check : Stmt → Except String Unit) (s : Stmt) : Except String Unit :=
  s.forDeepM check

/-- Deep monadic statement-list validator fold, in pre-order. -/
def checkRecList (check : Stmt → Except String Unit) (stmts : List Stmt) :
    Except String Unit :=
  Stmt.forDeepListM check stmts

/-- Deep monadic fold over branch bodies used by ADT statement matches. -/
def checkRecBranches (check : Stmt → Except String Unit)
    (branches : List (String × List String × List Stmt)) : Except String Unit :=
  branches.forM fun (_, _, body) => Stmt.checkRecList check body

mutual
partial def controlFlow : Stmt → ControlFlowSummary
  | .require _ _ | .requireError _ _ _ =>
      .mayReverting
  | .revertError _ _ | .panicCode _ | .revertReturndata =>
      .reverts
  | .return _ | .returnValues _ | .returnArray _ | .returnBytes _ | .returnStorageWords _ | .returnCodeData _ =>
      .returns
  | .stop =>
      .stops
  | .ite _ thenBranch elseBranch =>
      ControlFlowSummary.union (controlFlowList thenBranch) (controlFlowList elseBranch)
  | .forEach _ _ body =>
      -- Loops are bounded and may execute zero times, so the loop itself can fall through
      -- even if some body path returns or reverts.
      ControlFlowSummary.union .fallsThrough (controlFlowList body)
  | .forEachSetBit _ _ body =>
      ControlFlowSummary.union .fallsThrough (controlFlowList body)
  | .unsafeBlock _ body =>
      controlFlowList body
  | .matchAdt _ _ branches =>
      controlFlowBranches branches
  | .unsafeYul fragment =>
      fragment.controlFlow
  | _ =>
      .fallsThrough

partial def controlFlowList : List Stmt → ControlFlowSummary
  | [] => .fallsThrough
  | stmt :: rest =>
      ControlFlowSummary.seq (controlFlow stmt) (controlFlowList rest)

partial def controlFlowBranches : List (String × List String × List Stmt) → ControlFlowSummary
  | [] => .noPaths
  | (_, _, body) :: rest =>
      ControlFlowSummary.union (controlFlowList body) (controlFlowBranches rest)
end

example : (controlFlowList [Stmt.return (Expr.literal 1), Stmt.stop]).mayStop = false := by
  native_decide

example : (controlFlow (Stmt.require (Expr.literal 1) "ok")).mayRevert = true := by
  native_decide

partial def metadataDeep (stmt : Stmt) : StmtMetadata :=
  stmt.fold
    (fun acc _ md =>
      { subexpressions := acc.subexpressions ++ md.subexpressions
        termination := if acc.termination == .alwaysTerminates then .alwaysTerminates else md.termination
        controlFlow := ControlFlowSummary.union acc.controlFlow md.controlFlow
        lowLevelMechanics := acc.lowLevelMechanics ++ md.lowLevelMechanics
        scopeEffects :=
          { bindNames := acc.scopeEffects.bindNames ++ md.scopeEffects.bindNames
            assignNames := acc.scopeEffects.assignNames ++ md.scopeEffects.assignNames
            storageWrites := acc.scopeEffects.storageWrites ++ md.scopeEffects.storageWrites }
        localObligations := acc.localObligations ++ md.localObligations
        unsafeYulContracts := acc.unsafeYulContracts ++ md.unsafeYulContracts
        unsafeReasons := acc.unsafeReasons ++ md.unsafeReasons })
    {}

def metadataListDeep (stmts : List Stmt) : StmtMetadata :=
  foldList
    (fun acc _ md =>
      { subexpressions := acc.subexpressions ++ md.subexpressions
        termination := if acc.termination == .alwaysTerminates then .alwaysTerminates else md.termination
        controlFlow := ControlFlowSummary.union acc.controlFlow md.controlFlow
        lowLevelMechanics := acc.lowLevelMechanics ++ md.lowLevelMechanics
        scopeEffects :=
          { bindNames := acc.scopeEffects.bindNames ++ md.scopeEffects.bindNames
            assignNames := acc.scopeEffects.assignNames ++ md.scopeEffects.assignNames
            storageWrites := acc.scopeEffects.storageWrites ++ md.scopeEffects.storageWrites }
        localObligations := acc.localObligations ++ md.localObligations
        unsafeYulContracts := acc.unsafeYulContracts ++ md.unsafeYulContracts
        unsafeReasons := acc.unsafeReasons ++ md.unsafeReasons })
    {}
    stmts

end Stmt

structure FunctionSpec where
  name : String
  params : List Param
  returnType : Option FieldType  -- None for unit/void
  returns : List ParamType := []  -- preferred ABI return model; falls back to returnType when empty
  /-- Whether this entrypoint accepts non-zero msg.value. -/
  isPayable : Bool := false
  /-- Whether this entrypoint is ABI-marked as `view` (read-only intent). -/
  isView : Bool := false
  /-- Whether this entrypoint is ABI-marked as `pure` (no state/environment reads intent). -/
  isPure : Bool := false
  body : List Stmt
  /-- Storage field names declared in `modifies(...)`.  When non-empty the
      compiler validates that the body only writes to these fields and emits
      a frame theorem for all other fields.  (#1729, Axis 3 Step 1b) -/
  modifies : List String := []
  /-- Whether this function is annotated `no_external_calls`.  When true the
      compiler validates that the body contains no external call statements
      and emits a `_no_calls` theorem.  (#1729, Axis 3 Step 1c) -/
  noExternalCalls : Bool := false
  /-- Whether this function is annotated `allow_post_interaction_writes`.
      When true, CEI enforcement is bypassed for this function.
      (#1728, Axis 2 Step 2a) -/
  allowPostInteractionWrites : Bool := false
  /-- Storage field name used as reentrancy lock when annotated `nonreentrant(field)`.
      When non-empty, CEI enforcement is bypassed because the lock prevents
      reentrant state corruption.  (#1728, Axis 2 Step 2b) -/
  nonReentrantLock : Option String := none
  /-- Whether this function is annotated `cei_safe` — the user asserts CEI
      safety via a machine-checked proof obligation.  CEI enforcement is bypassed
      and a proof obligation is generated.  (#1728, Axis 2 Step 2b) -/
  ceiSafe : Bool := false
  /-- Whether this function is annotated `reentrancy_trusted` — an *unproven*
      author assertion that the function's external interaction surface cannot be
      exploited by a reentrant adversary (e.g. every external callee is a trusted
      contract that does not re-enter this one). This is the audited opt-out for
      the cross-function reentrancy gate: unlike `cei_safe`/`allow_post_interaction_writes`
      (which only concern single-function CEI), a mutating external call still opens
      a reentrancy window that another entrypoint could exploit, so the gate requires
      either a runtime `nonreentrant(<lock>)` guard or this explicit trust assertion.
      It generates no code and no proof obligation; it is a trust boundary recorded
      for audit. -/
  reentrancyTrusted : Bool := false
  /-- Storage field name used as access-control role when annotated `requires(field)`.
      A `require(caller == roleHolder)` check is auto-injected at the start of the
      function body.  (#1728, Axis 2 Step 2c) -/
  requiresRole : Option String := none
  /-- Whether this is an internal-only function (not exposed via selector dispatch) -/
  isInternal : Bool := false
  /-- Local proof obligations that isolate unsafe/assembly-shaped trust
      boundaries to this function rather than the entire contract. -/
  localObligations : List LocalObligation := []
  deriving Repr

structure ConstructorSpec where
  params : List Param  -- Constructor parameters (passed at deployment)
  /-- Whether deployment is allowed with non-zero msg.value. -/
  isPayable : Bool := false
  body : List Stmt     -- Initialization code
  /-- Local proof obligations that isolate unsafe/assembly-shaped trust
      boundaries to this constructor rather than the entire contract. -/
  localObligations : List LocalObligation := []
  deriving Repr

structure CompilationModel where
  name : String
  fields : List Field
  immutables : List ImmutableSpec := []
  /-- Explicit owner/admin/minter/relayer-style access-control declarations.
      Functions annotated with `requires(role)` resolve through this list when
      present; legacy `requires(storageField)` remains accepted for existing
      contracts. -/
  roles : List RoleDecl := []
  /-- Storage slots reserved for compatibility policy; compiler rejects field
      canonical/alias write slots that overlap these intervals. -/
  reservedSlotRanges : List ReservedSlotRange := []
  /-- Slot remap policy for compatibility mirror writes.
      Any field whose canonical slot is in a source interval also mirrors writes
      to the corresponding target slot with the same relative offset. -/
  slotAliasRanges : List SlotAliasRange := []
  constructor : Option ConstructorSpec  -- Deploy-time initialization with params
  functions : List FunctionSpec
  events : List EventDef := []  -- Event definitions (#153)
  errors : List ErrorDef := []  -- Custom errors (#586)
  externals : List ExternalFunction := []  -- External function declarations (#184)
  /-- User-defined algebraic data types (tagged unions). (#1727 Step 5b) -/
  adtTypes : List AdtTypeDef := []
  /-- EIP-7201 storage namespace offset.  When `some n`, every user-declared
      `slot k` was already shifted by `n` during macro elaboration.  The value
      is `keccak256("{ContractName}.storage.v0")` as a 256-bit Nat.
      (#1730, Axis 4 Step 4d) -/
  storageNamespace : Option Nat := none
  deriving Repr

/-!
## IR Generation from Spec

Automatically compile a CompilationModel to IRContract.
-/

-- Helper: Look up a field by name, resolving its canonical slot, and apply
-- a caller-supplied projection to the matched field and resolved slot.
private def findFieldByName (fields : List Field) (name : String)
    (extract : Field → Nat → α) : Option α :=
  let rec go (remaining : List Field) (idx : Nat) : Option α :=
    match remaining with
    | [] => none
    | f :: rest =>
        if f.name == name then some (extract f (f.slot.getD idx))
        else go rest (idx + 1)
  go fields 0

def findFieldSlot (fields : List Field) (name : String) : Option Nat :=
  findFieldByName fields name fun _ slot => slot

def findFieldWithResolvedSlot (fields : List Field) (name : String) : Option (Field × Nat) :=
  findFieldByName fields name fun f slot => (f, slot)

theorem field_mem_of_findFieldWithResolvedSlot_eq_some
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    f ∈ fields := by
  unfold findFieldWithResolvedSlot at h
  unfold findFieldByName at h
  -- h now involves findFieldByName.go. We generalise the index.
  suffices ∀ (flds : List Field) (idx : Nat),
      findFieldByName.go name (fun f slot => (f, slot)) flds idx = some (f, slot) →
      f ∈ flds by
    exact this fields 0 h
  intro flds idx hgo
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go] at hgo
  | cons hd tl ih =>
      simp only [findFieldByName.go] at hgo
      split at hgo
      · simp at hgo; exact hgo.1 ▸ List.Mem.head tl
      · exact List.Mem.tail hd (ih (idx + 1) hgo)

theorem fieldName_eq_of_findFieldWithResolvedSlot_eq_some
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    f.name = name := by
  unfold findFieldWithResolvedSlot at h
  unfold findFieldByName at h
  suffices ∀ (flds : List Field) (idx : Nat),
      findFieldByName.go name (fun f slot => (f, slot)) flds idx = some (f, slot) →
      f.name = name by
    exact this fields 0 h
  intro flds idx hgo
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go] at hgo
  | cons hd tl ih =>
      simp only [findFieldByName.go] at hgo
      split at hgo
      case isTrue hname =>
        simp at hgo; rw [← hgo.1]; exact beq_iff_eq.mp hname
      case isFalse =>
        exact ih (idx + 1) hgo

private theorem find_eq_of_findFieldByName_go
    {name : String}
    {f : Field}
    {slot : Nat}
    {fields : List Field}
    {idx : Nat} :
    findFieldByName.go name (fun f slot => (f, slot)) fields idx = some (f, slot) →
    fields.find? (·.name == name) = some f := by
  intro hgo
  induction fields generalizing idx with
  | nil => simp [findFieldByName.go] at hgo
  | cons hd tl ih =>
    simp only [findFieldByName.go] at hgo
    by_cases hname : hd.name == name
    · simp [hname] at hgo ⊢
      exact hgo.1
    · simp [hname] at hgo ⊢
      exact ih hgo

def findFieldWriteSlots (fields : List Field) (name : String) : Option (List Nat) :=
  findFieldByName fields name fun f slot => slot :: f.aliasSlots

/-- `findFieldWithResolvedSlot` iterates from `idx` onward; this exposes the recursive step. -/
theorem findFieldWithResolvedSlot_nil (name : String) :
    findFieldWithResolvedSlot [] name = none := rfl

theorem findFieldWithResolvedSlot_cons (f : Field) (rest : List Field) (name : String) :
    findFieldWithResolvedSlot (f :: rest) name =
      if f.name == name then some (f, f.slot.getD 0)
      else findFieldByName.go name (fun f slot => (f, slot)) rest 1 := rfl

/-- Stepping lemma for the internal go. -/
theorem findFieldWithResolvedSlot_go_nil (name : String) (idx : Nat) :
    findFieldByName.go name (fun f slot => (f, slot)) ([] : List Field) idx = none := rfl

theorem findFieldWithResolvedSlot_go_cons (f : Field) (rest : List Field)
    (name : String) (idx : Nat) :
    findFieldByName.go name (fun f slot => (f, slot)) (f :: rest) idx =
      if f.name == name then some (f, f.slot.getD idx)
      else findFieldByName.go name (fun f slot => (f, slot)) rest (idx + 1) := rfl

/-- Stepping lemmas for findFieldWriteSlots. -/
theorem findFieldWriteSlots_nil (name : String) :
    findFieldWriteSlots [] name = none := rfl

theorem findFieldWriteSlots_cons (f : Field) (rest : List Field) (name : String) :
    findFieldWriteSlots (f :: rest) name =
      if f.name == name then some (f.slot.getD 0 :: f.aliasSlots)
      else findFieldByName.go name (fun f slot => slot :: f.aliasSlots) rest 1 := rfl

theorem findFieldWriteSlots_go_nil (name : String) (idx : Nat) :
    findFieldByName.go name (fun f slot => slot :: f.aliasSlots) ([] : List Field) idx =
      none := rfl

theorem findFieldWriteSlots_go_cons (f : Field) (rest : List Field)
    (name : String) (idx : Nat) :
    findFieldByName.go name (fun f slot => slot :: f.aliasSlots) (f :: rest) idx =
      if f.name == name then some (f.slot.getD idx :: f.aliasSlots)
      else findFieldByName.go name (fun f slot => slot :: f.aliasSlots) rest (idx + 1) := rfl

/-- Bridge: findFieldWithResolvedSlot matches any function with the same recursive structure. -/
theorem findFieldWithResolvedSlot_go_eq_rec
    (flds : List Field) (idx : Nat) (name : String)
    {rec : List Field → Nat → Option (Field × Nat)}
    (hnil : ∀ i, rec [] i = none)
    (hcons : ∀ (hd : Field) (tl : List Field) (i : Nat),
        rec (hd :: tl) i = if hd.name == name then some (hd, hd.slot.getD i) else rec tl (i + 1)) :
    findFieldByName.go name (fun f slot => (f, slot)) flds idx = rec flds idx := by
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go, hnil]
  | cons hd tl ih => simp [findFieldByName.go, hcons]; split <;> simp_all

/-- Bridge: findFieldWriteSlots matches any function with the same recursive structure. -/
theorem findFieldWriteSlots_go_eq_rec
    (flds : List Field) (idx : Nat) (name : String)
    {rec : List Field → Nat → Option (List Nat)}
    (hnil : ∀ i, rec [] i = none)
    (hcons : ∀ (hd : Field) (tl : List Field) (i : Nat),
        rec (hd :: tl) i = if hd.name == name then some (hd.slot.getD i :: hd.aliasSlots) else rec tl (i + 1)) :
    findFieldByName.go name (fun f slot => slot :: f.aliasSlots) flds idx = rec flds idx := by
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go, hnil]
  | cons hd tl ih => simp [findFieldByName.go, hcons]; split <;> simp_all

/-- Standalone copy of `findFieldByName.go` for resolved slot, usable in proofs from other modules. -/
def findFieldWithResolvedSlotCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (Field × Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
    if field.name == name then some (field, field.slot.getD idx)
    else findFieldWithResolvedSlotCopyFrom rest (idx + 1) name

/-- Standalone copy of `findFieldByName.go` for write slots, usable in proofs from other modules. -/
def findFieldWriteSlotsCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (List Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
    if field.name == name then some (field.slot.getD idx :: field.aliasSlots)
    else findFieldWriteSlotsCopyFrom rest (idx + 1) name

theorem findFieldWithResolvedSlot_eq_CopyFrom
    (flds : List Field) (nm : String) :
    findFieldWithResolvedSlot flds nm =
      findFieldWithResolvedSlotCopyFrom flds 0 nm := by
  suffices ∀ idx, findFieldByName.go nm (fun f slot => (f, slot)) flds idx =
      findFieldWithResolvedSlotCopyFrom flds idx nm from this 0
  intro idx
  induction flds generalizing idx with
  | nil => rfl
  | cons hd tl ih =>
    simp [findFieldByName.go, findFieldWithResolvedSlotCopyFrom]
    split <;> simp_all

theorem findFieldWriteSlots_eq_CopyFrom
    (flds : List Field) (nm : String) :
    findFieldWriteSlots flds nm =
      findFieldWriteSlotsCopyFrom flds 0 nm := by
  suffices ∀ idx, findFieldByName.go nm (fun f slot => slot :: f.aliasSlots) flds idx =
      findFieldWriteSlotsCopyFrom flds idx nm from this 0
  intro idx
  induction flds generalizing idx with
  | nil => rfl
  | cons hd tl ih =>
    simp [findFieldByName.go, findFieldWriteSlotsCopyFrom]
    split <;> simp_all

def mappingTypeKeyTypes : MappingType → List MappingKeyType
  | .simple keyType => [keyType]
  | .nested outerKey innerKey => [outerKey, innerKey]
  | .chain keyTypes => keyTypes

def mappingTypeDepth (mt : MappingType) : Nat :=
  mt |> mappingTypeKeyTypes |> List.length

-- Helper: Is field a mapping?
def isMapping (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.dynamicArray _ => false
    | FieldType.mappingTyped _ => true
    | FieldType.mappingStruct _ _ => true
    | FieldType.mappingStruct2 _ _ _ => true
    | _ => false

theorem isMapping_false_of_findFieldWithResolvedSlot_address
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (hty : f.ty = FieldType.address) :
    isMapping fields name = false := by
  unfold isMapping
  have hfound : fields.find? (·.name == name) = some f := by
    unfold findFieldWithResolvedSlot at hfind
    unfold findFieldByName at hfind
    exact find_eq_of_findFieldByName_go hfind
  rw [hfound]
  simp [Option.any, hty]

theorem isMapping_false_of_findFieldWithResolvedSlot_uint256
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (hty : f.ty = FieldType.uint256) :
    isMapping fields name = false := by
  unfold isMapping
  have hfound : fields.find? (·.name == name) = some f := by
    unfold findFieldWithResolvedSlot at hfind
    unfold findFieldByName at hfind
    exact find_eq_of_findFieldByName_go hfind
  rw [hfound]
  simp [Option.any, hty]

-- Helper: Is field a double mapping?
def isMapping2 (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.dynamicArray _ => false
    | FieldType.mappingTyped mt => mappingTypeDepth mt == 2
    | FieldType.mappingStruct2 _ _ _ => true
    | _ => false

-- Helper: Find struct members for a struct-valued mapping field.
def findStructMembers (fields : List Field) (name : String) : Option (List StructMember) :=
  fields.find? (·.name == name) |>.bind fun f =>
    match f.ty with
    | FieldType.mappingStruct _ members => some members
    | FieldType.mappingStruct2 _ _ members => some members
    | _ => none

-- Helper: Look up a named struct member from the members list.
def findStructMember (members : List StructMember) (memberName : String) : Option StructMember :=
  members.find? (·.name == memberName)


end Compiler.CompilationModel
