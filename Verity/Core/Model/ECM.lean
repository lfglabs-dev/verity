/-
  Compiler.ECM: External Call Module Framework

  External Call Modules (ECMs) package reusable external call patterns
  (ERC-20 transfers, precompile calls, callbacks, etc.) as typed, auditable
  Lean structures that the compiler can plug in without modification.

  Standard modules ship in `Compiler/Modules/`. Third parties can publish
  their own as separate Lean packages.

  See: #964
-/

import Verity.Core.Model.Constants
import Verity.Core.Model.ProofStatus
import Verity.Core.Model.Yul.Ast

namespace Compiler.ECM

open Compiler.Yul
open Compiler.Constants (errorStringSelectorWord addressMask)

namespace StatefulExternal

/-- Call mutability at the external-world boundary. `staticcall` summaries are
    interpreted with an unchanged external world. -/
inductive Mutability where
  | call
  | staticcall
  deriving Repr, BEq

def Mutability.toJsonString : Mutability → String
  | .call => "call"
  | .staticcall => "staticcall"

/-- Abstract state for contracts outside the current caller. The first index is
    the account address and the second index is that account's modeled slot. -/
structure ExternalWorld where
  accountState : Nat → Nat → Nat := fun _ _ => 0

/-- Caller-visible request sent to an external contract summary. -/
structure Request where
  caller : Nat
  target : Nat
  selector : Option Nat
  calldata : List Nat
  value : Nat
  world : ExternalWorld

/-- Successful calls commit an external world and returndata. Reverting calls
    expose revert data but do not commit a caller continuation. -/
inductive Outcome where
  | success (world : ExternalWorld) (returndata : List Nat)
  | revert (revertData : List Nat)

namespace Outcome

def returndata : Outcome → List Nat
  | .success _ data => data
  | .revert data => data

def committedWorld? : Outcome → Option ExternalWorld
  | .success world _ => some world
  | .revert _ => none

@[simp] theorem committedWorld?_revert (data : List Nat) :
    (Outcome.revert data).committedWorld? = none := rfl

end Outcome

/-- Interface summary for an external contract interaction. The executable
    semantics quantifies over this relation instead of treating the callee as a
    pure oracle. -/
structure Summary where
  name : String
  selector : Option Nat := none
  mutability : Mutability
  assumptionNames : List String := []
  pre : Request → Prop := fun _ => True
  post : Request → ExternalWorld → List Nat → Prop := fun _ _ _ => True
  revert : Request → List Nat → Prop := fun _ _ => True

instance : Repr Summary where
  reprPrec summary prec :=
    reprPrec
      (summary.name, summary.selector, summary.mutability, summary.assumptionNames)
      prec

def Summary.interprets (summary : Summary) (request : Request) (outcome : Outcome) : Prop :=
  summary.pre request ∧
    match outcome with
    | .success world data =>
        summary.post request world data ∧
          (summary.mutability = .staticcall → world = request.world)
    | .revert data =>
        summary.revert request data

theorem Summary.static_success_preserves_world
    {summary : Summary} {request : Request} {world : ExternalWorld} {data : List Nat}
    (hstatic : summary.mutability = .staticcall)
    (hinterp : summary.interprets request (.success world data)) :
    world = request.world := by
  exact hinterp.2.2 hstatic

theorem Summary.revert_has_no_committed_world
    (data : List Nat) :
    (Outcome.revert data).committedWorld? = none := rfl

end StatefulExternal

/-- Context provided to ECM compile functions beyond the argument expressions.
    This gives modules access to compiler services without coupling them to
    the full CompilationModel compilation pipeline. -/
structure CompilationContext where
  /-- Whether dynamic data comes from calldata (external functions) or memory (internal). -/
  isDynamicFromCalldata : Bool := true

/-- Data-only external transport that has canonical compilation/denotation.
Tagged modules do not execute an arbitrary compilation closure. -/
inductive ByteTransport where
  | staticUint256 (resultVar : String) (selector numStaticArgs : Nat)
  | staticBool (resultVar : String) (selector numStaticArgs : Nat)
  | staticBytesUint256 (resultVar : String) (selector : Nat)
  | staticBytesBool (resultVar : String) (selector : Nat)
  /-- `resultVar := create2(value, offset, size, salt)` over physical memory. -/
  | create2 (resultVar : String)
  /-- `log{topicCount}(offset, size, topics...)` of an ABI-encoded event payload. -/
  | log (eventName : String) (topicCount : Nat)
  /-- Value-free low-level `CALL` of `selector ++ words` whose returndata is
  checked by the optional-bool convention (empty, or a valid ABI `bool`). -/
  | optionalBoolCall (resultVar : String) (selector numWordArgs : Nat)
  | callBytesUint256 (resultVar : String) (selector : Nat)
  | callBytesBool (resultVar : String) (selector : Nat)
  /-- `resultVar := extcodesize(target)`: the runtime code length of an account. -/
  | extCodeSize (resultVar : String)
  /-- `resultVar := <target>.code`: `extcodesize` then `extcodecopy` of the runtime
  code into a fresh `bytes memory` allocation (length word, then the bytes). -/
  | extCodeCopy (resultVar : String)
  /-- `return(offset, size)` of an ABI-encoded memory buffer, ending the frame. -/
  | returnMemory
  deriving DecidableEq, Repr

/-- An External Call Module packages a reusable external call pattern.
    Module authors provide the compilation logic; the compiler provides
    the generic framework for validation, compilation, and verification. -/
structure ExternalCallModule where
  /-- Human-readable name, used in error messages and audit reports. -/
  name : String

  /-- Number of Expr arguments this module expects.
      The compiler validates argument count before calling `compile`. -/
  numArgs : Nat

  /-- Local variables this module binds (e.g., ecrecover binds a result address).
      Empty for fire-and-forget patterns like safeTransfer. -/
  resultVars : List String := []

  /-- Does this pattern write to storage or make state-changing calls?
      If true, it cannot appear in view or pure functions. -/
  writesState : Bool

  /-- Does this pattern read storage or environment variables?
      If true, it cannot appear in pure functions. -/
  readsState : Bool

  /-- Compilation function. Takes a compilation context and compiled argument
      expressions (YulExpr) and produces the Yul statement sequence implementing
      this pattern. Returns Except so modules can report argument errors. -/
  compile : CompilationContext → List YulExpr → Except String (List YulStmt)

  /-- Optional closed byte transport; its descriptor governs execution and
      compilation, independently of the opaque legacy compilation closure. -/
  byteTransport : Option ByteTransport := none

  /-- Trust assumptions. Surfaced in compilation reports and aggregated
      across all modules used by a contract. -/
  axioms : List String := []

  /-- Proof-accounting status for this module's behavior. -/
  proofStatus : Compiler.ProofStatus := .assumed

  /-- Stable name for the stateful external-world summary associated with this
      ECM. Defaults to the module name so every typed ECM has a reportable
      summary without duplicating boilerplate in module definitions. -/
  summaryName : String := name

  /-- Optional ABI selector described by the external summary. Generic modules
      that close over a selector can override this, while dynamic wrappers may
      leave it unknown. -/
  summarySelector : Option Nat := none

  /-- Whether the summary is interpreted as a mutable call or staticcall. The
      default mirrors the existing `writesState` gate. -/
  summaryMutability : StatefulExternal.Mutability :=
    if writesState then .call else .staticcall

  /-- Optional 0-based index into `args` carrying the callee target address
      for `CallSite.target` at the `ecmCall*` / `ecmDo` boundary. Defaults to
      `none` (`target = 0`) so modules without an address argument remain
      backwards-compatible. -/
  targetArg : Option Nat := none

  /-- Optional 0-based index into `args` carrying the ETH value (in wei)
      transferred by a `.call` at the `ecmCall*` / `ecmDo` boundary. When set,
      `ecmCall*` / `ecmDo` populates `CallSite.value` and debits `selfBalance`
      via `debitSelfBalance` before running `commonExternalCall` (reverting on
      insufficient balance and rolling back the debit if the call fails). -/
  valueArg : Option Nat := none

instance : BEq ExternalCallModule where
  beq a b :=
    (a.numArgs == b.numArgs) &&
    ((a.byteTransport == b.byteTransport) &&
    ((a.resultVars == b.resultVars) &&
    ((a.summarySelector == b.summarySelector) &&
    ((a.name == b.name) &&
    ((a.writesState == b.writesState) &&
    ((a.readsState == b.readsState) &&
    ((a.axioms == b.axioms) &&
    ((a.proofStatus == b.proofStatus) &&
    ((a.summaryName == b.summaryName) &&
    ((a.summaryMutability == b.summaryMutability) &&
    ((a.targetArg == b.targetArg) &&
    (a.valueArg == b.valueArg))))))))))))

instance : Repr ExternalCallModule where
  reprPrec m _ := s!"ECM[{m.name}]"

instance : ToString ExternalCallModule where
  toString m := s!"ECM[{m.name}]"

namespace ExternalCallModule

/-- Derive the semantic external-world summary carried by an ECM. Standard ECMs
    use permissive pre/post relations for now; downstream proofs can refine the
    relation while trust reports still expose the assumed boundary uniformly. -/
def externalSummary (mod : ExternalCallModule) : StatefulExternal.Summary :=
  { name := mod.summaryName
    selector := mod.summarySelector
    mutability := mod.summaryMutability
    assumptionNames := mod.axioms }

end ExternalCallModule

namespace SolidityStaticCall

/-- All free variable references in a transport expression. -/
def argumentNames : YulExpr → List String
  | .ident name => [name]
  | .call _ args => args.flatMap argumentNames
  | _ => []

/-- Scratch locals cannot capture source arguments. Normal transports retain
stable names; a collision gets a name longer than every occupied identifier. -/
def scratchName (base : String) (occupied : List String) : String :=
  if occupied.contains base then
    base ++ String.ofList (List.replicate
      (occupied.foldl (fun longest name => max longest name.length) 0 + 1) '_')
  else base

def compileUint256 (resultVar : String) (selector numStaticArgs : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity staticcall selector exceeds four bytes"
  unless args.length == numStaticArgs + 1 do
    throw "Solidity staticcall argument count differs"
  let target ← match args.head? with
    | some value => pure value
    | none => throw "Solidity staticcall target is missing"
  let occupied := resultVar :: args.flatMap argumentNames
  let ptrName := scratchName "__solidity_static_ptr" occupied
  let successName := scratchName "__solidity_static_success" (ptrName :: occupied)
  let sizeName := scratchName "__solidity_static_size" (successName :: ptrName :: occupied)
  let ptr := YulExpr.ident ptrName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  let dataSize := 4 + numStaticArgs * 32
  let allocation := ((dataSize + 31) / 32) * 32
  let stores := (args.drop 1).zipIdx.map fun (value, index) =>
    YulStmt.exprStmt (.call "mstore" [
      .call "add" [ptr, .lit (4 + index * 32)], value])
  return [
    .let_ resultVar (.lit 0),
    .block (
      [.let_ ptrName (.call "mload" [.lit 64]),
       .exprStmt (.call "mstore" [ptr, .call "shl" [.lit 224, .hex selector]])] ++ stores ++
      [.exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, .lit allocation]]),
       .let_ successName (.call "staticcall" [
         .call "gas" [], target, ptr, .lit dataSize, ptr, .lit 32]),
       .let_ sizeName (.call "returndatasize" []),
       .if_ (.call "iszero" [success]) [
         .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
         .exprStmt (.call "revert" [.lit 0, size])],
       .if_ (.call "lt" [size, .lit 32]) [
         .exprStmt (.call "revert" [.lit 0, .lit 0])],
       .assign resultVar (.call "mload" [ptr])])]

def uint256Module (resultVar : String) (selector numStaticArgs : Nat) :
    ExternalCallModule where
  name := "solidityStaticUint256"
  numArgs := numStaticArgs + 1
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compileUint256 resultVar selector numStaticArgs args
  byteTransport := some (.staticUint256 resultVar selector numStaticArgs)
  axioms := []
  -- Compilation transport is differentially tested; no Yul equivalence proof
  -- is claimed by this development module.
  proofStatus := .assumed
  summaryName := "solidity_static_uint256_byte_response"
  summarySelector := some selector
  summaryMutability := .staticcall

def compileBool (resultVar : String) (selector numStaticArgs : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity staticcall selector exceeds four bytes"
  unless args.length == numStaticArgs + 1 do
    throw "Solidity staticcall argument count differs"
  let target ← match args.head? with
    | some value => pure value
    | none => throw "Solidity staticcall target is missing"
  let occupied := resultVar :: args.flatMap argumentNames
  let ptrName := scratchName "__solidity_static_ptr" occupied
  let successName := scratchName "__solidity_static_success" (ptrName :: occupied)
  let sizeName := scratchName "__solidity_static_size" (successName :: ptrName :: occupied)
  let wordName := scratchName "__solidity_static_word"
    (sizeName :: successName :: ptrName :: occupied)
  let ptr := YulExpr.ident ptrName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  let word := YulExpr.ident wordName
  let dataSize := 4 + numStaticArgs * 32
  let allocation := ((dataSize + 31) / 32) * 32
  let stores := (args.drop 1).zipIdx.map fun (value, index) =>
    YulStmt.exprStmt (.call "mstore" [
      .call "add" [ptr, .lit (4 + index * 32)], value])
  return [
    .let_ resultVar (.lit 0),
    .block (
      [.let_ ptrName (.call "mload" [.lit 64]),
       .exprStmt (.call "mstore" [ptr, .call "shl" [.lit 224, .hex selector]])] ++ stores ++
      [.exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, .lit allocation]]),
       .let_ successName (.call "staticcall" [
         .call "gas" [], target, ptr, .lit dataSize, ptr, .lit 32]),
       .let_ sizeName (.call "returndatasize" []),
       .if_ (.call "iszero" [success]) [
         .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
         .exprStmt (.call "revert" [.lit 0, size])],
       .if_ (.call "lt" [size, .lit 32]) [
         .exprStmt (.call "revert" [.lit 0, .lit 0])],
       .let_ wordName (.call "mload" [ptr]),
       .if_ (.call "gt" [word, .lit 1]) [
         .exprStmt (.call "revert" [.lit 0, .lit 0])],
       .assign resultVar word])]

def boolModule (resultVar : String) (selector numStaticArgs : Nat) :
    ExternalCallModule where
  name := "solidityStaticBool"
  numArgs := numStaticArgs + 1
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compileBool resultVar selector numStaticArgs args
  byteTransport := some (.staticBool resultVar selector numStaticArgs)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_static_bool_byte_response"
  summarySelector := some selector
  summaryMutability := .staticcall

/-- Copy `[srcPtr, srcPtr + srcSize)` into `[ptr + 4, ptr + 4 + srcSize)` in an
overlap-safe direction (forward when `ptr + 4 < srcPtr`, backward otherwise) and
then write the 4-byte selector at `[ptr, ptr + 4)` without disturbing the copied
payload bytes at `[ptr + 4, ptr + 32)`. -/
def copySelectorAndPayload (selector : Nat) (ptr srcPtr srcSize : YulExpr)
    (indexName : String) : List YulStmt :=
  let index := YulExpr.ident indexName
  let dest := YulExpr.call "add" [ptr, .lit 4]
  let alignedSize := YulExpr.call "and" [.call "add" [srcSize, .lit 31], .call "not" [.lit 31]]
  let prevIndex := YulExpr.call "sub" [index, .lit 32]
  [ .if_ (.call "lt" [dest, srcPtr]) [
      .for_ [.let_ indexName (.lit 0)] (.call "lt" [index, srcSize])
        [.assign indexName (.call "add" [index, .lit 32])]
        [.exprStmt (.call "mstore" [
          .call "add" [dest, index],
          .call "mload" [.call "add" [srcPtr, index]]])]],
    .if_ (.call "iszero" [.call "lt" [dest, srcPtr]]) [
      .for_ [.let_ indexName alignedSize] (.call "gt" [index, .lit 0])
        [.assign indexName prevIndex]
        [.exprStmt (.call "mstore" [
          .call "add" [dest, prevIndex],
          .call "mload" [.call "add" [srcPtr, prevIndex]]])]],
    .exprStmt (.call "mstore" [
      ptr,
      .call "or" [
        .call "shl" [.lit 224, .hex selector],
        .call "shr" [.lit 32, .call "mload" [dest]]]]) ]

def compileBytesUint256 (resultVar : String) (selector : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity staticcall selector exceeds four bytes"
  let [target, payloadPtr, payloadSize] := args
    | throw "Solidity bytes staticcall expects target, offset and size"
  let occupied := resultVar :: args.flatMap argumentNames
  let targetName := scratchName "__solidity_static_target" occupied
  let srcPtrName := scratchName "__solidity_static_src_ptr" (targetName :: occupied)
  let srcSizeName := scratchName "__solidity_static_src_size" (srcPtrName :: targetName :: occupied)
  let baseOccupied := srcSizeName :: srcPtrName :: targetName :: occupied
  let ptrName := scratchName "__solidity_static_ptr" baseOccupied
  let dataSizeName := scratchName "__solidity_static_data_size" (ptrName :: baseOccupied)
  let allocName := scratchName "__solidity_static_alloc" (dataSizeName :: ptrName :: baseOccupied)
  let indexName := scratchName "__solidity_static_idx"
    (allocName :: dataSizeName :: ptrName :: baseOccupied)
  let successName := scratchName "__solidity_static_success"
    (indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let sizeName := scratchName "__solidity_static_size"
    (successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let targetVal := YulExpr.ident targetName
  let srcPtr := YulExpr.ident srcPtrName
  let srcSize := YulExpr.ident srcSizeName
  let ptr := YulExpr.ident ptrName
  let dataSize := YulExpr.ident dataSizeName
  let alloc := YulExpr.ident allocName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  return [
    .let_ resultVar (.lit 0),
    .block (
      [ .let_ targetName target,
        .let_ srcPtrName payloadPtr,
        .let_ srcSizeName payloadSize,
        .let_ ptrName (.call "mload" [.lit 64]),
        .let_ dataSizeName (.call "add" [srcSize, .lit 4]),
        .let_ allocName (.call "and" [.call "add" [dataSize, .lit 31], .call "not" [.lit 31]]) ] ++
      copySelectorAndPayload selector ptr srcPtr srcSize indexName ++
      [ .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, alloc]]),
        .let_ successName (.call "staticcall" [
          .call "gas" [], targetVal, ptr, dataSize, ptr, .lit 32]),
        .let_ sizeName (.call "returndatasize" []),
        .if_ (.call "iszero" [success]) [
          .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
          .exprStmt (.call "revert" [.lit 0, size])],
        .if_ (.call "lt" [size, .lit 32]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .assign resultVar (.call "mload" [ptr])])]

def bytesUint256Module (resultVar : String) (selector : Nat) :
    ExternalCallModule where
  name := "solidityStaticBytesUint256"
  numArgs := 3
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compileBytesUint256 resultVar selector args
  byteTransport := some (.staticBytesUint256 resultVar selector)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_static_bytes_uint256_byte_response"
  summarySelector := some selector
  summaryMutability := .staticcall

def compileBytesBool (resultVar : String) (selector : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity staticcall selector exceeds four bytes"
  let [target, payloadPtr, payloadSize] := args
    | throw "Solidity bytes staticcall expects target, offset and size"
  let occupied := resultVar :: args.flatMap argumentNames
  let targetName := scratchName "__solidity_static_target" occupied
  let srcPtrName := scratchName "__solidity_static_src_ptr" (targetName :: occupied)
  let srcSizeName := scratchName "__solidity_static_src_size" (srcPtrName :: targetName :: occupied)
  let baseOccupied := srcSizeName :: srcPtrName :: targetName :: occupied
  let ptrName := scratchName "__solidity_static_ptr" baseOccupied
  let dataSizeName := scratchName "__solidity_static_data_size" (ptrName :: baseOccupied)
  let allocName := scratchName "__solidity_static_alloc" (dataSizeName :: ptrName :: baseOccupied)
  let indexName := scratchName "__solidity_static_idx"
    (allocName :: dataSizeName :: ptrName :: baseOccupied)
  let successName := scratchName "__solidity_static_success"
    (indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let sizeName := scratchName "__solidity_static_size"
    (successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let wordName := scratchName "__solidity_static_word"
    (sizeName :: successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let targetVal := YulExpr.ident targetName
  let srcPtr := YulExpr.ident srcPtrName
  let srcSize := YulExpr.ident srcSizeName
  let ptr := YulExpr.ident ptrName
  let dataSize := YulExpr.ident dataSizeName
  let alloc := YulExpr.ident allocName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  let word := YulExpr.ident wordName
  return [
    .let_ resultVar (.lit 0),
    .block (
      [ .let_ targetName target,
        .let_ srcPtrName payloadPtr,
        .let_ srcSizeName payloadSize,
        .let_ ptrName (.call "mload" [.lit 64]),
        .let_ dataSizeName (.call "add" [srcSize, .lit 4]),
        .let_ allocName (.call "and" [.call "add" [dataSize, .lit 31], .call "not" [.lit 31]]) ] ++
      copySelectorAndPayload selector ptr srcPtr srcSize indexName ++
      [ .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, alloc]]),
        .let_ successName (.call "staticcall" [
          .call "gas" [], targetVal, ptr, dataSize, ptr, .lit 32]),
        .let_ sizeName (.call "returndatasize" []),
        .if_ (.call "iszero" [success]) [
          .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
          .exprStmt (.call "revert" [.lit 0, size])],
        .if_ (.call "lt" [size, .lit 32]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .let_ wordName (.call "mload" [ptr]),
        .if_ (.call "gt" [word, .lit 1]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .assign resultVar word])]

def bytesBoolModule (resultVar : String) (selector : Nat) :
    ExternalCallModule where
  name := "solidityStaticBytesBool"
  numArgs := 3
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compileBytesBool resultVar selector args
  byteTransport := some (.staticBytesBool resultVar selector)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_static_bytes_bool_byte_response"
  summarySelector := some selector
  summaryMutability := .staticcall


end SolidityStaticCall

namespace SolidityCreate2

/-- `create2` with the value, initcode offset, initcode size and salt in
argument order. Callers pass atoms, so Yul's right-to-left evaluation of the
builtin arguments is unobservable. -/
def compile (resultVar : String) (args : List YulExpr) : Except String (List YulStmt) :=
  match args with
  | [value, offset, size, salt] =>
      pure [.let_ resultVar (.call "create2" [value, offset, size, salt])]
  | _ => throw "Solidity create2 expects value, offset, size and salt"

def module (resultVar : String) : ExternalCallModule where
  name := "solidityCreate2"
  numArgs := 4
  resultVars := [resultVar]
  writesState := true
  readsState := true
  compile := fun _ args => compile resultVar args
  byteTransport := some (.create2 resultVar)
  axioms := []
  -- Compilation transport is differentially tested; Denote executes only the
  -- checked initcode templates of `DenoteCreate2`.
  proofStatus := .assumed
  summaryName := "solidity_create2_checked_initcode"
  summaryMutability := .call

end SolidityCreate2

namespace SolidityLog

/-- `log{n}` of the memory payload `[offset, offset + size)`. The arguments are
the `n` topics followed by the payload offset and size. -/
def compile (topicCount : Nat) (args : List YulExpr) : Except String (List YulStmt) := do
  unless topicCount ≤ 4 do throw "Solidity event logs carry at most four topics"
  unless args.length == topicCount + 2 do throw "Solidity event log argument count differs"
  let topics := args.take topicCount
  match args.drop topicCount with
  | [offset, size] => pure [.exprStmt (.call s!"log{topicCount}" ([offset, size] ++ topics))]
  | _ => throw "Solidity event log payload is missing"

def module (eventName : String) (topicCount : Nat) : ExternalCallModule where
  name := "solidityLog"
  numArgs := topicCount + 2
  resultVars := []
  writesState := true
  readsState := false
  compile := fun _ args => compile topicCount args
  byteTransport := some (.log eventName topicCount)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_event_log"
  -- A log hands control to no account.
  summaryMutability := .staticcall

end SolidityLog

namespace SolidityLowLevelCall

/-- `(bool success, bytes memory returndata) = target.call(abi.encodeCall(f, (words...)))`
followed by `if (!success)` forwarding of the complete returndata and the
optional-bool check `returndata.length == 0 || abi.decode(returndata, (bool))`.
The calldata is written at the free pointer, which is advanced past it after the
call (a free pointer word inside the calldata area is then irrelevant). A failed
child forwards its returndata; empty returndata binds `1`; a non-empty response
shorter than a word or whose first word is not a valid `bool` reverts with no
data; otherwise the decoded `bool` is bound. The caller's own error for a decoded
`false` is a separate `require` on the result. -/
def compileOptionalBool (resultVar : String) (selector numWordArgs : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity low-level call selector exceeds four bytes"
  unless args.length == numWordArgs + 1 do
    throw "Solidity low-level call argument count differs"
  let target ← match args.head? with
    | some value => pure value
    | none => throw "Solidity low-level call target is missing"
  let occupied := resultVar :: args.flatMap SolidityStaticCall.argumentNames
  let ptrName := SolidityStaticCall.scratchName "__solidity_call_ptr" occupied
  let successName := SolidityStaticCall.scratchName "__solidity_call_success" (ptrName :: occupied)
  let sizeName := SolidityStaticCall.scratchName "__solidity_call_size"
    (successName :: ptrName :: occupied)
  let wordName := SolidityStaticCall.scratchName "__solidity_call_word"
    (sizeName :: successName :: ptrName :: occupied)
  let ptr := YulExpr.ident ptrName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  let word := YulExpr.ident wordName
  let dataSize := 4 + numWordArgs * 32
  let allocation := ((dataSize + 31) / 32) * 32
  let stores := (args.drop 1).zipIdx.map fun (value, index) =>
    YulStmt.exprStmt (.call "mstore" [
      .call "add" [ptr, .lit (4 + index * 32)], value])
  return [
    .let_ resultVar (.lit 0),
    .block (
      [.let_ ptrName (.call "mload" [.lit 64]),
       .exprStmt (.call "mstore" [ptr, .call "shl" [.lit 224, .hex selector]])] ++ stores ++
      [.let_ successName (.call "call" [
         .call "gas" [], target, .lit 0, ptr, .lit dataSize, .lit 0, .lit 0]),
       .let_ sizeName (.call "returndatasize" []),
       .if_ (.call "iszero" [success]) [
         .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
         .exprStmt (.call "revert" [.lit 0, size])],
       .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, .lit allocation]]),
       .switch size [(0, [.assign resultVar (.lit 1)])] (some [
         .if_ (.call "lt" [size, .lit 32]) [
           .exprStmt (.call "revert" [.lit 0, .lit 0])],
         .exprStmt (.call "returndatacopy" [ptr, .lit 0, .lit 32]),
         .let_ wordName (.call "mload" [ptr]),
         .if_ (.call "gt" [word, .lit 1]) [
           .exprStmt (.call "revert" [.lit 0, .lit 0])],
         .assign resultVar word])])]

def optionalBoolModule (resultVar : String) (selector numWordArgs : Nat) :
    ExternalCallModule where
  name := "solidityLowLevelOptionalBoolCall"
  numArgs := numWordArgs + 1
  resultVars := [resultVar]
  writesState := true
  readsState := true
  compile := fun _ args => compileOptionalBool resultVar selector numWordArgs args
  byteTransport := some (.optionalBoolCall resultVar selector numWordArgs)
  axioms := []
  -- Compilation transport is differentially tested; Denote runs the request
  -- against the explicit byte-call adversary.
  proofStatus := .assumed
  summaryName := "solidity_low_level_optional_bool_call"
  summarySelector := some selector
  summaryMutability := .call

def compileBytesUint256 (resultVar : String) (selector : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity low-level call selector exceeds four bytes"
  let [target, payloadPtr, payloadSize] := args
    | throw "Solidity bytes call expects target, offset and size"
  let occupied := resultVar :: args.flatMap SolidityStaticCall.argumentNames
  let targetName := SolidityStaticCall.scratchName "__solidity_call_target" occupied
  let srcPtrName := SolidityStaticCall.scratchName "__solidity_call_src_ptr" (targetName :: occupied)
  let srcSizeName := SolidityStaticCall.scratchName "__solidity_call_src_size" (srcPtrName :: targetName :: occupied)
  let baseOccupied := srcSizeName :: srcPtrName :: targetName :: occupied
  let ptrName := SolidityStaticCall.scratchName "__solidity_call_ptr" baseOccupied
  let dataSizeName := SolidityStaticCall.scratchName "__solidity_call_data_size" (ptrName :: baseOccupied)
  let allocName := SolidityStaticCall.scratchName "__solidity_call_alloc" (dataSizeName :: ptrName :: baseOccupied)
  let indexName := SolidityStaticCall.scratchName "__solidity_call_idx"
    (allocName :: dataSizeName :: ptrName :: baseOccupied)
  let successName := SolidityStaticCall.scratchName "__solidity_call_success"
    (indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let sizeName := SolidityStaticCall.scratchName "__solidity_call_size"
    (successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let targetVal := YulExpr.ident targetName
  let srcPtr := YulExpr.ident srcPtrName
  let srcSize := YulExpr.ident srcSizeName
  let ptr := YulExpr.ident ptrName
  let dataSize := YulExpr.ident dataSizeName
  let alloc := YulExpr.ident allocName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  return [
    .let_ resultVar (.lit 0),
    .block (
      [ .let_ targetName target,
        .let_ srcPtrName payloadPtr,
        .let_ srcSizeName payloadSize,
        .let_ ptrName (.call "mload" [.lit 64]),
        .let_ dataSizeName (.call "add" [srcSize, .lit 4]),
        .let_ allocName (.call "and" [.call "add" [dataSize, .lit 31], .call "not" [.lit 31]]) ] ++
      SolidityStaticCall.copySelectorAndPayload selector ptr srcPtr srcSize indexName ++
      [ .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, alloc]]),
        .let_ successName (.call "call" [
          .call "gas" [], targetVal, .lit 0, ptr, dataSize, ptr, .lit 32]),
        .let_ sizeName (.call "returndatasize" []),
        .if_ (.call "iszero" [success]) [
          .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
          .exprStmt (.call "revert" [.lit 0, size])],
        .if_ (.call "lt" [size, .lit 32]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .assign resultVar (.call "mload" [ptr])])]

def bytesUint256Module (resultVar : String) (selector : Nat) :
    ExternalCallModule where
  name := "solidityCallBytesUint256"
  numArgs := 3
  resultVars := [resultVar]
  writesState := true
  readsState := true
  compile := fun _ args => compileBytesUint256 resultVar selector args
  byteTransport := some (.callBytesUint256 resultVar selector)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_call_bytes_uint256_byte_response"
  summarySelector := some selector
  summaryMutability := .call

def compileBytesBool (resultVar : String) (selector : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless selector < 2^32 do throw "Solidity low-level call selector exceeds four bytes"
  let [target, payloadPtr, payloadSize] := args
    | throw "Solidity bytes call expects target, offset and size"
  let occupied := resultVar :: args.flatMap SolidityStaticCall.argumentNames
  let targetName := SolidityStaticCall.scratchName "__solidity_call_target" occupied
  let srcPtrName := SolidityStaticCall.scratchName "__solidity_call_src_ptr" (targetName :: occupied)
  let srcSizeName := SolidityStaticCall.scratchName "__solidity_call_src_size" (srcPtrName :: targetName :: occupied)
  let baseOccupied := srcSizeName :: srcPtrName :: targetName :: occupied
  let ptrName := SolidityStaticCall.scratchName "__solidity_call_ptr" baseOccupied
  let dataSizeName := SolidityStaticCall.scratchName "__solidity_call_data_size" (ptrName :: baseOccupied)
  let allocName := SolidityStaticCall.scratchName "__solidity_call_alloc" (dataSizeName :: ptrName :: baseOccupied)
  let indexName := SolidityStaticCall.scratchName "__solidity_call_idx"
    (allocName :: dataSizeName :: ptrName :: baseOccupied)
  let successName := SolidityStaticCall.scratchName "__solidity_call_success"
    (indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let sizeName := SolidityStaticCall.scratchName "__solidity_call_size"
    (successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let wordName := SolidityStaticCall.scratchName "__solidity_call_word"
    (sizeName :: successName :: indexName :: allocName :: dataSizeName :: ptrName :: baseOccupied)
  let targetVal := YulExpr.ident targetName
  let srcPtr := YulExpr.ident srcPtrName
  let srcSize := YulExpr.ident srcSizeName
  let ptr := YulExpr.ident ptrName
  let dataSize := YulExpr.ident dataSizeName
  let alloc := YulExpr.ident allocName
  let success := YulExpr.ident successName
  let size := YulExpr.ident sizeName
  let word := YulExpr.ident wordName
  return [
    .let_ resultVar (.lit 0),
    .block (
      [ .let_ targetName target,
        .let_ srcPtrName payloadPtr,
        .let_ srcSizeName payloadSize,
        .let_ ptrName (.call "mload" [.lit 64]),
        .let_ dataSizeName (.call "add" [srcSize, .lit 4]),
        .let_ allocName (.call "and" [.call "add" [dataSize, .lit 31], .call "not" [.lit 31]]) ] ++
      SolidityStaticCall.copySelectorAndPayload selector ptr srcPtr srcSize indexName ++
      [ .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, alloc]]),
        .let_ successName (.call "call" [
          .call "gas" [], targetVal, .lit 0, ptr, dataSize, ptr, .lit 32]),
        .let_ sizeName (.call "returndatasize" []),
        .if_ (.call "iszero" [success]) [
          .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, size]),
          .exprStmt (.call "revert" [.lit 0, size])],
        .if_ (.call "lt" [size, .lit 32]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .let_ wordName (.call "mload" [ptr]),
        .if_ (.call "gt" [word, .lit 1]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .assign resultVar word])]

def bytesBoolModule (resultVar : String) (selector : Nat) :
    ExternalCallModule where
  name := "solidityCallBytesBool"
  numArgs := 3
  resultVars := [resultVar]
  writesState := true
  readsState := true
  compile := fun _ args => compileBytesBool resultVar selector args
  byteTransport := some (.callBytesBool resultVar selector)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_call_bytes_bool_byte_response"
  summarySelector := some selector
  summaryMutability := .call

end SolidityLowLevelCall

namespace SolidityExtCodeSize

/-- `<address>.code.length`, i.e. `extcodesize(target)` of an atomic target. -/
def compile (resultVar : String) (args : List YulExpr) : Except String (List YulStmt) :=
  match args with
  | [target] => pure [.let_ resultVar (.call "extcodesize" [target])]
  | _ => throw "Solidity code length expects one target"

def module (resultVar : String) : ExternalCallModule where
  name := "solidityExtCodeSize"
  numArgs := 1
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compile resultVar args
  byteTransport := some (.extCodeSize resultVar)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_external_code_size"
  -- Reading code hands control to no account.
  summaryMutability := .staticcall

end SolidityExtCodeSize

namespace SolidityExtCodeCopy

/-- Solidity's `Panic(0x41)` allocation failure. -/
def panicAllocation : List YulStmt :=
  [.exprStmt (.call "mstore" [.lit 0, .call "shl" [.lit 224, .hex 0x4e487b71]]),
   .exprStmt (.call "mstore" [.lit 4, .lit 0x41]),
   .exprStmt (.call "revert" [.lit 0, .lit 0x24])]

/-- `<address>.code` of an atomic target, as solc's `external_code_at`: the
length is `extcodesize`, a `bytes memory` array of that length is allocated at
the free pointer (`Panic(0x41)` when the length or the new free pointer exceeds
64 bits or wraps), the length word is stored and the code is copied after it.
`resultVar` is the array pointer. -/
def compile (resultVar : String) (args : List YulExpr) : Except String (List YulStmt) := do
  let target ← match args with
    | [target] => pure target
    | _ => throw "Solidity external code expects one target"
  let occupied := resultVar :: SolidityStaticCall.argumentNames target
  let sizeName := SolidityStaticCall.scratchName "__solidity_code_size" occupied
  let nextName := SolidityStaticCall.scratchName "__solidity_code_next" (sizeName :: occupied)
  let pointer := YulExpr.ident resultVar
  let size := YulExpr.ident sizeName
  let next := YulExpr.ident nextName
  let maxWord := YulExpr.hex (2^64 - 1)
  return [
    .let_ resultVar (.call "mload" [.lit 64]),
    .block [
      .let_ sizeName (.call "extcodesize" [target]),
      .if_ (.call "gt" [size, maxWord]) panicAllocation,
      .let_ nextName (.call "add" [pointer,
        .call "add" [.call "and" [.call "add" [size, .lit 31], .call "not" [.lit 31]], .lit 32]]),
      .if_ (.call "or" [.call "gt" [next, maxWord], .call "lt" [next, pointer]]) panicAllocation,
      .exprStmt (.call "mstore" [.lit 64, next]),
      .exprStmt (.call "mstore" [pointer, size]),
      .exprStmt (.call "extcodecopy" [target, .call "add" [pointer, .lit 32], .lit 0, size])]]

def module (resultVar : String) : ExternalCallModule where
  name := "solidityExtCodeCopy"
  numArgs := 1
  resultVars := [resultVar]
  writesState := false
  readsState := true
  compile := fun _ args => compile resultVar args
  byteTransport := some (.extCodeCopy resultVar)
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_external_code_copy"
  -- Reading code hands control to no account.
  summaryMutability := .staticcall

end SolidityExtCodeCopy

namespace SolidityReturnMemory

/-- `return(offset, size)` of an ABI-encoded buffer in memory. -/
def compile (args : List YulExpr) : Except String (List YulStmt) :=
  match args with
  | [offset, size] => pure [.exprStmt (.call "return" [offset, size])]
  | _ => throw "Solidity memory return expects an offset and a size"

def module : ExternalCallModule where
  name := "solidityReturnMemory"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  compile := fun _ args => compile args
  byteTransport := some .returnMemory
  axioms := []
  proofStatus := .assumed
  summaryName := "solidity_return_memory"
  -- Returning hands control to no account.
  summaryMutability := .staticcall

end SolidityReturnMemory

namespace ExternalCallModule

/-- Compile closed byte transports from their data descriptor. Their metadata
must match the canonical module, preventing contradictory mutability, arity,
result bindings or trust accounting. Legacy modules retain their own compiler. -/
def compileCanonical (module : ExternalCallModule) (context : CompilationContext)
    (args : List YulExpr) : Except String (List YulStmt) := do
  match module.byteTransport with
  | none => module.compile context args
  | some (.staticUint256 resultVar selector numStaticArgs) =>
      let expected := SolidityStaticCall.uint256Module resultVar selector numStaticArgs
      unless module == expected do
        throw "closed Solidity staticcall transport metadata differs"
      SolidityStaticCall.compileUint256 resultVar selector numStaticArgs args
  | some (.staticBool resultVar selector numStaticArgs) =>
      let expected := SolidityStaticCall.boolModule resultVar selector numStaticArgs
      unless module == expected do
        throw "closed Solidity staticcall transport metadata differs"
      SolidityStaticCall.compileBool resultVar selector numStaticArgs args
  | some (.staticBytesUint256 resultVar selector) =>
      let expected := SolidityStaticCall.bytesUint256Module resultVar selector
      unless module == expected do
        throw "closed Solidity staticcall transport metadata differs"
      SolidityStaticCall.compileBytesUint256 resultVar selector args
  | some (.staticBytesBool resultVar selector) =>
      let expected := SolidityStaticCall.bytesBoolModule resultVar selector
      unless module == expected do
        throw "closed Solidity staticcall transport metadata differs"
      SolidityStaticCall.compileBytesBool resultVar selector args
  | some (.create2 resultVar) =>
      unless module == SolidityCreate2.module resultVar do
        throw "closed Solidity create2 transport metadata differs"
      SolidityCreate2.compile resultVar args
  | some (.log eventName topicCount) =>
      unless module == SolidityLog.module eventName topicCount do
        throw "closed Solidity event log transport metadata differs"
      SolidityLog.compile topicCount args
  | some (.optionalBoolCall resultVar selector numWordArgs) =>
      unless module == SolidityLowLevelCall.optionalBoolModule resultVar selector numWordArgs do
        throw "closed Solidity low-level call transport metadata differs"
      SolidityLowLevelCall.compileOptionalBool resultVar selector numWordArgs args
  | some (.callBytesUint256 resultVar selector) =>
      unless module == SolidityLowLevelCall.bytesUint256Module resultVar selector do
        throw "closed Solidity low-level call transport metadata differs"
      SolidityLowLevelCall.compileBytesUint256 resultVar selector args
  | some (.callBytesBool resultVar selector) =>
      unless module == SolidityLowLevelCall.bytesBoolModule resultVar selector do
        throw "closed Solidity low-level call transport metadata differs"
      SolidityLowLevelCall.compileBytesBool resultVar selector args
  | some (.extCodeSize resultVar) =>
      unless module == SolidityExtCodeSize.module resultVar do
        throw "closed Solidity code length transport metadata differs"
      SolidityExtCodeSize.compile resultVar args
  | some (.extCodeCopy resultVar) =>
      unless module == SolidityExtCodeCopy.module resultVar do
        throw "closed Solidity external code transport metadata differs"
      SolidityExtCodeCopy.compile resultVar args
  | some .returnMemory =>
      unless module == SolidityReturnMemory.module do
        throw "closed Solidity memory return transport metadata differs"
      SolidityReturnMemory.compile args

end ExternalCallModule

/-! ### Shared Compilation Utilities

These helpers are used by standard modules and available to third-party modules.
They mirror the helpers in CompilationModel but are decoupled from the full compilation
pipeline so that module files only need to import `Compiler.ECM`. -/

def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
  if bs.isEmpty then
    []
  else
    let chunk := bs.take 32
    chunk :: chunkBytes32 (bs.drop 32)
termination_by bs.length
decreasing_by
  simp_wf
  cases bs with
  | nil => simp at *
  | cons head tail => simp; omega

def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Generate Yul statements that revert with an Error(string) message.
    This is the standard Solidity revert encoding: selector + offset + length + data. -/
def revertWithMessage (message : String) : List YulStmt :=
  let bytes := bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

/-- Copy dynamic data (calldata or memory) to a destination offset.
    Uses calldatacopy or a memory loop depending on `isDynamicFromCalldata`. -/
def dynamicCopyData (ctx : CompilationContext)
    (destOffset sourceOffset len : YulExpr) : List YulStmt :=
  if ctx.isDynamicFromCalldata then
    [YulStmt.exprStmt (YulExpr.call "calldatacopy" [destOffset, sourceOffset, len])]
  else
    [YulStmt.for_
      [YulStmt.let_ "__copy_i" (YulExpr.lit 0)]
      (YulExpr.call "lt" [YulExpr.ident "__copy_i", len])
      [YulStmt.assign "__copy_i" (YulExpr.call "add" [YulExpr.ident "__copy_i", YulExpr.lit 32])]
      [YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [destOffset, YulExpr.ident "__copy_i"],
        YulExpr.call "mload" [YulExpr.call "add" [sourceOffset, YulExpr.ident "__copy_i"]]
      ])]]

/-! ### Verified ECM Shim Promotion & Typed Module Constructors (Phase 4 Track D1) -/

namespace ExternalCallModule

/-- Promote an `ExternalCallModule` to `.proved` proof-accounting status when
backed by a verified compiler runtime shim (`VerifiedCompilerShim`). -/
def withProvedStatus (mod : ExternalCallModule) : ExternalCallModule :=
  { mod with proofStatus := .proved }

/-- Alias for `withProvedStatus` marking an `ExternalCallModule` as `.proved`. -/
def provedModule (mod : ExternalCallModule) : ExternalCallModule :=
  mod.withProvedStatus

/-- Boolean predicate checking whether an `ExternalCallModule` has `.proved` status. -/
def isProved (mod : ExternalCallModule) : Bool :=
  mod.proofStatus == .proved

/-- `withProvedStatus` sets `proofStatus` to `.proved`. -/
@[simp] theorem withProvedStatus_proofStatus (mod : ExternalCallModule) :
    mod.withProvedStatus.proofStatus = .proved := rfl

/-- `provedModule` sets `proofStatus` to `.proved`. -/
@[simp] theorem provedModule_proofStatus (mod : ExternalCallModule) :
    (provedModule mod).proofStatus = .proved := rfl

/-- `isProved` evaluates to `true` after `withProvedStatus`. -/
@[simp] theorem isProved_withProvedStatus (mod : ExternalCallModule) :
    mod.withProvedStatus.isProved = true := rfl

/-- `isProved` evaluates to `true` after `provedModule`. -/
@[simp] theorem isProved_provedModule (mod : ExternalCallModule) :
    (provedModule mod).isProved = true := rfl

/-- `withProvedStatus` preserves `name`. -/
@[simp] theorem withProvedStatus_name (mod : ExternalCallModule) :
    mod.withProvedStatus.name = mod.name := rfl

/-- `withProvedStatus` preserves `numArgs`. -/
@[simp] theorem withProvedStatus_numArgs (mod : ExternalCallModule) :
    mod.withProvedStatus.numArgs = mod.numArgs := rfl

/-- `withProvedStatus` preserves `resultVars`. -/
@[simp] theorem withProvedStatus_resultVars (mod : ExternalCallModule) :
    mod.withProvedStatus.resultVars = mod.resultVars := rfl

/-- `withProvedStatus` preserves `writesState`. -/
@[simp] theorem withProvedStatus_writesState (mod : ExternalCallModule) :
    mod.withProvedStatus.writesState = mod.writesState := rfl

/-- `withProvedStatus` preserves `readsState`. -/
@[simp] theorem withProvedStatus_readsState (mod : ExternalCallModule) :
    mod.withProvedStatus.readsState = mod.readsState := rfl

/-- `withProvedStatus` preserves `axioms`. -/
@[simp] theorem withProvedStatus_axioms (mod : ExternalCallModule) :
    mod.withProvedStatus.axioms = mod.axioms := rfl

/-- `withProvedStatus` preserves `byteTransport`. -/
@[simp] theorem withProvedStatus_byteTransport (mod : ExternalCallModule) :
    mod.withProvedStatus.byteTransport = mod.byteTransport := rfl

/-- `withProvedStatus` is idempotent. -/
@[simp] theorem withProvedStatus_idempotent (mod : ExternalCallModule) :
    mod.withProvedStatus.withProvedStatus = mod.withProvedStatus := rfl

end ExternalCallModule

export ExternalCallModule (withProvedStatus provedModule isProved)

/-- Compile a typed EIP-712 digest in scratch space `[0x00, 0x40)` followed by
an `ecrecover` (`address(1)`) precompile call preserving `memory[0x40]` (`#2002`). -/
def compileEip712Ecrecover (resultVar : String) (args : List YulExpr) :
    Except String (List YulStmt) := do
  let [domainSeparator, structHash, vExpr, rExpr, sExpr] := args
    | throw "eip712Ecrecover expects 5 arguments (domainSeparator, structHash, v, r, s)"
  let fmpSave := "__eip712_saved_fmp"
  let digestVar := "__eip712_digest"
  let ptrVar := "__eip712_ecr_ptr"
  let okVar := "__eip712_ecr_ok"
  let ptr := YulExpr.ident ptrVar
  return [
    .let_ resultVar (.lit 0),
    .block [
      .let_ fmpSave (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.lit 0, domainSeparator]),
      .exprStmt (.call "mstore" [.lit 32, structHash]),
      .let_ digestVar (.call "keccak256" [.lit 0, .lit 64]),
      .let_ ptrVar (.ident fmpSave),
      .exprStmt (.call "mstore" [ptr, .ident digestVar]),
      .exprStmt (.call "mstore" [.call "add" [ptr, .lit 32], vExpr]),
      .exprStmt (.call "mstore" [.call "add" [ptr, .lit 64], rExpr]),
      .exprStmt (.call "mstore" [.call "add" [ptr, .lit 96], sExpr]),
      .let_ okVar (.call "staticcall" [
        .call "gas" [], .lit 1, ptr, .lit 128, .lit 0, .lit 32]),
      .if_ (.call "iszero" [.ident okVar]) [
        .exprStmt (.call "revert" [.lit 0, .lit 0])],
      .if_ (.call "iszero" [.call "returndatasize" []]) [
        .exprStmt (.call "mstore" [.lit 0, .lit 0])],
      .exprStmt (.call "mstore" [.lit 64, .ident fmpSave]),
      .assign resultVar (.call "and" [.call "mload" [.lit 0], .hex addressMask])]]

/-- Typed ECM module for EIP-712 scratch-space digest computation + `ecrecover`
precompile (`address(1)`) preserving `memory[0x40]` (`#2002`). -/
def eip712EcrecoverModule (resultVar : String) : ExternalCallModule :=
  provedModule {
    name := "eip712Ecrecover"
    numArgs := 5
    resultVars := [resultVar]
    writesState := false
    readsState := true
    compile := fun _ args => compileEip712Ecrecover resultVar args
    byteTransport := none
    axioms := []
    summaryName := "eip712_ecrecover_verified_shim"
    summaryMutability := .staticcall
  }

/-- Compile a typed `SSTORE2` runtime data-contract `extcodesize` / `extcodecopy`
`CodeData` read/write shim preserving persistent storage and `0x40` (`#2023`). -/
def compileSstore2CodeData (resultVar : String) (args : List YulExpr) :
    Except String (List YulStmt) := do
  let [pointer, destOffset, codeOffset, size] := args
    | throw "sstore2CodeData expects 4 arguments (pointer, destOffset, codeOffset, size)"
  let fmpSave := "__sstore2_saved_fmp"
  let codeLen := "__sstore2_code_len"
  return [
    .let_ resultVar (.lit 0),
    .block [
      .let_ fmpSave (.call "mload" [.lit 64]),
      .let_ codeLen (.call "extcodesize" [pointer]),
      .if_ (.call "iszero" [
        .call "lt" [.lit 0, .ident codeLen]]) [
        .exprStmt (.call "revert" [.lit 0, .lit 0])],
      .exprStmt (.call "extcodecopy" [pointer, destOffset, codeOffset, size]),
      .exprStmt (.call "mstore" [.lit 64, .ident fmpSave]),
      .assign resultVar (.ident codeLen)]]

/-- Typed ECM module for `CREATE2` + `SSTORE2` runtime data-contract
`extcodesize`/`extcodecopy` `CodeData` read/write preserving `0x40` (`#2023`). -/
def sstore2CodeDataModule (resultVar : String) : ExternalCallModule :=
  provedModule {
    name := "sstore2CodeData"
    numArgs := 4
    resultVars := [resultVar]
    writesState := false
    readsState := true
    compile := fun _ args => compileSstore2CodeData resultVar args
    byteTransport := none
    axioms := []
    summaryName := "sstore2_codedata_verified_shim"
    summaryMutability := .staticcall
  }

/-- Typed ECM module for ABI-encoded dynamic/struct event emission (`LOG1`..`LOG4`)
backed by `dynamicAndStructEventVerifiedShim` (`#2000`). -/
def dynamicStructEventModule (eventName : String) (topicCount : Nat) : ExternalCallModule :=
  provedModule {
    name := "dynamicStructEvent"
    numArgs := topicCount + 2
    resultVars := []
    writesState := true
    readsState := false
    compile := fun _ args => SolidityLog.compile topicCount args
    byteTransport := none
    axioms := []
    summaryName := s!"dynamic_struct_event_{eventName}"
    summaryMutability := .staticcall
  }

/-- Compile an outlined `solc`-shaped Yul helper call (`abi_decode_tuple_*`,
`checked_add_t_uint256`, `panic_error_0x11`, `extract_byte_array_length`) (`#2058`, `#2059`,
`#2071`, `#1982`). -/
def compileSolcOutlinedHelper (helperName resultVar : String) (numArgs : Nat)
    (args : List YulExpr) : Except String (List YulStmt) := do
  unless args.length == numArgs do
    throw s!"solcOutlinedHelper {helperName} argument count differs"
  if resultVar.isEmpty then
    return [.exprStmt (.call helperName args)]
  else
    return [.let_ resultVar (.call helperName args)]

/-- Typed ECM module for outlined `solc`-shaped Yul helper functions used by
Yul-identity targets (`#2058`, `#2059`, `#2071`, `#1982`). -/
def solcOutlinedHelperModule (helperName resultVar : String) (numArgs : Nat) :
    ExternalCallModule :=
  provedModule {
    name := "solcOutlinedHelper"
    numArgs := numArgs
    resultVars := if resultVar.isEmpty then [] else [resultVar]
    writesState := false
    readsState := false
    compile := fun _ args => compileSolcOutlinedHelper helperName resultVar numArgs args
    byteTransport := none
    axioms := []
    summaryName := helperName
    summaryMutability := .staticcall
  }

/-- `eip712EcrecoverModule` has `.proved` proof-accounting status. -/
@[simp] theorem eip712EcrecoverModule_proofStatus (resultVar : String) :
    (eip712EcrecoverModule resultVar).proofStatus = .proved := rfl

/-- `sstore2CodeDataModule` has `.proved` proof-accounting status. -/
@[simp] theorem sstore2CodeDataModule_proofStatus (resultVar : String) :
    (sstore2CodeDataModule resultVar).proofStatus = .proved := rfl

/-- `dynamicStructEventModule` has `.proved` proof-accounting status. -/
@[simp] theorem dynamicStructEventModule_proofStatus (eventName : String) (topicCount : Nat) :
    (dynamicStructEventModule eventName topicCount).proofStatus = .proved := rfl

/-- `solcOutlinedHelperModule` has `.proved` proof-accounting status. -/
@[simp] theorem solcOutlinedHelperModule_proofStatus
    (helperName resultVar : String) (numArgs : Nat) :
    (solcOutlinedHelperModule helperName resultVar numArgs).proofStatus = .proved := rfl

end Compiler.ECM
