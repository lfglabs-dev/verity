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
  deriving BEq, Repr

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

instance : BEq ExternalCallModule where
  beq a b := a.name == b.name && a.numArgs == b.numArgs &&
    a.resultVars == b.resultVars && a.writesState == b.writesState &&
    a.readsState == b.readsState && a.axioms == b.axioms &&
    a.proofStatus == b.proofStatus && a.summaryName == b.summaryName &&
    a.summarySelector == b.summarySelector && a.summaryMutability == b.summaryMutability &&
    a.byteTransport == b.byteTransport

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


end SolidityStaticCall

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

end Compiler.ECM
