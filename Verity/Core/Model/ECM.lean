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
    a.summarySelector == b.summarySelector && a.summaryMutability == b.summaryMutability

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

/-! ### Shared Compilation Utilities

These helpers are used by standard modules and available to third-party modules.
They mirror the helpers in CompilationModel but are decoupled from the full compilation
pipeline so that module files only need to import `Compiler.ECM`. -/

private def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

private def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
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

private def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Generate Yul statements that revert with an Error(string) message.
    This is the standard Solidity revert encoding: selector + offset + length + data. -/
def revertWithMessage (message : String) : List YulStmt :=
  let bytes := bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

/-- Copy dynamic data (calldata or memory) to a destination offset.
    Uses calldatacopy or a memory loop depending on `isDynamicFromCalldata`. -/
def dynamicCopyData (ctx : CompilationContext)
    (destOffset sourceOffset len : YulExpr) : List YulStmt :=
  if ctx.isDynamicFromCalldata then
    [YulStmt.expr (YulExpr.call "calldatacopy" [destOffset, sourceOffset, len])]
  else
    [YulStmt.for_
      [YulStmt.let_ "__copy_i" (YulExpr.lit 0)]
      (YulExpr.call "lt" [YulExpr.ident "__copy_i", len])
      [YulStmt.assign "__copy_i" (YulExpr.call "add" [YulExpr.ident "__copy_i", YulExpr.lit 32])]
      [YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [destOffset, YulExpr.ident "__copy_i"],
        YulExpr.call "mload" [YulExpr.call "add" [sourceOffset, YulExpr.ident "__copy_i"]]
      ])]]

end Compiler.ECM
