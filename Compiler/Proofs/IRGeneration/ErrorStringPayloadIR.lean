import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas
import Verity.Core.Model.ECM

/-!
# Proof-side observable for the Error(string) revert payload

Companion to the `Panic(uint256)` observable (#2280): the ECM helper
`revertWithMessage` emits `mstore` writes (selector, ABI offset, length, data
chunks) followed by a `revert`.  This module proves the emitted statements
execute to exactly those writes applied to memory (`execIRStmts_mstoreWrites`
over the syntactic `MstoreWrites` characterization), with
`applyWrites_not_written` projecting unshadowed keys.  Connecting this to
`revertWithMessage`'s full chunk layout needs its private chunker exposed —
the tracked follow-up; the header projections (selector at 0, ABI offset at 4,
length at 36) follow from these lemmas once the emitted list is
characterized.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.ECM

/-- Apply a write list left to right (later writes shadow earlier ones). -/
def applyWrites (mem : Nat → Nat) : List (Nat × Nat) → Nat → Nat
  | [] => mem
  | (o, w) :: rest =>
      applyWrites (fun x => if x = o then w else mem x) rest

/-- Unwritten keys read through the write list unchanged. -/
theorem applyWrites_not_written (k : Nat) :
    ∀ (writes : List (Nat × Nat)) (mem : Nat → Nat),
      (∀ ow ∈ writes, ow.1 ≠ k) →
      applyWrites mem writes k = mem k
  | [], _, _ => rfl
  | (o, w) :: rest, mem, hall => by
      have hkey : o ≠ k := hall (o, w) (by simp)
      rw [show applyWrites mem ((o, w) :: rest) k =
        applyWrites (fun x => if x = o then w else mem x) rest k from rfl,
        applyWrites_not_written k rest _ (fun ow hw => hall ow (by simp [hw])),
        if_neg (fun h => hkey h.symm)]

/-- Syntactic characterization: each statement is a literal `mstore` of the
paired write (value given as `lit` or `hex` — both evaluate to the word). -/
inductive MstoreWrites : List YulStmt → List (Nat × Nat) → Prop
  | nil : MstoreWrites [] []
  | consLit {stmts writes} (o w : Nat) :
      MstoreWrites stmts writes →
      MstoreWrites (.exprStmt (.call "mstore" [.lit o, .lit w]) :: stmts)
        ((o, w) :: writes)
  | consHex {stmts writes} (o w : Nat) :
      MstoreWrites stmts writes →
      MstoreWrites (.exprStmt (.call "mstore" [.lit o, .hex w]) :: stmts)
        ((o, w) :: writes)

theorem MstoreWrites.append {xs ys : List YulStmt} {ws vs : List (Nat × Nat)}
    (hx : MstoreWrites xs ws) (hy : MstoreWrites ys vs) :
    MstoreWrites (xs ++ ys) (ws ++ vs) := by
  induction hx with
  | nil => simpa using hy
  | consLit o w _ ih => exact .consLit o w ih
  | consHex o w _ ih => exact .consHex o w ih

theorem MstoreWrites.length_eq {stmts : List YulStmt} {writes : List (Nat × Nat)}
    (h : MstoreWrites stmts writes) : stmts.length = writes.length := by
  induction h with
  | nil => rfl
  | consLit _ _ _ ih => simpa using ih
  | consHex _ _ _ ih => simpa using ih

/-- A block of literal `mstore`s executes to `continue` with exactly its
writes applied. -/
theorem execIRStmts_mstoreWrites :
    ∀ {stmts : List YulStmt} {writes : List (Nat × Nat)},
      MstoreWrites stmts writes → ∀ (fuel : Nat) (state : IRState),
        execIRStmts (stmts.length + fuel + 1) state stmts =
          .continue { state with memory := applyWrites state.memory writes }
  | _, _, .nil, fuel, state => by simp [execIRStmts, applyWrites]
  | _, _, @MstoreWrites.consLit tail wtail o w htail, fuel, state => by
      rw [show (YulStmt.exprStmt (.call "mstore" [.lit o, .lit w]) :: tail).length +
        fuel + 1 = (tail.length + fuel + 1) + 1 from by simp [List.length]; omega]
      show (match execIRStmt (tail.length + fuel + 1) state
          (.exprStmt (.call "mstore" [.lit o, .lit w])) with
        | .continue s₁ => execIRStmts (tail.length + fuel + 1) s₁ tail
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) = _
      rw [show execIRStmt (tail.length + fuel + 1) state
          (.exprStmt (.call "mstore" [.lit o, .lit w])) =
        .continue { state with
          memory := fun x => if x = o then w else state.memory x } from by
        simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs]]
      exact execIRStmts_mstoreWrites htail fuel _
  | _, _, @MstoreWrites.consHex tail wtail o w htail, fuel, state => by
      rw [show (YulStmt.exprStmt (.call "mstore" [.lit o, .hex w]) :: tail).length +
        fuel + 1 = (tail.length + fuel + 1) + 1 from by simp [List.length]; omega]
      show (match execIRStmt (tail.length + fuel + 1) state
          (.exprStmt (.call "mstore" [.lit o, .hex w])) with
        | .continue s₁ => execIRStmts (tail.length + fuel + 1) s₁ tail
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) = _
      rw [show execIRStmt (tail.length + fuel + 1) state
          (.exprStmt (.call "mstore" [.lit o, .hex w])) =
        .continue { state with
          memory := fun x => if x = o then w else state.memory x } from by
        simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs]]
      exact execIRStmts_mstoreWrites htail fuel _

end Compiler.Proofs.IRGeneration
