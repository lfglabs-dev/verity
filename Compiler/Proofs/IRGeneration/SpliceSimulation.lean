import Compiler.Proofs.IRGeneration.FuelBound
import Compiler.Proofs.IRGeneration.NonReentrantGuardIR

/-!
# Splice simulation (fragment slice 1: atomics, `if`, `block`)

Relates the execution of a lock-release-spliced body to the original body:
results agree exactly, except that frame halts (`return`/`stop`) carry the
lock-released state — which is the intended semantics of
`applyLockReleaseOnExits`.  Built on the fuel-stability API (#2286/#2287).

This slice covers the fragment without `switch` and `for`; `switch` follows
the same shape and is the next extension.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel

/-- Clear the lock slot. -/
def releaseState (slot : Nat) (s : IRState) : IRState :=
  { s with transientStorage := fun o => if o = slot then 0 else s.transientStorage o }

/-- The simulation relation: frame halts carry the released state, everything
else is unchanged. -/
def releasedResult (slot : Nat) : IRExecResult → IRExecResult
  | .return v s => .return v (releaseState slot s)
  | .stop s => .stop (releaseState slot s)
  | .continue s => .continue s
  | .revert s => .revert s

mutual

/-- Fragment for this slice: loop- and switch-free. -/
def SpliceSim : YulStmt → Prop
  | .if_ _ body => SpliceSimList body
  | .block stmts => SpliceSimList stmts
  | .for_ _ _ _ _ => False
  | .switch _ _ _ => False
  | _ => True

def SpliceSimList : List YulStmt → Prop
  | [] => True
  | s :: rest => SpliceSim s ∧ SpliceSimList rest

end

mutual

theorem SpliceSim.loopFree : ∀ (s : YulStmt), SpliceSim s → LoopFree s
  | .if_ _ body, h => by
      simpa [LoopFree] using SpliceSimList.loopFree body (by simpa [SpliceSim] using h)
  | .block stmts, h => by
      simpa [LoopFree] using SpliceSimList.loopFree stmts (by simpa [SpliceSim] using h)
  | .for_ _ _ _ _, h => by simp [SpliceSim] at h
  | .switch _ _ _, h => by simp [SpliceSim] at h
  | .comment _, _ => by simp [LoopFree]
  | .let_ _ _, _ => by simp [LoopFree]
  | .letMany _ _, _ => by simp [LoopFree]
  | .assign _ _, _ => by simp [LoopFree]
  | .leave, _ => by simp [LoopFree]
  | .exprStmt _, _ => by simp [LoopFree]
  | .funcDef _ _ _ _, _ => by simp [LoopFree]

theorem SpliceSimList.loopFree : ∀ (xs : List YulStmt), SpliceSimList xs →
    LoopFreeList xs
  | [], _ => by simp [LoopFreeList]
  | x :: rest, h => by
      obtain ⟨hx, hrest⟩ : SpliceSim x ∧ SpliceSimList rest := by
        simpa [SpliceSimList] using h
      exact ⟨SpliceSim.loopFree x hx, SpliceSimList.loopFree rest hrest⟩

end

/-- A non-exit expression statement never halts the frame: every interpreter
branch other than the `return`/`stop` builtins produces `continue` or
`revert`. -/
theorem execIRStmt_exprStmt_no_halt (e : YulExpr) (fuel : Nat) (state : IRState)
    (hret : ∀ args, e ≠ .call "return" args)
    (hstop : ∀ args, e ≠ .call "stop" args) :
    (∀ v s, execIRStmt (fuel + 1) state (.exprStmt e) ≠ .return v s) ∧
      (∀ s, execIRStmt (fuel + 1) state (.exprStmt e) ≠ .stop s) := by
  refine ⟨fun v s hcontra => ?_, fun s hcontra => ?_⟩ <;>
  · rw [execIRStmt.eq_def] at hcontra
    repeat' split at hcontra
    all_goals first
      | exact absurd rfl (hret _)
      | exact absurd rfl (hstop _)
      | simp_all
      | cases hcontra

end Compiler.Proofs.IRGeneration
