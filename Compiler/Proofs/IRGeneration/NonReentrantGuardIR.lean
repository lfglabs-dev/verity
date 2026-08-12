import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

/-!
# IR semantics of the nonreentrant guard prologue

First machine-checked brick of the `guarded` ↔ emitted-Yul correspondence
(lane 2.2): the exact statements produced by
`Compiler.CompilationModel.nonReentrantGuardPrologue` are evaluated under the
IR interpreter used by the IR-generation proofs.

- lock slot reads `1` → the frame reverts with the state untouched;
- lock slot reads `0` → execution falls through with the lock set to `1` and
  nothing else changed;
- the release statement spliced by `applyLockReleaseOnExits` resets the slot;
- on the reachable (binary) lock values, the Yul decision `eq(tload(slot), 1)`
  agrees with the source-model decision `lock ≠ 0` of
  `Verity.Core.Model.NonReentrantGuard.guarded`.

Still open: pushing these statement-level facts through
`attachNonReentrantGuard`/`compileGuardedFunctionSpec` and the
`compile_preserves_semantics` stack to lift the `noNonReentrant`
supported-fragment obligations.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel

/-- The exact prologue shape emitted for a resolved lock slot. -/
def guardPrologueStmts (slot : Nat) : List YulStmt :=
  [ .if_ (.call "eq" [.call "tload" [.lit slot], .lit 1])
      [.exprStmt (.call "revert" [.lit 0, .lit 0])],
    .exprStmt (.call "tstore" [.lit slot, .lit 1]) ]

/-- The release statement spliced before every successful exit. -/
def lockReleaseStmt (slot : Nat) : YulStmt :=
  .exprStmt (.call "tstore" [.lit slot, .lit 0])

/-- `nonReentrantGuardPrologue` emits exactly `guardPrologueStmts` at the
resolved slot. -/
theorem nonReentrantGuardPrologue_eq (fields : List Field) (lockField : String)
    (field : Field) (slot : Nat)
    (h : findFieldWithResolvedSlot fields lockField = some (field, slot)) :
    nonReentrantGuardPrologue fields lockField = .ok (guardPrologueStmts slot) := by
  simp [nonReentrantGuardPrologue, h, guardPrologueStmts, pure, Except.pure]

/-- Lock held (`tload = 1`) → the prologue reverts and the state is untouched. -/
theorem execIRStmts_guardPrologue_locked (fuel : Nat) (state : IRState) (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hlock : state.transientStorage slot = 1) :
    execIRStmts (fuel + 3) state (guardPrologueStmts slot) = .revert state := by
  have hmod : slot % Compiler.Constants.evmModulus = slot := Nat.mod_eq_of_lt hslot
  have hone : (1 : Nat) < Compiler.Constants.evmModulus := by
    simp [Compiler.Constants.evmModulus]
  cases fuel with
  | zero =>
      simp [guardPrologueStmts, execIRStmts, execIRStmt, evalIRExpr, evalIRCall,
        evalIRExprs, hmod, hlock, Nat.mod_eq_of_lt hone,
        YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]
  | succ n =>
      simp [guardPrologueStmts, execIRStmts, execIRStmt, evalIRExpr, evalIRCall,
        evalIRExprs, hmod, hlock, Nat.mod_eq_of_lt hone,
        YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]

/-- Lock free (`tload = 0`) → the prologue acquires the lock and changes
nothing else. -/
theorem execIRStmts_guardPrologue_free (fuel : Nat) (state : IRState) (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hlock : state.transientStorage slot = 0) :
    execIRStmts (fuel + 3) state (guardPrologueStmts slot) =
      .continue { state with
        transientStorage := fun o => if o = slot then 1 else state.transientStorage o } := by
  have hmod : slot % Compiler.Constants.evmModulus = slot := Nat.mod_eq_of_lt hslot
  have hone : (1 : Nat) < Compiler.Constants.evmModulus := by
    simp [Compiler.Constants.evmModulus]
  simp [guardPrologueStmts, execIRStmts, execIRStmt, evalIRExpr, evalIRCall,
    evalIRExprs, hmod, hlock, Nat.mod_eq_of_lt hone,
    YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]

/-- The spliced release resets the lock slot and changes nothing else. -/
theorem execIRStmt_lockRelease (fuel : Nat) (state : IRState) (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) :
    execIRStmt (fuel + 1) state (lockReleaseStmt slot) =
      .continue { state with
        transientStorage := fun o => if o = slot then 0 else state.transientStorage o } := by
  have hmod : slot % Compiler.Constants.evmModulus = slot := Nat.mod_eq_of_lt hslot
  simp [lockReleaseStmt, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hmod]

/-- On the reachable (binary) lock values, the Yul decision `eq(lock, 1)`
agrees with the source model's `lock ≠ 0` (`NonReentrantGuard.guarded`). -/
theorem guard_decision_agrees (v : Nat) (hv : v = 0 ∨ v = 1) :
    (v = 1) ↔ v ≠ 0 := by
  rcases hv with h | h <;> simp [h]

/-- Acquire-then-release round-trips the lock slot: the transient storage
function is extensionally the initial one when the slot started free. -/
theorem guard_acquire_release_roundtrip (fuel₁ fuel₂ : Nat) (state : IRState)
    (slot : Nat) (hslot : slot < Compiler.Constants.evmModulus)
    (hlock : state.transientStorage slot = 0) :
    ∀ acquired, execIRStmts (fuel₁ + 3) state (guardPrologueStmts slot) =
        .continue acquired →
      ∀ released, execIRStmt (fuel₂ + 1) acquired (lockReleaseStmt slot) =
          .continue released →
        ∀ k, released.transientStorage k = state.transientStorage k := by
  intro acquired hacq released hrel k
  rw [execIRStmts_guardPrologue_free fuel₁ state slot hslot hlock] at hacq
  injection hacq with hacq
  rw [execIRStmt_lockRelease fuel₂ acquired slot hslot] at hrel
  injection hrel with hrel
  rw [← hrel, ← hacq]
  by_cases hk : k = slot
  · simp [hk, hlock]
  · simp [hk]

/-! ## Fall-through release semantics

With `spliceLockRelease`/`yulFrameHalts` now total (equation lemmas exist),
the epilogue behavior of `applyLockReleaseOnExits` becomes provable.  The
first law: on a straight-line body (no frame exits, hence no splice points)
that executes to a `continue`, the guarded body releases the lock on
fall-through and changes nothing else. -/

/-- Sequencing lemma for the fuel-indexed interpreter: a prefix that continues
consumes exactly its length in fuel. -/
theorem execIRStmts_append_continue (ys : List YulStmt) :
    ∀ (xs : List YulStmt) (fuel : Nat) (state s' : IRState),
      execIRStmts fuel state xs = .continue s' →
      execIRStmts fuel state (xs ++ ys) =
        execIRStmts (fuel - xs.length) s' ys
  | [], fuel, state, s', h => by
      have hs : s' = state := by
        simpa [execIRStmts] using h.symm
      subst hs
      simp [execIRStmts]
  | x :: xs', fuel, state, s', h => by
      cases fuel with
      | zero => simp [execIRStmts] at h
      | succ f =>
          rw [show (x :: xs') ++ ys = x :: (xs' ++ ys) from rfl]
          rw [show execIRStmts (f + 1) state (x :: (xs' ++ ys)) =
            (match execIRStmt f state x with
              | .continue s₁ => execIRStmts f s₁ (xs' ++ ys)
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) from rfl]
          rw [show execIRStmts (f + 1) state (x :: xs') =
            (match execIRStmt f state x with
              | .continue s₁ => execIRStmts f s₁ xs'
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) from rfl] at h
          cases hstep : execIRStmt f state x with
          | «continue» s₁ =>
              rw [hstep] at h
              simpa [List.length] using
                execIRStmts_append_continue ys xs' f s₁ s' h
          | «return» v s => rw [hstep] at h; cases h
          | stop s => rw [hstep] at h; cases h
          | revert s => rw [hstep] at h; cases h

/-- Fall-through law: a straight-line guarded body (no frame exits, no splice
points) that continues releases the lock at the end and changes nothing
else. -/
theorem applyLockReleaseOnExits_fallthrough (slot : Nat) (body : List YulStmt)
    (fuel : Nat) (state s' : IRState)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hnohalt : yulFrameHaltsList body = false)
    (hnosplice : spliceLockReleaseList (lockReleaseStmt slot) body = body)
    (hexec : execIRStmts fuel state body = .continue s')
    (hfuel : body.length + 2 ≤ fuel) :
    execIRStmts fuel state
        (applyLockReleaseOnExits (lockReleaseStmt slot) body) =
      .continue { s' with
        transientStorage := fun o => if o = slot then 0 else s'.transientStorage o } := by
  unfold applyLockReleaseOnExits
  rw [hnosplice, hnohalt]
  simp only [Bool.false_eq_true, if_false]
  rw [execIRStmts_append_continue [lockReleaseStmt slot] body fuel state s' hexec]
  obtain ⟨k, hk⟩ : ∃ k, fuel - body.length = k + 2 :=
    ⟨fuel - body.length - 2, by omega⟩
  rw [hk]
  rw [show execIRStmts (k + 2) s' [lockReleaseStmt slot] =
    (match execIRStmt (k + 1) s' (lockReleaseStmt slot) with
      | .continue s₁ => execIRStmts (k + 1) s₁ []
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s) from rfl]
  rw [execIRStmt_lockRelease k s' slot hslot]
  simp [execIRStmts]

end Compiler.Proofs.IRGeneration
