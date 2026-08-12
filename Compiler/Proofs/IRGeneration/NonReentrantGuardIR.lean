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

/-! ## Splice-point release semantics

The other exit class: bodies that halt the frame with `stop`/`return` get the
release spliced immediately before the halt, and no trailing release. -/

/-- Splicing distributes over concatenation. -/
theorem spliceLockReleaseList_append (release : YulStmt) :
    ∀ (xs ys : List YulStmt),
      spliceLockReleaseList release (xs ++ ys) =
        spliceLockReleaseList release xs ++ spliceLockReleaseList release ys
  | [], _ => rfl
  | x :: xs', ys => by
      simp [spliceLockReleaseList, spliceLockReleaseList_append release xs' ys]

/-- `yulFrameHaltsList` looks only at the last statement: appending a halting
statement makes the list halt. -/
theorem yulFrameHaltsList_append_halting (s : YulStmt)
    (hs : yulFrameHalts s = true) :
    ∀ (xs : List YulStmt), yulFrameHaltsList (xs ++ [s]) = true
  | [] => by simpa [yulFrameHaltsList] using hs
  | [_] => by
      simpa [yulFrameHaltsList] using
        yulFrameHaltsList_append_halting s hs []
  | _ :: x' :: xs' => by
      simpa [yulFrameHaltsList] using
        yulFrameHaltsList_append_halting s hs (x' :: xs')

/-- Stop-exit law: a straight-line body ending in `stop` releases the lock
immediately before halting, and gets no trailing (dead) release. -/
theorem applyLockReleaseOnExits_stop (slot : Nat) (xs : List YulStmt)
    (fuel : Nat) (state s' : IRState)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hnosplice : spliceLockReleaseList (lockReleaseStmt slot) xs = xs)
    (hxs : execIRStmts fuel state xs = .continue s')
    (hfuel : xs.length + 3 ≤ fuel) :
    execIRStmts fuel state
        (applyLockReleaseOnExits (lockReleaseStmt slot)
          (xs ++ [YulStmt.exprStmt (.call "stop" [])])) =
      .stop { s' with
        transientStorage := fun o => if o = slot then 0 else s'.transientStorage o } := by
  unfold applyLockReleaseOnExits
  rw [yulFrameHaltsList_append_halting _ (by rfl) xs, if_pos rfl,
    spliceLockReleaseList_append, hnosplice,
    show spliceLockReleaseList (lockReleaseStmt slot)
        [YulStmt.exprStmt (.call "stop" [])] =
      [lockReleaseStmt slot, YulStmt.exprStmt (.call "stop" [])] from rfl,
    execIRStmts_append_continue _ xs fuel state s' hxs]
  obtain ⟨k, hk⟩ : ∃ k, fuel - xs.length = k + 3 :=
    ⟨fuel - xs.length - 3, by omega⟩
  rw [hk]
  rw [show execIRStmts (k + 3) s'
      [lockReleaseStmt slot, YulStmt.exprStmt (.call "stop" [])] =
    (match execIRStmt (k + 2) s' (lockReleaseStmt slot) with
      | .continue s₁ => execIRStmts (k + 2) s₁ [YulStmt.exprStmt (.call "stop" [])]
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s) from rfl]
  rw [execIRStmt_lockRelease (k + 1) s' slot hslot]
  rfl

/-! ## Composed guard correspondence (straight-line bodies)

The IR-level mirror of `Verity.Core.Model.NonReentrantGuard.guarded` for
straight-line bodies: locked entry reverts untouched; free entry runs the body
under the acquired lock and releases it on fall-through. -/

/-- Locked entry: the whole guarded compilation unit — prologue followed by
anything — reverts untouched; the revert short-circuits the rest. -/
theorem guardedBody_locked_reverts (slot : Nat) (rest : List YulStmt)
    (fuel : Nat) (state : IRState)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hlock : state.transientStorage slot = 1)
    (hfuel : 3 ≤ fuel) :
    execIRStmts fuel state (guardPrologueStmts slot ++ rest) = .revert state := by
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
  subst hk
  have hmod : slot % Compiler.Constants.evmModulus = slot := Nat.mod_eq_of_lt hslot
  have hone : (1 : Nat) < Compiler.Constants.evmModulus := by
    simp [Compiler.Constants.evmModulus]
  cases k with
  | zero =>
      simp [guardPrologueStmts, execIRStmts, execIRStmt, evalIRExpr, evalIRCall,
        evalIRExprs, hmod, hlock, Nat.mod_eq_of_lt hone,
        YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]
  | succ n =>
      simp [guardPrologueStmts, execIRStmts, execIRStmt, evalIRExpr, evalIRCall,
        evalIRExprs, hmod, hlock, Nat.mod_eq_of_lt hone,
        YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]

/-- Free entry: the guarded unit runs its suffix from the acquired state.
Composes the prologue-acquire lemma with fuel sequencing. -/
theorem guardedBody_free_runs_suffix (slot : Nat) (rest : List YulStmt)
    (fuel : Nat) (state : IRState)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hlock : state.transientStorage slot = 0)
    (hfuel : 3 ≤ fuel) :
    execIRStmts fuel state (guardPrologueStmts slot ++ rest) =
      execIRStmts (fuel - 2) { state with
        transientStorage := fun o => if o = slot then 1 else state.transientStorage o }
        rest := by
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
  subst hk
  rw [execIRStmts_append_continue rest (guardPrologueStmts slot) (k + 3) state _
    (execIRStmts_guardPrologue_free k state slot hslot hlock)]
  rfl

end Compiler.Proofs.IRGeneration
