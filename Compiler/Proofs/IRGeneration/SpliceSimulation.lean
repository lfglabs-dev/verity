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
  | .exprStmt (.call "return" args) => ∃ a b, args = [YulExpr.lit a, YulExpr.lit b]
  | .exprStmt (.call "stop" args) => args = []
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

/-- Atomic non-exit statements: everything the splice leaves untouched and
whose execution cannot halt the frame. -/
def AtomicNonExit : YulStmt → Prop
  | .comment _ => True
  | .let_ _ _ => True
  | .letMany _ _ => True
  | .assign _ _ => True
  | .leave => True
  | .funcDef _ _ _ _ => True
  | .exprStmt (.call "return" _) => False
  | .exprStmt (.call "stop" _) => False
  | .exprStmt _ => True
  | _ => False

/-- The splice leaves atomic non-exit statements untouched. -/
theorem spliceLockRelease_atomic (release : YulStmt) :
    ∀ (x : YulStmt), AtomicNonExit x →
      spliceLockRelease release x = [x]
  | .comment _, _ => rfl
  | .let_ _ _, _ => rfl
  | .letMany _ _, _ => rfl
  | .assign _ _, _ => rfl
  | .leave, _ => rfl
  | .funcDef _ _ _ _, _ => rfl
  | .exprStmt (.lit _), _ => rfl
  | .exprStmt (.hex _), _ => rfl
  | .exprStmt (.ident _), _ => rfl
  | .exprStmt (.str _), _ => rfl
  | .exprStmt (.call f args), h => by
      have hret : f ≠ "return" := by
        intro hf; subst hf; simp [AtomicNonExit] at h
      have hstop : f ≠ "stop" := by
        intro hf; subst hf; simp [AtomicNonExit] at h
      simp [spliceLockRelease, hret, hstop]
  | .if_ _ _, h => by simp [AtomicNonExit] at h
  | .for_ _ _ _ _, h => by simp [AtomicNonExit] at h
  | .switch _ _ _, h => by simp [AtomicNonExit] at h
  | .block _, h => by simp [AtomicNonExit] at h

/-- Atomic non-exit statements never halt the frame. -/
theorem execIRStmt_atomic_no_halt (x : YulStmt) (hx : AtomicNonExit x)
    (fuel : Nat) (state : IRState) :
    (∀ v s, execIRStmt (fuel + 1) state x ≠ .return v s) ∧
      (∀ s, execIRStmt (fuel + 1) state x ≠ .stop s) := by
  cases x with
  | exprStmt e =>
      refine execIRStmt_exprStmt_no_halt e fuel state ?_ ?_ <;>
        (intro args hcontra; subst hcontra; simp [AtomicNonExit] at hx)
  | comment _ => exact ⟨(fun v s h => nomatch h), (fun s h => nomatch h)⟩
  | «leave» => exact ⟨(fun v s h => nomatch h), (fun s h => nomatch h)⟩
  | funcDef _ _ _ _ => exact ⟨(fun v s h => nomatch h), (fun s h => nomatch h)⟩
  | letMany _ _ => exact ⟨(fun v s h => nomatch h), (fun s h => nomatch h)⟩
  | let_ n v =>
      refine ⟨fun v' s' hcontra => ?_, fun s' hcontra => ?_⟩ <;>
        (cases heval : evalIRExpr state v <;> simp [execIRStmt, heval] at hcontra)
  | assign n v =>
      refine ⟨fun v' s' hcontra => ?_, fun s' hcontra => ?_⟩ <;>
        (cases heval : evalIRExpr state v <;> simp [execIRStmt, heval] at hcontra)
  | if_ _ _ => simp [AtomicNonExit] at hx
  | for_ _ _ _ _ => simp [AtomicNonExit] at hx
  | «switch» _ _ _ => simp [AtomicNonExit] at hx
  | block _ => simp [AtomicNonExit] at hx

/-- Cons step for an atomic non-exit head: the head executes identically on
both sides (fuel stability), cannot halt, and the tails relate by the given
induction hypothesis. -/
theorem spliced_cons_atomic (slot : Nat) (x : YulStmt) (rest : List YulStmt)
    (hAtomic : AtomicNonExit x) (hLFx : LoopFree x)
    (IH : ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F →
      stmtsFuelBound rest ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) rest) =
        releasedResult slot (execIRStmts G state rest))
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) (x :: rest)) ≤ F)
    (hG : stmtsFuelBound (x :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) (x :: rest)) =
      releasedResult slot (execIRStmts G state (x :: rest)) := by
  have hshape : spliceLockReleaseList (lockReleaseStmt slot) (x :: rest) =
      x :: spliceLockReleaseList (lockReleaseStmt slot) rest := by
    rw [show spliceLockReleaseList (lockReleaseStmt slot) (x :: rest) =
      spliceLockRelease (lockReleaseStmt slot) x ++
        spliceLockReleaseList (lockReleaseStmt slot) rest from rfl,
      spliceLockRelease_atomic (lockReleaseStmt slot) x hAtomic]
    rfl
  rw [hshape] at hF ⊢
  simp only [stmtsFuelBound] at hF hG
  have hmaxF : stmtFuelBound x ≤ Nat.max (stmtFuelBound x)
      (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) ∧
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤
        Nat.max (stmtFuelBound x)
          (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hmaxG : stmtFuelBound x ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound rest) ∧
      stmtsFuelBound rest ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound rest) :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hbx : stmtFuelBound x ≤ F - 1 := by omega
  have hbx' : stmtFuelBound x ≤ G - 1 := by omega
  have hbrest : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤
      F - 1 := by omega
  have hbrest' : stmtsFuelBound rest ≤ G - 1 := by omega
  have hFpos : 1 ≤ F := by omega
  have hGpos : 1 ≤ G := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hbx hbx' hbrest hbrest'
  have hhead : execIRStmt F' state x = execIRStmt G' state x :=
    execIRStmt_stable_of_le x hLFx F' G' state hbx hbx'
  show (match execIRStmt F' state x with
    | .continue s₁ => execIRStmts F' s₁
        (spliceLockReleaseList (lockReleaseStmt slot) rest)
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) =
    releasedResult slot (match execIRStmt G' state x with
    | .continue s₁ => execIRStmts G' s₁ rest
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s)
  rw [hhead]
  obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 :=
    ⟨G' - 1, by have := stmtFuelBound_pos x; omega⟩
  have hnohalt := execIRStmt_atomic_no_halt x hAtomic G'' state
  cases hres : execIRStmt (G'' + 1) state x with
  | «continue» s₁ => exact IH F' (G'' + 1) s₁ hbrest hbrest'
  | «return» v s => exact absurd hres (hnohalt.1 v s)
  | stop s => exact absurd hres (hnohalt.2 s)
  | revert s => rfl

/-- Cons step for a `stop()` head: the release runs, the frame halts with the
released state, the tail is dead on both sides. -/
theorem spliced_cons_stop (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) (rest : List YulStmt)
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.exprStmt (.call "stop" []) :: rest)) ≤ F)
    (hG : stmtsFuelBound (YulStmt.exprStmt (.call "stop" []) :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot)
        (YulStmt.exprStmt (.call "stop" []) :: rest)) =
      releasedResult slot
        (execIRStmts G state (YulStmt.exprStmt (.call "stop" []) :: rest)) := by
  have hshape : spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.exprStmt (.call "stop" []) :: rest) =
      lockReleaseStmt slot :: YulStmt.exprStmt (.call "stop" []) ::
        spliceLockReleaseList (lockReleaseStmt slot) rest := rfl
  rw [hshape] at hF ⊢
  have hlr : stmtFuelBound (lockReleaseStmt slot) = 1 := rfl
  simp only [stmtsFuelBound, stmtFuelBound, hlr] at hF hG
  have hx1 : (1 : Nat) ≤ Nat.max 1
      (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_left _ _
  have hx2 : Nat.max 1
      (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) + 1 ≤
      Nat.max 1 (Nat.max 1
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) + 1) :=
    Nat.le_max_right _ _
  have hg1 : (1 : Nat) ≤ Nat.max 1 (stmtsFuelBound rest) := Nat.le_max_left _ _
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
  show (match execIRStmt (F' + 2) state (lockReleaseStmt slot) with
    | .continue s₁ => execIRStmts (F' + 2) s₁
        (YulStmt.exprStmt (.call "stop" []) ::
          spliceLockReleaseList (lockReleaseStmt slot) rest)
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) = _
  rw [execIRStmt_lockRelease (F' + 1) state slot hslot]
  rfl

/-- Cons step for a `return(lit, lit)` head: the release runs, the returned
word reads memory (untouched by the release), the frame halts released. -/
theorem spliced_cons_return (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) (a b : Nat)
    (rest : List YulStmt) (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) :: rest)) ≤ F)
    (hG : stmtsFuelBound
      (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot)
        (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) :: rest)) =
      releasedResult slot (execIRStmts G state
        (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) :: rest)) := by
  have hshape : spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) :: rest) =
      lockReleaseStmt slot ::
        YulStmt.exprStmt (.call "return" [.lit a, .lit b]) ::
        spliceLockReleaseList (lockReleaseStmt slot) rest := rfl
  rw [hshape] at hF ⊢
  have hlr : stmtFuelBound (lockReleaseStmt slot) = 1 := rfl
  simp only [stmtsFuelBound, stmtFuelBound, hlr] at hF hG
  have hx1 : (1 : Nat) ≤ Nat.max 1
      (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_left _ _
  have hx2 : Nat.max 1
      (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) + 1 ≤
      Nat.max 1 (Nat.max 1
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) + 1) :=
    Nat.le_max_right _ _
  have hg1 : (1 : Nat) ≤ Nat.max 1 (stmtsFuelBound rest) := Nat.le_max_left _ _
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
  show (match execIRStmt (F' + 2) state (lockReleaseStmt slot) with
    | .continue s₁ => execIRStmts (F' + 2) s₁
        (YulStmt.exprStmt (.call "return" [.lit a, .lit b]) ::
          spliceLockReleaseList (lockReleaseStmt slot) rest)
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) = _
  rw [execIRStmt_lockRelease (F' + 1) state slot hslot]
  by_cases hb : b = 32 <;>
    simp [execIRStmts, execIRStmt, evalIRExpr, evalIRExprs, releasedResult,
      releaseState, hb]

/-- Cons step for an `if` head: the condition evaluates identically, the
spliced branch relates by the body IH, and the outcome propagates through the
list step by cases on the original branch result. -/
theorem spliced_cons_if (slot : Nat) (cond : YulExpr) (body rest : List YulStmt)
    (IHbody : ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) ≤ F →
      stmtsFuelBound body ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) body) =
        releasedResult slot (execIRStmts G state body))
    (IHrest : ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F →
      stmtsFuelBound rest ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) rest) =
        releasedResult slot (execIRStmts G state rest))
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.if_ cond body :: rest)) ≤ F)
    (hG : stmtsFuelBound (YulStmt.if_ cond body :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot)
        (YulStmt.if_ cond body :: rest)) =
      releasedResult slot (execIRStmts G state (YulStmt.if_ cond body :: rest)) := by
  have hshape : spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.if_ cond body :: rest) =
      YulStmt.if_ cond (spliceLockReleaseList (lockReleaseStmt slot) body) ::
        spliceLockReleaseList (lockReleaseStmt slot) rest := rfl
  rw [hshape] at hF ⊢
  simp only [stmtsFuelBound, stmtFuelBound] at hF hG
  have hx1 : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) + 1 ≤
      Nat.max (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) + 1)
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_left _ _
  have hx2 : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤
      Nat.max (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) + 1)
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_right _ _
  have hg1 : stmtsFuelBound body + 1 ≤
      Nat.max (stmtsFuelBound body + 1) (stmtsFuelBound rest) := Nat.le_max_left _ _
  have hg2 : stmtsFuelBound rest ≤
      Nat.max (stmtsFuelBound body + 1) (stmtsFuelBound rest) := Nat.le_max_right _ _
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
  show (match (match evalIRExpr state cond with
      | some c => if c ≠ 0 then
          execIRStmts F' state (spliceLockReleaseList (lockReleaseStmt slot) body)
        else .continue state
      | none => .revert state) with
    | .continue s₁ => execIRStmts (F' + 1) s₁
        (spliceLockReleaseList (lockReleaseStmt slot) rest)
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) =
    releasedResult slot (match (match evalIRExpr state cond with
      | some c => if c ≠ 0 then execIRStmts G' state body else .continue state
      | none => .revert state) with
    | .continue s₁ => execIRStmts (G' + 1) s₁ rest
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s)
  cases heval : evalIRExpr state cond with
  | none => simp [releasedResult]
  | some c =>
      by_cases hc : c ≠ 0
      · simp only [if_pos hc]
        rw [IHbody F' G' state (by omega) (by omega)]
        cases hrb : execIRStmts G' state body with
        | «continue» s₁ =>
            simp only [releasedResult]
            exact IHrest (F' + 1) (G' + 1) s₁ (by omega) (by omega)
        | «return» v s => simp [releasedResult]
        | stop s => simp [releasedResult]
        | revert s => simp [releasedResult]
      · simp only [if_neg hc, releasedResult]
        exact IHrest (F' + 1) (G' + 1) state (by omega) (by omega)

/-- Cons step for a `block` head: the spliced block relates by the body IH
and the outcome propagates through the list step. -/
theorem spliced_cons_block (slot : Nat) (stmts rest : List YulStmt)
    (IHbody : ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) stmts) ≤ F →
      stmtsFuelBound stmts ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) stmts) =
        releasedResult slot (execIRStmts G state stmts))
    (IHrest : ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F →
      stmtsFuelBound rest ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) rest) =
        releasedResult slot (execIRStmts G state rest))
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.block stmts :: rest)) ≤ F)
    (hG : stmtsFuelBound (YulStmt.block stmts :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot)
        (YulStmt.block stmts :: rest)) =
      releasedResult slot (execIRStmts G state (YulStmt.block stmts :: rest)) := by
  have hshape : spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.block stmts :: rest) =
      YulStmt.block (spliceLockReleaseList (lockReleaseStmt slot) stmts) ::
        spliceLockReleaseList (lockReleaseStmt slot) rest := rfl
  rw [hshape] at hF ⊢
  simp only [stmtsFuelBound, stmtFuelBound] at hF hG
  have hx1 : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) stmts) + 1 ≤
      Nat.max (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) stmts) + 1)
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_left _ _
  have hx2 : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤
      Nat.max (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) stmts) + 1)
        (stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest)) :=
    Nat.le_max_right _ _
  have hg1 : stmtsFuelBound stmts + 1 ≤
      Nat.max (stmtsFuelBound stmts + 1) (stmtsFuelBound rest) := Nat.le_max_left _ _
  have hg2 : stmtsFuelBound rest ≤
      Nat.max (stmtsFuelBound stmts + 1) (stmtsFuelBound rest) := Nat.le_max_right _ _
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
  show (match execIRStmts F' state
      (spliceLockReleaseList (lockReleaseStmt slot) stmts) with
    | .continue s₁ => execIRStmts (F' + 1) s₁
        (spliceLockReleaseList (lockReleaseStmt slot) rest)
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) =
    releasedResult slot (match execIRStmts G' state stmts with
    | .continue s₁ => execIRStmts (G' + 1) s₁ rest
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s)
  rw [IHbody F' G' state (by omega) (by omega)]
  cases hrb : execIRStmts G' state stmts with
  | «continue» s₁ =>
      simp only [releasedResult]
      exact IHrest (F' + 1) (G' + 1) s₁ (by omega) (by omega)
  | «return» v s => simp [releasedResult]
  | stop s => simp [releasedResult]
  | revert s => simp [releasedResult]

/-- The general splice simulation over the fragment: executing the spliced
body equals the original execution with frame halts carrying the released
state — at any fuels above the respective bounds. -/
theorem execIRStmts_spliced (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) :
    ∀ (xs : List YulStmt), SpliceSimList xs → ∀ (F G : Nat) (state : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) ≤ F →
      stmtsFuelBound xs ≤ G →
      execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) xs) =
        releasedResult slot (execIRStmts G state xs)
  | [], _, F, G, state, hF, hG => by
      have hF1 : 1 ≤ F := Nat.le_trans (by simp [spliceLockReleaseList, stmtsFuelBound]) hF
      have hG1 : 1 ≤ G := Nat.le_trans (by simp [stmtsFuelBound]) hG
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simp [spliceLockReleaseList, execIRStmts, releasedResult]
  | x :: rest, hSS, F, G, state, hF, hG => by
      obtain ⟨hx, hrest⟩ : SpliceSim x ∧ SpliceSimList rest := by
        simpa [SpliceSimList] using hSS
      have IHrest := fun F G st hF hG =>
        execIRStmts_spliced slot hslot rest hrest F G st hF hG
      cases x with
      | if_ cond body =>
          exact spliced_cons_if slot cond body rest
            (fun F G st hF hG => execIRStmts_spliced slot hslot body
              (by simpa [SpliceSim] using hx) F G st hF hG)
            IHrest F G state hF hG
      | block stmts =>
          exact spliced_cons_block slot stmts rest
            (fun F G st hF hG => execIRStmts_spliced slot hslot stmts
              (by simpa [SpliceSim] using hx) F G st hF hG)
            IHrest F G state hF hG
      | for_ _ _ _ _ => exact absurd hx (by simp [SpliceSim])
      | «switch» _ _ _ => exact absurd hx (by simp [SpliceSim])
      | comment t =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | let_ n v =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | letMany ns v =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | assign n v =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | «leave» =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | funcDef n ps rs b =>
          exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
      | exprStmt e =>
          cases e with
          | lit v => exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
          | hex v => exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
          | ident n => exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
          | str t => exact spliced_cons_atomic slot _ rest (by simp [AtomicNonExit]) (by simp [LoopFree]) IHrest F G state hF hG
          | call f args =>
              by_cases hret : f = "return"
              · subst hret
                obtain ⟨a, b, rfl⟩ : ∃ a b, args = [YulExpr.lit a, YulExpr.lit b] := by
                  simpa [SpliceSim] using hx
                exact spliced_cons_return slot hslot a b rest F G state hF hG
              · by_cases hstop : f = "stop"
                · subst hstop
                  obtain rfl : args = [] := by simpa [SpliceSim] using hx
                  exact spliced_cons_stop slot hslot rest F G state hF hG
                · exact spliced_cons_atomic slot _ rest
                    (by simp [AtomicNonExit, hret, hstop]) (by simp [LoopFree])
                    IHrest F G state hF hG

/-- A halted prefix short-circuits an appended suffix. -/
theorem execIRStmts_append_halt (ys : List YulStmt) :
    ∀ (xs : List YulStmt) (fuel : Nat) (state : IRState) (r : IRExecResult),
      execIRStmts fuel state xs = r →
      (∀ s, r ≠ .continue s) →
      execIRStmts fuel state (xs ++ ys) = r
  | [], fuel, state, r, hr, hnc => by
      have hcs : r = .continue state := by
        cases fuel <;> simpa [execIRStmts] using hr.symm
      exact absurd hcs (hnc state)
  | x :: xs', fuel, state, r, hr, hnc => by
      cases fuel with
      | zero =>
          simp [execIRStmts] at hr ⊢
          exact hr
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
              | .revert s => .revert s) from rfl] at hr
          cases hstep : execIRStmt f state x with
          | «continue» s₁ =>
              rw [hstep] at hr
              exact execIRStmts_append_halt ys xs' f s₁ r hr hnc
          | «return» v s => rw [hstep] at hr; rw [← hr]
          | stop s => rw [hstep] at hr; rw [← hr]
          | revert s => rw [hstep] at hr; rw [← hr]

/-- Wrapper composition, fall-through analysis branch: when the halt analysis
reports the body can fall through, `applyLockReleaseOnExits` appends a
trailing release, and the wrapped execution equals the original with every
successful outcome carrying the released state — halts released by the
splice, the fall-through by the trailing statement, reverts rolling back the
acquire untouched. -/
theorem execIRStmts_applyLockReleaseOnExits_fallthrough (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (xs : List YulStmt) (hSS : SpliceSimList xs)
    (hH : yulFrameHaltsList xs = false)
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) +
      (spliceLockReleaseList (lockReleaseStmt slot) xs).length + 2 ≤ F)
    (hG : stmtsFuelBound xs ≤ G) :
    execIRStmts F state (applyLockReleaseOnExits (lockReleaseStmt slot) xs) =
      (match execIRStmts G state xs with
        | .continue s => .continue (releaseState slot s)
        | .return v s => .return v (releaseState slot s)
        | .stop s => .stop (releaseState slot s)
        | .revert s => .revert s) := by
  have hboundlist : 1 ≤ stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) :=
    stmtsFuelBound_pos _
  unfold applyLockReleaseOnExits
  rw [hH]
  simp only [Bool.false_eq_true, if_false]
  have hsim := execIRStmts_spliced slot hslot xs hSS F G state (by omega) hG
  cases hres : execIRStmts G state xs with
  | «continue» s =>
      have hpre : execIRStmts F state
          (spliceLockReleaseList (lockReleaseStmt slot) xs) = .continue s := by
        rw [hsim, hres]; rfl
      rw [execIRStmts_append_continue [lockReleaseStmt slot] _ F state s hpre]
      obtain ⟨k, hk⟩ : ∃ k, F -
          (spliceLockReleaseList (lockReleaseStmt slot) xs).length = k + 2 :=
        ⟨F - (spliceLockReleaseList (lockReleaseStmt slot) xs).length - 2, by omega⟩
      rw [hk]
      rw [show execIRStmts (k + 2) s [lockReleaseStmt slot] =
        (match execIRStmt (k + 1) s (lockReleaseStmt slot) with
          | .continue s₁ => execIRStmts (k + 1) s₁ []
          | .return v s' => .return v s'
          | .stop s' => .stop s'
          | .revert s' => .revert s') from rfl,
        execIRStmt_lockRelease k s slot hslot]
      rfl
  | «return» v s =>
      have hpre : execIRStmts F state
          (spliceLockReleaseList (lockReleaseStmt slot) xs) =
          .return v (releaseState slot s) := by
        rw [hsim, hres]; rfl
      rw [execIRStmts_append_halt [lockReleaseStmt slot] _ F state _ hpre
        (by intro s' h; cases h)]
  | stop s =>
      have hpre : execIRStmts F state
          (spliceLockReleaseList (lockReleaseStmt slot) xs) =
          .stop (releaseState slot s) := by
        rw [hsim, hres]; rfl
      rw [execIRStmts_append_halt [lockReleaseStmt slot] _ F state _ hpre
        (by intro s' h; cases h)]
  | revert s =>
      have hpre : execIRStmts F state
          (spliceLockReleaseList (lockReleaseStmt slot) xs) = .revert s := by
        rw [hsim, hres]; rfl
      rw [execIRStmts_append_halt [lockReleaseStmt slot] _ F state _ hpre
        (by intro s' h; cases h)]

/-- Frame halts whose interpreter semantics actually halt (the analysis also
marks `invalid`/`selfdestruct`, which the interpreter continues — those are
excluded here). -/
inductive ModeledHalt : YulStmt → Prop
  | stop : ModeledHalt (.exprStmt (.call "stop" []))
  | ret (a b : Nat) :
      ModeledHalt (.exprStmt (.call "return" [.lit a, .lit b]))
  | rev (a b : YulExpr) :
      ModeledHalt (.exprStmt (.call "revert" [a, b]))

/-- A modeled halt never continues, at any fuel (out of fuel reverts). -/
theorem execIRStmt_modeledHalt_no_continue (h : YulStmt) (hmh : ModeledHalt h)
    (fuel : Nat) (state : IRState) :
    ∀ s, execIRStmt fuel state h ≠ .continue s := by
  intro s hcontra
  cases hmh with
  | stop => cases fuel <;> simp [execIRStmt] at hcontra
  | ret a b =>
      cases fuel with
      | zero => simp [execIRStmt] at hcontra
      | succ f =>
          by_cases hb : b = 32 <;>
            simp [execIRStmt, evalIRExpr, evalIRExprs, hb] at hcontra
  | rev a b => cases fuel <;> simp [execIRStmt] at hcontra

/-- A body ending in a modeled halt never continues. -/
theorem execIRStmts_last_halt_no_continue (h : YulStmt) (hmh : ModeledHalt h) :
    ∀ (ys : List YulStmt) (fuel : Nat) (state : IRState) (s : IRState),
      execIRStmts fuel state (ys ++ [h]) ≠ .continue s := by
  intro ys fuel state s hcontra
  cases hpre : execIRStmts fuel state ys with
  | «continue» s₁ =>
      rw [execIRStmts_append_continue [h] ys fuel state s₁ hpre] at hcontra
      cases hfl : fuel - ys.length with
      | zero => rw [hfl] at hcontra; simp [execIRStmts] at hcontra
      | succ k =>
          rw [hfl] at hcontra
          rw [show execIRStmts (k + 1) s₁ [h] =
            (match execIRStmt k s₁ h with
              | .continue s₂ => execIRStmts k s₂ []
              | .return v s' => .return v s'
              | .stop s' => .stop s'
              | .revert s' => .revert s') from rfl] at hcontra
          cases hstep : execIRStmt k s₁ h with
          | «continue» s₂ =>
              exact execIRStmt_modeledHalt_no_continue h hmh k s₁ s₂ hstep
          | «return» v s' => rw [hstep] at hcontra; cases hcontra
          | stop s' => rw [hstep] at hcontra; cases hcontra
          | revert s' => rw [hstep] at hcontra; cases hcontra
  | «return» v s₁ =>
      rw [execIRStmts_append_halt [h] ys fuel state _ hpre
        (by intro _ hc; cases hc)] at hcontra
      cases hcontra
  | stop s₁ =>
      rw [execIRStmts_append_halt [h] ys fuel state _ hpre
        (by intro _ hc; cases hc)] at hcontra
      cases hcontra
  | revert s₁ =>
      rw [execIRStmts_append_halt [h] ys fuel state _ hpre
        (by intro _ hc; cases hc)] at hcontra
      cases hcontra

/-- Modeled halts are halting for the frame analysis. -/
theorem ModeledHalt.frameHalts {h : YulStmt} (hmh : ModeledHalt h) :
    yulFrameHalts h = true := by
  cases hmh <;> rfl

/-- Wrapper composition, halting-analysis branch: a fragment body ending in a
modeled halt gets no trailing release, and the wrapped execution equals the
original with halts carrying the released state — the fall-through arm being
unreachable. -/
theorem execIRStmts_applyLockReleaseOnExits_halting (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (ys : List YulStmt) (h : YulStmt)
    (hSS : SpliceSimList (ys ++ [h])) (hmh : ModeledHalt h)
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (ys ++ [h])) ≤ F)
    (hG : stmtsFuelBound (ys ++ [h]) ≤ G) :
    execIRStmts F state
        (applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])) =
      (match execIRStmts G state (ys ++ [h]) with
        | .continue s => .continue (releaseState slot s)
        | .return v s => .return v (releaseState slot s)
        | .stop s => .stop (releaseState slot s)
        | .revert s => .revert s) := by
  unfold applyLockReleaseOnExits
  rw [yulFrameHaltsList_append_halting h hmh.frameHalts ys, if_pos rfl]
  rw [execIRStmts_spliced slot hslot (ys ++ [h]) hSS F G state hF hG]
  cases hres : execIRStmts G state (ys ++ [h]) with
  | «continue» s =>
      exact absurd hres (execIRStmts_last_halt_no_continue h hmh ys G state s)
  | «return» v s => rfl
  | stop s => rfl
  | revert s => rfl

/-- End-to-end guarded unit, fall-through bodies: the compiled prologue plus
release-wrapped body mirrors `NonReentrantGuard.guarded` exactly — locked
entry reverts untouched; free entry runs the body from the acquired state
with every successful outcome carrying the released state. -/
theorem execIRStmts_guardedUnit_fallthrough (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (xs : List YulStmt) (hSS : SpliceSimList xs)
    (hH : yulFrameHaltsList xs = false)
    (F G : Nat) (state : IRState)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) +
      (spliceLockReleaseList (lockReleaseStmt slot) xs).length + 4 ≤ F)
    (hG : stmtsFuelBound xs ≤ G) :
    execIRStmts F state (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) xs) =
      if state.transientStorage slot = 1 then .revert state
      else
        (match execIRStmts G { state with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } xs with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  rcases hlock01 with hfree | hlocked
  · rw [if_neg (by rw [hfree]; decide)]
    rw [guardedBody_free_runs_suffix slot _ F state hslot hfree (by omega)]
    exact execIRStmts_applyLockReleaseOnExits_fallthrough slot hslot xs hSS hH
      (F - 2) G _ (by omega) hG
  · rw [if_pos hlocked]
    exact guardedBody_locked_reverts slot _ F state hslot hlocked (by omega)

/-- End-to-end guarded unit, modeled-halt endings. -/
theorem execIRStmts_guardedUnit_halting (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (ys : List YulStmt) (h : YulStmt)
    (hSS : SpliceSimList (ys ++ [h])) (hmh : ModeledHalt h)
    (F G : Nat) (state : IRState)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (ys ++ [h])) + 2 ≤ F)
    (hG : stmtsFuelBound (ys ++ [h]) ≤ G) :
    execIRStmts F state (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])) =
      if state.transientStorage slot = 1 then .revert state
      else
        (match execIRStmts G { state with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } (ys ++ [h]) with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  have hpos := stmtsFuelBound_pos
    (spliceLockReleaseList (lockReleaseStmt slot) (ys ++ [h]))
  rcases hlock01 with hfree | hlocked
  · rw [if_neg (by rw [hfree]; decide)]
    rw [guardedBody_free_runs_suffix slot _ F state hslot hfree (by omega)]
    exact execIRStmts_applyLockReleaseOnExits_halting slot hslot ys h hSS hmh
      (F - 2) G _ (by omega) hG
  · rw [if_pos hlocked]
    exact guardedBody_locked_reverts slot _ F state hslot hlocked (by omega)

end Compiler.Proofs.IRGeneration
