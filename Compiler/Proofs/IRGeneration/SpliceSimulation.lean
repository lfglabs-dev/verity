import Compiler.Proofs.IRGeneration.FuelBound
import Compiler.Proofs.IRGeneration.NonReentrantGuardIR
import Compiler.Proofs.IRGeneration.ParamLoading

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
  | .switch _ cases dflt => SpliceSimCases cases ∧ SpliceSimDflt dflt
  | .exprStmt (.call "return" args) => ∃ a b, args = [YulExpr.lit a, YulExpr.lit b]
  | .exprStmt (.call "stop" args) => args = []
  | .exprStmt (.call "selfdestruct" _) => False
  | _ => True

def SpliceSimCases : List (Nat × List YulStmt) → Prop
  | [] => True
  | c :: rest => SpliceSimList c.2 ∧ SpliceSimCases rest

def SpliceSimDflt : Option (List YulStmt) → Prop
  | none => True
  | some stmts => SpliceSimList stmts

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
  | .switch _ cases dflt, h => by
      obtain ⟨hc, hd⟩ : SpliceSimCases cases ∧ SpliceSimDflt dflt := by
        simpa [SpliceSim] using h
      simp only [LoopFree]
      exact ⟨SpliceSimCases.loopFree cases hc, SpliceSimDflt.loopFree dflt hd⟩
  | .comment _, _ => by simp [LoopFree]
  | .let_ _ _, _ => by simp [LoopFree]
  | .letMany _ _, _ => by simp [LoopFree]
  | .assign _ _, _ => by simp [LoopFree]
  | .leave, _ => by simp [LoopFree]
  | .exprStmt _, _ => by simp [LoopFree]
  | .funcDef _ _ _ _, _ => by simp [LoopFree]

theorem SpliceSimCases.loopFree : ∀ (cs : List (Nat × List YulStmt)),
    SpliceSimCases cs → LoopFreeCases cs
  | [], _ => by simp [LoopFreeCases]
  | c :: rest, h => by
      obtain ⟨hc, hrest⟩ : SpliceSimList c.2 ∧ SpliceSimCases rest := by
        simpa [SpliceSimCases] using h
      exact ⟨SpliceSimList.loopFree c.2 hc, SpliceSimCases.loopFree rest hrest⟩

theorem SpliceSimDflt.loopFree : ∀ (d : Option (List YulStmt)),
    SpliceSimDflt d → LoopFreeDflt d
  | none, _ => by simp [LoopFreeDflt]
  | some stmts, h => SpliceSimList.loopFree stmts (by simpa [SpliceSimDflt] using h)

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
    (hstop : ∀ args, e ≠ .call "stop" args)
    (hsd : ∀ args, e ≠ .call "selfdestruct" args) :
    (∀ v s, execIRStmt (fuel + 1) state (.exprStmt e) ≠ .return v s) ∧
      (∀ s, execIRStmt (fuel + 1) state (.exprStmt e) ≠ .stop s) := by
  -- Every leaf of the unfolded interpreter is closed by a constructor clash or by
  -- the excluded builtin name; no leaf needs `simp_all` over the split context.
  refine ⟨fun v s hcontra => ?_, fun s hcontra => ?_⟩ <;>
  · rw [execIRStmt.eq_def] at hcontra
    repeat' split at hcontra
    all_goals first
      | exact absurd rfl (hret _)
      | exact absurd rfl (hstop _)
      | exact absurd rfl (hsd _)
      | (cases hcontra; done)
      | contradiction
      | (injections; subst_vars
         first
          | exact absurd rfl (hret _)
          | exact absurd rfl (hstop _)
          | exact absurd rfl (hsd _))

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
  | .exprStmt (.call "selfdestruct" _) => False
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
      refine execIRStmt_exprStmt_no_halt e fuel state ?_ ?_ ?_ <;>
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

/-- The splice simulation for a list body, at all fuels above the bounds. -/
private def SplicedSim (slot : Nat) (xs : List YulStmt) : Prop :=
  ∀ (F G : Nat) (state : IRState),
    stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) ≤ F →
    stmtsFuelBound xs ≤ G →
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot) xs) =
      releasedResult slot (execIRStmts G state xs)

/-- The splice simulation for a single (spliced, original) head statement. -/
private def HeadSim (slot : Nat) (x' x : YulStmt) : Prop :=
  ∀ (F G : Nat) (state : IRState), stmtFuelBound x' ≤ F → stmtFuelBound x ≤ G →
    execIRStmt F state x' = releasedResult slot (execIRStmt G state x)

/-- Both components of a cons bound sit strictly below it. -/
private theorem stmtsFuelBound_cons_le {x : YulStmt} {xs : List YulStmt} {F : Nat}
    (h : stmtsFuelBound (x :: xs) ≤ F) :
    stmtFuelBound x + 1 ≤ F ∧ stmtsFuelBound xs + 1 ≤ F := by
  simp only [stmtsFuelBound] at h
  have h1 : stmtFuelBound x ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound xs) :=
    Nat.le_max_left _ _
  have h2 : stmtsFuelBound xs ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound xs) :=
    Nat.le_max_right _ _
  omega

/-- List step at successor fuel: a related head result propagates through the
spliced tail. -/
private theorem execIRStmts_cons_succ_of_head (slot : Nat) (x' x : YulStmt)
    (rest : List YulStmt) (IHrest : SplicedSim slot rest) (F G : Nat) (state : IRState)
    (hhead : execIRStmt F state x' = releasedResult slot (execIRStmt G state x))
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F)
    (hG : stmtsFuelBound rest ≤ G) :
    execIRStmts (F + 1) state (x' :: spliceLockReleaseList (lockReleaseStmt slot) rest) =
      releasedResult slot (execIRStmts (G + 1) state (x :: rest)) := by
  simp only [execIRStmts, hhead]
  cases execIRStmt G state x with
  | «continue» s₁ => exact IHrest F G s₁ hF hG
  | _ => rfl

/-- Cons step from a head simulation: peel one unit of fuel on each side and
propagate the head result through the tail. -/
private theorem execIRStmts_cons_of_head (slot : Nat) (x' x : YulStmt)
    (rest : List YulStmt) (hhead : HeadSim slot x' x) (IHrest : SplicedSim slot rest)
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (x' :: spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F)
    (hG : stmtsFuelBound (x :: rest) ≤ G) :
    execIRStmts F state (x' :: spliceLockReleaseList (lockReleaseStmt slot) rest) =
      releasedResult slot (execIRStmts G state (x :: rest)) := by
  obtain ⟨hF1, hF2⟩ := stmtsFuelBound_cons_le hF
  obtain ⟨hG1, hG2⟩ := stmtsFuelBound_cons_le hG
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  exact execIRStmts_cons_succ_of_head slot x' x rest IHrest F' G' state
    (hhead F' G' state (by omega) (by omega)) (by omega) (by omega)

/-- The splice keeps an atomic non-exit head in place. -/
private theorem spliceLockReleaseList_cons_atomic (slot : Nat) (x : YulStmt)
    (rest : List YulStmt) (hAtomic : AtomicNonExit x) :
    spliceLockReleaseList (lockReleaseStmt slot) (x :: rest) =
      x :: spliceLockReleaseList (lockReleaseStmt slot) rest := by
  rw [show spliceLockReleaseList (lockReleaseStmt slot) (x :: rest) =
    spliceLockRelease (lockReleaseStmt slot) x ++
      spliceLockReleaseList (lockReleaseStmt slot) rest from rfl,
    spliceLockRelease_atomic (lockReleaseStmt slot) x hAtomic]
  rfl

/-- An atomic non-exit head executes identically at any fuels above its bound
and never halts, so its result is unchanged by `releasedResult`. -/
private theorem headSim_atomic (slot : Nat) (x : YulStmt) (hAtomic : AtomicNonExit x)
    (hLFx : LoopFree x) : HeadSim slot x x := by
  intro F G state hbx hbx'
  rw [execIRStmt_stable_of_le x hLFx F G state hbx hbx']
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 :=
    ⟨G - 1, by have := stmtFuelBound_pos x; omega⟩
  have hnohalt := execIRStmt_atomic_no_halt x hAtomic G' state
  cases hres : execIRStmt (G' + 1) state x with
  | «continue» s₁ => rfl
  | «return» v s => exact absurd hres (hnohalt.1 v s)
  | stop s => exact absurd hres (hnohalt.2 s)
  | revert s => rfl

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
  rw [spliceLockReleaseList_cons_atomic slot x rest hAtomic] at hF ⊢
  exact execIRStmts_cons_of_head slot x x rest (headSim_atomic slot x hAtomic hLFx) IH
    F G state hF hG

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
    simp [execIRStmts, execIRStmt, releasedResult,
      releaseState, hb]

/-- An `if` head with a spliced body relates by the body simulation. -/
private theorem headSim_if (slot : Nat) (cond : YulExpr) (body : List YulStmt)
    (IHbody : SplicedSim slot body) :
    HeadSim slot (.if_ cond (spliceLockReleaseList (lockReleaseStmt slot) body))
      (.if_ cond body) := by
  intro F G state hF hG
  simp only [stmtFuelBound] at hF hG
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  cases heval : evalIRExpr state cond with
  | none => simp only [execIRStmt, heval, releasedResult]
  | some c =>
      by_cases hc : c ≠ 0
      · simp only [execIRStmt, heval, if_pos hc]
        exact IHbody F' G' state (by omega) (by omega)
      · simp only [execIRStmt, heval, if_neg hc, releasedResult]

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
  exact execIRStmts_cons_of_head slot _ _ rest (headSim_if slot cond body IHbody) IHrest
    F G state hF hG

/-- A `block` head with a spliced body relates by the body simulation. -/
private theorem headSim_block (slot : Nat) (stmts : List YulStmt)
    (IHbody : SplicedSim slot stmts) :
    HeadSim slot (.block (spliceLockReleaseList (lockReleaseStmt slot) stmts))
      (.block stmts) := by
  intro F G state hF hG
  simp only [stmtFuelBound] at hF hG
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  exact IHbody F' G' state (by omega) (by omega)

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
  exact execIRStmts_cons_of_head slot _ _ rest (headSim_block slot stmts IHbody) IHrest
    F G state hF hG

/-- `find?` commutes with the key-preserving case splice. -/
theorem find?_spliceCases (release : YulStmt) (v : Nat) :
    ∀ (cs : List (Nat × List YulStmt)),
      List.find? (fun (c : Nat × List YulStmt) => c.1 == v)
          (spliceLockReleaseCases release cs) =
        (List.find? (fun (c : Nat × List YulStmt) => c.1 == v) cs).map
          (fun c => (c.1, spliceLockReleaseList release c.2))
  | [] => rfl
  | c :: rest => by
      rw [show spliceLockReleaseCases release (c :: rest) =
        (c.1, spliceLockReleaseList release c.2) ::
          spliceLockReleaseCases release rest from rfl]
      by_cases hv : c.1 == v
      · simp [List.find?, hv]
      · simp only [List.find?, hv]
        simpa using find?_spliceCases release v rest

/-- Bound domination through the case splice, by membership. -/
theorem spliced_case_bound_le (release : YulStmt) :
    ∀ (cs : List (Nat × List YulStmt)) (c : Nat × List YulStmt), c ∈ cs →
      stmtsFuelBound (spliceLockReleaseList release c.2) ≤
        casesFuelBound (spliceLockReleaseCases release cs)
  | [], _, h => by cases h
  | x :: rest, c, h => by
      rw [show spliceLockReleaseCases release (x :: rest) =
        (x.1, spliceLockReleaseList release x.2) ::
          spliceLockReleaseCases release rest from rfl]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (spliced_case_bound_le release rest c h)
          (Nat.le_max_right _ _)

/-- Fragment membership for cases. -/
theorem SpliceSimCases.mem :
    ∀ {cs : List (Nat × List YulStmt)}, SpliceSimCases cs →
      ∀ {c : Nat × List YulStmt}, c ∈ cs → SpliceSimList c.2 := by
  intro cs h c hmem
  induction cs with
  | nil => cases hmem
  | cons x rest ih =>
      obtain ⟨hx, hrest⟩ := h
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hx
      · exact ih hrest hmem

/-- Fuel bounds for a selected switch case, on both sides of the splice. -/
private theorem spliced_switch_case_bounds (slot : Nat)
    {cases : List (Nat × List YulStmt)} {dflt : Option (List YulStmt)}
    {c : Nat × List YulStmt} (hmem : c ∈ cases) {F G : Nat}
    (hF : Nat.max (casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases))
      (dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) dflt)) + 1 ≤ F + 1)
    (hG : Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + 1 ≤ G + 1) :
    stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) c.2) ≤ F ∧
      stmtsFuelBound c.2 ≤ G := by
  have h1 := spliced_case_bound_le (lockReleaseStmt slot) cases c hmem
  have h2 := stmtsFuelBound_le_casesFuelBound cases c hmem
  have h3 : casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases) ≤
      Nat.max (casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases))
        (dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) dflt)) :=
    Nat.le_max_left _ _
  have h4 : casesFuelBound cases ≤ Nat.max (casesFuelBound cases) (dfltFuelBound dflt) :=
    Nat.le_max_left _ _
  omega

/-- Fuel bounds for a present switch default, on both sides of the splice. -/
private theorem spliced_switch_dflt_bounds (slot : Nat)
    {cases : List (Nat × List YulStmt)} {body : List YulStmt} {F G : Nat}
    (hF : Nat.max (casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases))
      (dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) (some body))) + 1 ≤ F + 1)
    (hG : Nat.max (casesFuelBound cases) (dfltFuelBound (some body)) + 1 ≤ G + 1) :
    stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) ≤ F ∧
      stmtsFuelBound body ≤ G := by
  have h1 : dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) (some body)) ≤
      Nat.max (casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases))
        (dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) (some body))) :=
    Nat.le_max_right _ _
  have h2 : dfltFuelBound (some body) ≤
      Nat.max (casesFuelBound cases) (dfltFuelBound (some body)) := Nat.le_max_right _ _
  have h3 : dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) (some body)) =
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) := rfl
  have h4 : dfltFuelBound (some body) = stmtsFuelBound body := rfl
  omega

/-- The default branch of a switch whose scrutinee matches no case. -/
private theorem spliced_switch_dflt_exec (slot : Nat) (cases : List (Nat × List YulStmt))
    (dflt : Option (List YulStmt))
    (IHdflt : ∀ body, dflt = some body → SplicedSim slot body) (F G : Nat) (state : IRState)
    (hF : Nat.max (casesFuelBound (spliceLockReleaseCases (lockReleaseStmt slot) cases))
      (dfltFuelBound (spliceLockReleaseDflt (lockReleaseStmt slot) dflt)) + 1 ≤ F + 1)
    (hG : Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + 1 ≤ G + 1) :
    (match (generalizing := false) spliceLockReleaseDflt (lockReleaseStmt slot) dflt with
      | some body => execIRStmts F state body
      | none => .continue state) =
      releasedResult slot (match (generalizing := false) dflt with
        | some body => execIRStmts G state body
        | none => .continue state) := by
  cases dflt with
  | none => rfl
  | some body =>
      obtain ⟨hbF, hbG⟩ := spliced_switch_dflt_bounds slot hF hG
      exact IHdflt body rfl F G state hbF hbG

/-- A `switch` head with spliced branches relates by the branch simulations:
the scrutinee evaluates identically and `find?` commutes with the splice. -/
private theorem headSim_switch (slot : Nat) (e : YulExpr)
    (cases : List (Nat × List YulStmt)) (dflt : Option (List YulStmt))
    (IHcases : ∀ c ∈ cases, SplicedSim slot c.2)
    (IHdflt : ∀ body, dflt = some body → SplicedSim slot body) :
    HeadSim slot (.switch e (spliceLockReleaseCases (lockReleaseStmt slot) cases)
      (spliceLockReleaseDflt (lockReleaseStmt slot) dflt)) (.switch e cases dflt) := by
  intro F G state hF hG
  simp only [stmtFuelBound] at hF hG
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  cases heval : evalIRExpr state e with
  | none => simp only [execIRStmt, heval, releasedResult]
  | some v =>
      simp only [execIRStmt, heval, find?_spliceCases (lockReleaseStmt slot) v cases]
      cases hfind : List.find? (fun (c : Nat × List YulStmt) => c.1 == v) cases with
      | some c =>
          obtain ⟨k, body⟩ := c
          have hmem := List.mem_of_find?_eq_some hfind
          obtain ⟨hbF, hbG⟩ := spliced_switch_case_bounds slot hmem hF hG
          exact IHcases (k, body) hmem F' G' state hbF hbG
      | none => exact spliced_switch_dflt_exec slot cases dflt IHdflt F' G' state hF hG

/-- `spliced_cons_switch`, stated over `SplicedSim`. -/
private theorem spliced_cons_switch_sim (slot : Nat) (e : YulExpr)
    (cases : List (Nat × List YulStmt)) (dflt : Option (List YulStmt))
    (rest : List YulStmt) (IHcases : ∀ c ∈ cases, SplicedSim slot c.2)
    (IHdflt : ∀ body, dflt = some body → SplicedSim slot body)
    (IHrest : SplicedSim slot rest) :
    SplicedSim slot (YulStmt.switch e cases dflt :: rest) := by
  intro F G state hF hG
  exact execIRStmts_cons_of_head slot _ _ rest
    (headSim_switch slot e cases dflt IHcases IHdflt) IHrest F G state hF hG

/-- Cons step for a `switch` head: the scrutinee evaluates identically, the
selected branch (case via the find? commutation, or default) relates by the
given IHs, and the outcome propagates through the list step. -/
theorem spliced_cons_switch (slot : Nat) (e : YulExpr)
    (cases : List (Nat × List YulStmt)) (dflt : Option (List YulStmt))
    (rest : List YulStmt)
    (IHcases : ∀ c ∈ cases, ∀ (F G : Nat) (st : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) c.2) ≤ F →
      stmtsFuelBound c.2 ≤ G →
      execIRStmts F st (spliceLockReleaseList (lockReleaseStmt slot) c.2) =
        releasedResult slot (execIRStmts G st c.2))
    (IHdflt : ∀ body, dflt = some body → ∀ (F G : Nat) (st : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) ≤ F →
      stmtsFuelBound body ≤ G →
      execIRStmts F st (spliceLockReleaseList (lockReleaseStmt slot) body) =
        releasedResult slot (execIRStmts G st body))
    (IHrest : ∀ (F G : Nat) (st : IRState),
      stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) rest) ≤ F →
      stmtsFuelBound rest ≤ G →
      execIRStmts F st (spliceLockReleaseList (lockReleaseStmt slot) rest) =
        releasedResult slot (execIRStmts G st rest))
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (YulStmt.switch e cases dflt :: rest)) ≤ F)
    (hG : stmtsFuelBound (YulStmt.switch e cases dflt :: rest) ≤ G) :
    execIRStmts F state (spliceLockReleaseList (lockReleaseStmt slot)
        (YulStmt.switch e cases dflt :: rest)) =
      releasedResult slot
        (execIRStmts G state (YulStmt.switch e cases dflt :: rest)) := by
  exact spliced_cons_switch_sim slot e cases dflt rest IHcases IHdflt IHrest F G state hF hG

/-- Cons step for an atomic non-exit head, stated over `SplicedSim`. -/
private theorem spliced_cons_leaf (slot : Nat) (x : YulStmt) (rest : List YulStmt)
    (hx : AtomicNonExit x ∧ LoopFree x) (IHrest : SplicedSim slot rest) :
    SplicedSim slot (x :: rest) :=
  spliced_cons_atomic slot x rest hx.1 hx.2 IHrest

/-- Cons step for an expression-statement head of the fragment: `return`/`stop`
heads take the release, every other call is atomic. -/
private theorem spliced_cons_exprStmt (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) (e : YulExpr) (rest : List YulStmt)
    (hx : SpliceSim (.exprStmt e)) (IHrest : SplicedSim slot rest) :
    SplicedSim slot (.exprStmt e :: rest) := by
  intro F G state hF hG
  cases e
  case call f args =>
    by_cases hret : f = "return"
    · subst hret
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [YulExpr.lit a, YulExpr.lit b] := by
        simpa [SpliceSim] using hx
      exact spliced_cons_return slot hslot a b rest F G state hF hG
    · by_cases hstop : f = "stop"
      · subst hstop
        obtain rfl : args = [] := by simpa [SpliceSim] using hx
        exact spliced_cons_stop slot hslot rest F G state hF hG
      · by_cases hsd : f = "selfdestruct"
        · subst hsd
          exact absurd hx (by simp [SpliceSim])
        · exact spliced_cons_leaf slot _ rest
            (by simp [AtomicNonExit, LoopFree, hret, hstop, hsd])
            IHrest F G state hF hG
  all_goals
    exact spliced_cons_leaf slot _ rest (by simp [AtomicNonExit, LoopFree])
      IHrest F G state hF hG

/-- The splice simulation for the empty body. -/
private theorem spliced_nil (slot : Nat) : SplicedSim slot [] := by
  intro F G state _ _
  simp only [spliceLockReleaseList, execIRStmts, releasedResult]

mutual

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
  | [], _ => spliced_nil slot
  | x :: rest, hSS => by
      have IHrest := execIRStmts_spliced slot hslot rest hSS.2
      cases x
      case if_ c b =>
        exact spliced_cons_if slot c b rest (execIRStmts_spliced slot hslot b hSS.1) IHrest
      case block b =>
        exact spliced_cons_block slot b rest (execIRStmts_spliced slot hslot b hSS.1) IHrest
      case «switch» e cs d =>
        exact spliced_cons_switch slot e cs d rest
          (execIRStmts_splicedCases slot hslot cs hSS.1.1)
          (execIRStmts_splicedDflt slot hslot d hSS.1.2) IHrest
      case for_ => exact absurd hSS.1 (by simp [SpliceSim])
      case exprStmt e => exact spliced_cons_exprStmt slot hslot e rest hSS.1 IHrest
      all_goals exact spliced_cons_leaf slot _ rest (by simp [AtomicNonExit, LoopFree]) IHrest
termination_by xs _ => sizeOf xs
decreasing_by all_goals (simp_wf; (try simp [*, Option.some.sizeOf_spec]); try omega)

/-- Companion recursion over switch cases: pointwise simulation for every
member body, with structurally static termination. -/
theorem execIRStmts_splicedCases (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) :
    ∀ (cs : List (Nat × List YulStmt)), SpliceSimCases cs →
      ∀ c ∈ cs, ∀ (F G : Nat) (st : IRState),
        stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) c.2) ≤ F →
        stmtsFuelBound c.2 ≤ G →
        execIRStmts F st (spliceLockReleaseList (lockReleaseStmt slot) c.2) =
          releasedResult slot (execIRStmts G st c.2)
  | [], _, c, hmem, _, _, _, _, _ => nomatch hmem
  | ⟨k, body⟩ :: rest', hSS, c, hmem, F, G, st, hF, hG => by
      obtain ⟨hhead, hrest'⟩ : SpliceSimList body ∧ SpliceSimCases rest' := by
        simpa [SpliceSimCases] using hSS
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact execIRStmts_spliced slot hslot body hhead F G st hF hG
      · exact execIRStmts_splicedCases slot hslot rest' hrest' c hmem' F G st hF hG
termination_by cs _ _ _ _ _ _ _ _ => sizeOf cs
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Companion recursion for the default branch. -/
theorem execIRStmts_splicedDflt (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) :
    ∀ (d : Option (List YulStmt)), SpliceSimDflt d →
      ∀ body, d = some body → ∀ (F G : Nat) (st : IRState),
        stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) body) ≤ F →
        stmtsFuelBound body ≤ G →
        execIRStmts F st (spliceLockReleaseList (lockReleaseStmt slot) body) =
          releasedResult slot (execIRStmts G st body)
  | none, _, _, hbody, _, _, _, _, _ => nomatch hbody
  | some dbody, hd, body, hbody, F, G, st, hF, hG => by
      obtain rfl : dbody = body := by injection hbody
      exact execIRStmts_spliced slot hslot dbody
        (by simpa [SpliceSimDflt] using hd) F G st hF hG
termination_by d _ _ _ _ _ _ _ _ => sizeOf d
decreasing_by
  all_goals simp_wf

end

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

/-- A continuing prefix followed by the trailing release continues with the
released state. -/
private theorem execIRStmts_append_lockRelease_continue (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus) (xs : List YulStmt) (F : Nat)
    (state s : IRState) (hpre : execIRStmts F state xs = .continue s)
    (hF : xs.length + 2 ≤ F) :
    execIRStmts F state (xs ++ [lockReleaseStmt slot]) =
      .continue (releaseState slot s) := by
  rw [execIRStmts_append_continue [lockReleaseStmt slot] _ F state s hpre]
  obtain ⟨k, hk⟩ : ∃ k, F - xs.length = k + 2 := ⟨F - xs.length - 2, by omega⟩
  rw [hk, show execIRStmts (k + 2) s [lockReleaseStmt slot] =
    (match execIRStmt (k + 1) s (lockReleaseStmt slot) with
      | .continue s₁ => execIRStmts (k + 1) s₁ []
      | .return v s' => .return v s'
      | .stop s' => .stop s'
      | .revert s' => .revert s') from rfl,
    execIRStmt_lockRelease k s slot hslot]
  rfl

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
  have hbound := stmtsFuelBound_pos (spliceLockReleaseList (lockReleaseStmt slot) xs)
  simp only [applyLockReleaseOnExits, hH, Bool.false_eq_true, if_false]
  have hsim := execIRStmts_spliced slot hslot xs hSS F G state (by omega) hG
  cases hres : execIRStmts G state xs
  case «continue» s =>
    exact execIRStmts_append_lockRelease_continue slot hslot _ F state s
      (by rw [hsim, hres]; rfl) (by omega)
  all_goals
    exact execIRStmts_append_halt [lockReleaseStmt slot] _ F state _
      (by rw [hsim, hres]; rfl) (by intro s' h; cases h)

/-- Frame halts whose interpreter semantics actually halt (the analysis also
marks `invalid`/`selfdestruct`, which the interpreter continues — those are
excluded here). -/
inductive ModeledHalt : YulStmt → Prop
  | stop : ModeledHalt (.exprStmt (.call "stop" []))
  | ret (a b : Nat) :
      ModeledHalt (.exprStmt (.call "return" [.lit a, .lit b]))
  | rev (a b : YulExpr) :
      ModeledHalt (.exprStmt (.call "revert" [a, b]))
  | inv : ModeledHalt (.exprStmt (.call "invalid" []))

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
            simp [execIRStmt, hb] at hcontra
  | rev a b =>
      cases fuel with
      | zero => simp [execIRStmt] at hcontra
      | succ f => simp only [execIRStmt] at hcontra; split at hcontra <;> cases hcontra
  | inv => cases fuel <;> simp [execIRStmt] at hcontra

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

/-- Parameter binding never touches transient storage. -/
theorem applyBindingsToIRState_transient :
    ∀ (bindings : List (String × Nat)) (state : IRState),
      (ParamLoading.applyBindingsToIRState state bindings).transientStorage =
        state.transientStorage
  | [], _ => rfl
  | (n, v) :: rest, state => by
      rw [show ParamLoading.applyBindingsToIRState state ((n, v) :: rest) =
        ParamLoading.applyBindingsToIRState (state.setVar n v) rest from rfl,
        applyBindingsToIRState_transient rest (state.setVar n v)]
      rfl

/-- The full guarded function body — parameter loads, prologue, release-wrapped
body — mirrors `guarded` end to end for fall-through fragment bodies: loads
bind the arguments, a locked entry then reverts with only the bindings
applied, and a free entry runs the body from the acquired bound state with
successful outcomes released. -/
theorem execIRStmts_guardedFunction_fallthrough (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (params : List Param) (bindings : List (String × Nat))
    (xs : List YulStmt) (hSS : SpliceSimList xs)
    (hH : yulFrameHaltsList xs = false)
    (extraFuel G : Nat) (state : IRState)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hfits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) xs) +
      (spliceLockReleaseList (lockReleaseStmt slot) xs).length + 4 ≤
      (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) xs).length + extraFuel + 1)
    (hG : stmtsFuelBound xs ≤ G) :
    execIRStmts ((genParamLoads params).length +
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) xs).length +
        extraFuel + 1) state
      (genParamLoads params ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) xs)) =
      if state.transientStorage slot = 1 then
        .revert (ParamLoading.applyBindingsToIRState state bindings)
      else
        (match execIRStmts G { ParamLoading.applyBindingsToIRState state bindings with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } xs with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  rw [ParamLoading.exec_genParamLoads_supported_then_extraFuel state params bindings
    _ extraFuel hsupported hfits hbind]
  have htrans := applyBindingsToIRState_transient bindings state
  rw [execIRStmts_guardedUnit_fallthrough slot hslot xs hSS hH _ G
    (ParamLoading.applyBindingsToIRState state bindings)
    (by rw [htrans]; exact hlock01) hF hG, htrans]

/-- Halting twin of `execIRStmts_guardedFunction_fallthrough`: bodies ending
in a modeled halt. -/
theorem execIRStmts_guardedFunction_halting (slot : Nat)
    (hslot : slot < Compiler.Constants.evmModulus)
    (params : List Param) (bindings : List (String × Nat))
    (ys : List YulStmt) (h : YulStmt)
    (hSS : SpliceSimList (ys ++ [h])) (hmh : ModeledHalt h)
    (extraFuel G : Nat) (state : IRState)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hfits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (ys ++ [h])) + 2 ≤
      (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
        extraFuel + 1)
    (hG : stmtsFuelBound (ys ++ [h]) ≤ G) :
    execIRStmts ((genParamLoads params).length +
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
        extraFuel + 1) state
      (genParamLoads params ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h]))) =
      if state.transientStorage slot = 1 then
        .revert (ParamLoading.applyBindingsToIRState state bindings)
      else
        (match execIRStmts G { ParamLoading.applyBindingsToIRState state bindings with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } (ys ++ [h]) with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  rw [ParamLoading.exec_genParamLoads_supported_then_extraFuel state params bindings
    _ extraFuel hsupported hfits hbind]
  have htrans := applyBindingsToIRState_transient bindings state
  rw [execIRStmts_guardedUnit_halting slot hslot ys h hSS hmh _ G
    (ParamLoading.applyBindingsToIRState state bindings)
    (by rw [htrans]; exact hlock01) hF hG, htrans]

/-- Correctness of the post-compilation guard transformation itself: for an
annotated function whose compiled body has the standard loads-then-body
shape, the transformed function's body executes exactly as the guarded
composition — locked entry reverts after binding, free entry runs the body
from the acquired bound state with successful outcomes released.  This is the
`compileGuardedFunctionSpec`-level correctness statement; consuming it from
the whole-contract preservation theorems is the remaining (additive)
integration step. -/
theorem attachNonReentrantGuard_exec (fields : List Field)
    (spec : FunctionSpec) (irFn guardedFn : IRFunction) (lockField : String)
    (field : Field) (slot : Nat) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (extraFuel G : Nat) (state : IRState)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec irFn = .ok guardedFn)
    (hbody : irFn.body = genParamLoads spec.bindingParams ++ bodyStmts)
    (hslot : slot < Compiler.Constants.evmModulus)
    (hSS : SpliceSimList bodyStmts)
    (hH : yulFrameHaltsList bodyStmts = false)
    (hsupported : ∀ param ∈ spec.bindingParams, SupportedExternalScalarParamType param.ty)
    (hfits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.bindingParams state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts) +
      (spliceLockReleaseList (lockReleaseStmt slot) bodyStmts).length + 4 ≤
      (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts).length +
        extraFuel + 1)
    (hG : stmtsFuelBound bodyStmts ≤ G) :
    execIRStmts ((genParamLoads spec.bindingParams).length +
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts).length +
        extraFuel + 1) state guardedFn.body =
      if state.transientStorage slot = 1 then
        .revert (ParamLoading.applyBindingsToIRState state bindings)
      else
        (match execIRStmts G { ParamLoading.applyBindingsToIRState state bindings with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } bodyStmts with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  have hshape := attachNonReentrantGuard_some_shape fields spec irFn lockField
    field slot hlock hfield
  rw [hguard] at hshape
  have hbodyEq : guardedFn.body =
      genParamLoads spec.bindingParams ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) bodyStmts) := by
    have := congrArg IRFunction.body (Except.ok.inj hshape)
    simpa [hbody, List.take_left, List.drop_left, List.append_assoc] using this
  rw [hbodyEq]
  exact execIRStmts_guardedFunction_fallthrough slot hslot spec.bindingParams bindings
    bodyStmts hSS hH extraFuel G state hsupported hfits hbind hlock01 hF hG

/-- Halting twin of `attachNonReentrantGuard_exec`. -/
theorem attachNonReentrantGuard_exec_halting (fields : List Field)
    (spec : FunctionSpec) (irFn guardedFn : IRFunction) (lockField : String)
    (field : Field) (slot : Nat) (ys : List YulStmt) (h : YulStmt)
    (bindings : List (String × Nat)) (extraFuel G : Nat) (state : IRState)
    (hlock : spec.nonReentrantLock = some lockField)
    (hfield : findFieldWithResolvedSlot fields lockField = some (field, slot))
    (hguard : attachNonReentrantGuard fields spec irFn = .ok guardedFn)
    (hbody : irFn.body = genParamLoads spec.bindingParams ++ (ys ++ [h]))
    (hslot : slot < Compiler.Constants.evmModulus)
    (hSS : SpliceSimList (ys ++ [h])) (hmh : ModeledHalt h)
    (hsupported : ∀ param ∈ spec.bindingParams, SupportedExternalScalarParamType param.ty)
    (hfits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.bindingParams state.calldata =
      some bindings)
    (hlock01 : state.transientStorage slot = 0 ∨ state.transientStorage slot = 1)
    (hF : stmtsFuelBound (spliceLockReleaseList (lockReleaseStmt slot)
      (ys ++ [h])) + 2 ≤
      (guardPrologueStmts slot ++
        applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
        extraFuel + 1)
    (hG : stmtsFuelBound (ys ++ [h]) ≤ G) :
    execIRStmts ((genParamLoads spec.bindingParams).length +
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])).length +
        extraFuel + 1) state guardedFn.body =
      if state.transientStorage slot = 1 then
        .revert (ParamLoading.applyBindingsToIRState state bindings)
      else
        (match execIRStmts G { ParamLoading.applyBindingsToIRState state bindings with
            transientStorage := fun o => if o = slot then 1
              else state.transientStorage o } (ys ++ [h]) with
          | .continue s => .continue (releaseState slot s)
          | .return v s => .return v (releaseState slot s)
          | .stop s => .stop (releaseState slot s)
          | .revert s => .revert s) := by
  have hshape := attachNonReentrantGuard_some_shape fields spec irFn lockField
    field slot hlock hfield
  rw [hguard] at hshape
  have hbodyEq : guardedFn.body =
      genParamLoads spec.bindingParams ++
        (guardPrologueStmts slot ++
          applyLockReleaseOnExits (lockReleaseStmt slot) (ys ++ [h])) := by
    have := congrArg IRFunction.body (Except.ok.inj hshape)
    simpa [hbody, List.take_left, List.drop_left, List.append_assoc] using this
  rw [hbodyEq]
  exact execIRStmts_guardedFunction_halting slot hslot spec.bindingParams bindings
    ys h hSS hmh extraFuel G state hsupported hfits hbind hlock01 hF hG

end Compiler.Proofs.IRGeneration
