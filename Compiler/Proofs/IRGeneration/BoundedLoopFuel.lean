import Compiler.Proofs.IRGeneration.FuelBound
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas

/-!
# Fuel stability for literal-bound `forEach` loops (#2276 follow-up)

`FuelBound.lean` gives fuel stability for the loop-free fragment.  This
module extends it to the steady-state loop emitted by the `forEach`
lowering — `for_ [] lt(idx, cnt) [idx := add(idx, 1)] body` — under the
loop invariant that drives it: `idx` holds `k`, `cnt` holds `C`, and the
body preserves both counters (a semantic hypothesis here; the syntactic
discharge via a decidable body checker lands with the fragment admission).

Fuel accounting: each iteration of the interpreter's `for_` case peels one
`succ` (the recursive `for_ []` re-entry), while `body`/`post` run at the
current (decreasing) fuel.  So `C - k` iterations plus headroom for the
deepest subterm bound the whole loop:
`boundedForFuel body C k = (C - k) + max(bodyBound, postBound) + 1`.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul

/-- Variable lookup after `setVar` at the same name. -/
theorem IRState.getVar_setVar_self (s : IRState) (name : String) (v : Nat) :
    (s.setVar name v).getVar name = some v := by
  simp [IRState.getVar, IRState.setVar]

/-- The post statement of the `forEach` lowering: increment the counter. -/
theorem execIRStmts_forEach_post (idxN : String) (fuel : Nat)
    (state : IRState) (k : Nat)
    (hidx : state.getVar idxN = some k)
    (hk : k + 1 < Compiler.Constants.evmModulus)
    (hfuel : 2 ≤ fuel) :
    execIRStmts fuel state
        [.assign idxN (.call "add" [.ident idxN, .lit 1])] =
      .continue (state.setVar idxN (k + 1)) := by
  rcases Nat.exists_eq_add_of_le hfuel with ⟨extra, rfl⟩
  rw [Nat.add_comm]
  have hkM : k < Compiler.Constants.evmModulus := by omega
  simp only [execIRStmts, execIRStmt]
  simp only [evalIRExpr, evalIRCall, evalIRExprs, hidx]
  simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Nat.mod_eq_of_lt hk]

/-- The loop condition of the `forEach` lowering evaluates to the comparison
of the two counters. -/
theorem evalIRExpr_forEach_cond (idxN cntN : String) (state : IRState)
    (k C : Nat)
    (hidx : state.getVar idxN = some k)
    (hcnt : state.getVar cntN = some C)
    (hkM : k < Compiler.Constants.evmModulus)
    (hCM : C < Compiler.Constants.evmModulus) :
    evalIRExpr state (.call "lt" [.ident idxN, .ident cntN]) =
      some (if k < C then 1 else 0) := by
  simp only [evalIRExpr, evalIRCall, evalIRExprs, hidx, hcnt]
  simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hCM]

/-- Fuel bound for the steady-state `forEach` loop with `C - k` iterations
remaining. -/
def boundedForFuel (body : List YulStmt) (C k : Nat) : Nat :=
  (C - k) + Nat.max (stmtsFuelBound body)
    (stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])]) + 1

/-- The post bound is name-independent (structural). -/
theorem stmtsFuelBound_post_eq (idxN : String) :
    stmtsFuelBound [.assign idxN (.call "add" [.ident idxN, .lit 1])] =
      stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])] := rfl

/-- The steady-state loop of the `forEach` lowering. -/
private abbrev forEachLoop (idxN cntN : String) (body : List YulStmt) : YulStmt :=
  .for_ [] (.call "lt" [.ident idxN, .ident cntN])
    [.assign idxN (.call "add" [.ident idxN, .lit 1])] body

/-- Fuel facts for one more remaining iteration: the bound peels one `succ`
and still covers the body and the post statement. -/
private theorem boundedForFuel_succ_facts (body : List YulStmt) (C k : Nat) (hk : k < C) :
    boundedForFuel body C k = Nat.succ (boundedForFuel body C (k + 1)) ∧
      stmtsFuelBound body ≤ boundedForFuel body C (k + 1) ∧
      2 ≤ boundedForFuel body C (k + 1) := by
  have hpost : 2 ≤ stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])] := by
    simp [stmtsFuelBound, stmtFuelBound]
  have hr : stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])] ≤ Nat.max
      (stmtsFuelBound body) (stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])]) :=
    Nat.le_max_right _ _
  have hl : stmtsFuelBound body ≤ Nat.max (stmtsFuelBound body)
      (stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])]) := Nat.le_max_left _ _
  unfold boundedForFuel
  omega

/-- An empty-init loop iteration whose body stops the loop yields the body
result at both fuels when the body agrees at both fuels. -/
private theorem execIRStmt_for_empty_body_noncontinue_stable (G F : Nat) (state : IRState)
    (post body : List YulStmt) (cond : YulExpr) (r : IRExecResult)
    (hcond : evalIRExpr state cond = some 1)
    (hbodyEq : execIRStmts G state body = execIRStmts F state body)
    (hbody : execIRStmts F state body = r) (hterm : ∀ s, r ≠ .continue s) :
    execIRStmt (Nat.succ G) state (.for_ [] cond post body) =
      execIRStmt (Nat.succ F) state (.for_ [] cond post body) := by
  have hnil : ∀ (n : Nat), execIRStmts n state [] = .continue state :=
    fun n => by simp [execIRStmts]
  rw [execIRStmt_for_body_noncontinue G state state [] post body cond 1 r (hnil _) hcond
      one_ne_zero (hbodyEq.trans hbody) hterm,
    execIRStmt_for_body_noncontinue F state state [] post body cond 1 r (hnil _) hcond
      one_ne_zero hbody hterm]

/-- One empty-init loop iteration agrees at fuels `G + 1` and `F + 1` when the
body agrees at both fuels and, after a continuing body, the post statement and
the remaining loop agree as well. -/
private theorem execIRStmt_for_empty_stable_step (G F : Nat) (state : IRState)
    (post body : List YulStmt) (cond : YulExpr) (hcond : evalIRExpr state cond = some 1)
    (hbodyEq : execIRStmts G state body = execIRStmts F state body)
    (hcont : ∀ s'', execIRStmts F state body = .continue s'' → ∃ sPost,
      execIRStmts G s'' post = .continue sPost ∧ execIRStmts F s'' post = .continue sPost ∧
      execIRStmt G sPost (.for_ [] cond post body) =
        execIRStmt F sPost (.for_ [] cond post body)) :
    execIRStmt (Nat.succ G) state (.for_ [] cond post body) =
      execIRStmt (Nat.succ F) state (.for_ [] cond post body) := by
  have hnil : ∀ (n : Nat), execIRStmts n state [] = .continue state :=
    fun n => by simp [execIRStmts]
  cases hbody : execIRStmts F state body with
  | «continue» s'' =>
      obtain ⟨sPost, hpostG, hpostF, hrec⟩ := hcont s'' hbody
      rw [execIRStmt_for_one_continue G state state s'' sPost [] post body cond 1 (hnil _)
          hcond one_ne_zero (hbodyEq.trans hbody) hpostG,
        execIRStmt_for_one_continue F state state s'' sPost [] post body cond 1 (hnil _)
          hcond one_ne_zero hbody hpostF]
      exact hrec
  | «return» _ _ | stop _ | revert _ =>
      exact execIRStmt_for_empty_body_noncontinue_stable G F state post body
        cond _ hcond hbodyEq hbody (fun s hh => by cases hh)

/-- Base case of bounded-loop fuel stability: no iterations remain, so the
condition fails at both fuels. -/
private theorem execIRStmt_boundedFor_stable_zero (idxN cntN : String) (body : List YulStmt)
    (k : Nat) (state : IRState) (f : Nat) (hidx : state.getVar idxN = some k)
    (hcnt : state.getVar cntN = some k) (hCM : k < Compiler.Constants.evmModulus) :
    execIRStmt (boundedForFuel body k k + f) state (forEachLoop idxN cntN body) =
      execIRStmt (boundedForFuel body k k) state (forEachLoop idxN cntN body) := by
  have hcond := evalIRExpr_forEach_cond idxN cntN state k k hidx hcnt hCM hCM
  rw [if_neg (by omega)] at hcond
  have hnil : ∀ (F : Nat), execIRStmts F state [] = .continue state :=
    fun F => by simp [execIRStmts]
  rw [show boundedForFuel body k k + f = Nat.succ (boundedForFuel body k k - 1 + f) from by
      unfold boundedForFuel; omega,
    show boundedForFuel body k k = Nat.succ (boundedForFuel body k k - 1) from by
      unfold boundedForFuel; omega,
    execIRStmt_for_init_cond_zero _ state state [] _ body _ (hnil _) hcond,
    execIRStmt_for_init_cond_zero _ state state [] _ body _ (hnil _) hcond]

/-- Inductive step of bounded-loop fuel stability, given stability for one
fewer remaining iteration. -/
private theorem execIRStmt_boundedFor_stable_succ (idxN cntN : String) (hne : idxN ≠ cntN)
    (body : List YulStmt) (hLF : LoopFreeList body)
    (hpres : ∀ (g : Nat) (s s' : IRState), execIRStmts g s body = .continue s' →
      s'.getVar idxN = s.getVar idxN ∧ s'.getVar cntN = s.getVar cntN)
    (k C : Nat) (state : IRState) (f : Nat) (hidx : state.getVar idxN = some k)
    (hcnt : state.getVar cntN = some C) (hk : k < C) (hCM : C < Compiler.Constants.evmModulus)
    (ih : ∀ (state : IRState) (f : Nat), state.getVar idxN = some (k + 1) →
      state.getVar cntN = some C →
      execIRStmt (boundedForFuel body C (k + 1) + f) state (forEachLoop idxN cntN body) =
        execIRStmt (boundedForFuel body C (k + 1)) state (forEachLoop idxN cntN body)) :
    execIRStmt (boundedForFuel body C k + f) state (forEachLoop idxN cntN body) =
      execIRStmt (boundedForFuel body C k) state (forEachLoop idxN cntN body) := by
  have hcond := evalIRExpr_forEach_cond idxN cntN state k C hidx hcnt (by omega) hCM
  rw [if_pos hk] at hcond
  obtain ⟨hsucc, hFbody, hF2⟩ := boundedForFuel_succ_facts body C k hk
  rw [hsucc, show Nat.succ (boundedForFuel body C (k + 1)) + f =
    Nat.succ (boundedForFuel body C (k + 1) + f) from by omega]
  refine execIRStmt_for_empty_stable_step _ _ state _ body _ hcond
    (execIRStmts_stable_of_le body hLF _ _ state (by omega) hFbody) (fun s'' hbody => ?_)
  obtain ⟨hidx'', hcnt''⟩ := hpres _ state s'' hbody
  exact ⟨s''.setVar idxN (k + 1), execIRStmts_forEach_post idxN _ s'' k (hidx''.trans hidx)
    (by omega) (by omega), execIRStmts_forEach_post idxN _ s'' k (hidx''.trans hidx) (by omega)
    hF2, ih _ f (IRState.getVar_setVar_self s'' idxN (k + 1))
      ((IRState.getVar_setVar_ne s'' (k + 1) (Ne.symm hne)).trans (hcnt''.trans hcnt))⟩

/-- Fuel stability for the steady-state literal-bound loop: with the counter
invariant in hand, execution at the structural bound and at any larger fuel
agree.  The body's counter preservation is a semantic hypothesis; the
decidable syntactic discharge ships with the fragment admission. -/
theorem execIRStmt_boundedFor_stable
    (idxN cntN : String) (hne : idxN ≠ cntN)
    (body : List YulStmt) (hLF : LoopFreeList body)
    (hpres : ∀ (g : Nat) (s s' : IRState),
      execIRStmts g s body = .continue s' →
      s'.getVar idxN = s.getVar idxN ∧ s'.getVar cntN = s.getVar cntN) :
    ∀ (gas k C : Nat), gas = C - k →
      ∀ (state : IRState) (f : Nat),
      state.getVar idxN = some k →
      state.getVar cntN = some C →
      k ≤ C → C < Compiler.Constants.evmModulus →
      execIRStmt (boundedForFuel body C k + f) state
          (.for_ [] (.call "lt" [.ident idxN, .ident cntN])
            [.assign idxN (.call "add" [.ident idxN, .lit 1])] body) =
        execIRStmt (boundedForFuel body C k) state
          (.for_ [] (.call "lt" [.ident idxN, .ident cntN])
            [.assign idxN (.call "add" [.ident idxN, .lit 1])] body) := by
  intro gas
  induction gas with
  | zero =>
      intro k C hgas state f hidx hcnt hkC hCM
      obtain rfl : k = C := by omega
      exact execIRStmt_boundedFor_stable_zero idxN cntN body k state f hidx hcnt hCM
  | succ gas ih =>
      intro k C hgas state f hidx hcnt hkC hCM
      exact execIRStmt_boundedFor_stable_succ idxN cntN hne body hLF hpres k C state f hidx
        hcnt (by omega) hCM (fun s f' h1 h2 => ih (k + 1) C (by omega) s f' h1 h2 (by omega) hCM)

/-- Consumer API: any two fuels at or above the bound execute the
steady-state loop identically. -/
theorem execIRStmt_boundedFor_stable_of_le
    (idxN cntN : String) (hne : idxN ≠ cntN)
    (body : List YulStmt) (hLF : LoopFreeList body)
    (hpres : ∀ (g : Nat) (s s' : IRState),
      execIRStmts g s body = .continue s' →
      s'.getVar idxN = s.getVar idxN ∧ s'.getVar cntN = s.getVar cntN)
    (k C : Nat) (state : IRState)
    (hidx : state.getVar idxN = some k)
    (hcnt : state.getVar cntN = some C)
    (hkC : k ≤ C) (hCM : C < Compiler.Constants.evmModulus)
    (F G : Nat)
    (hF : boundedForFuel body C k ≤ F) (hG : boundedForFuel body C k ≤ G) :
    execIRStmt F state
        (.for_ [] (.call "lt" [.ident idxN, .ident cntN])
          [.assign idxN (.call "add" [.ident idxN, .lit 1])] body) =
      execIRStmt G state
        (.for_ [] (.call "lt" [.ident idxN, .ident cntN])
          [.assign idxN (.call "add" [.ident idxN, .lit 1])] body) := by
  rw [show F = boundedForFuel body C k + (F - boundedForFuel body C k) from by
      omega,
    execIRStmt_boundedFor_stable idxN cntN hne body hLF hpres (C - k) k C rfl
      state _ hidx hcnt hkC hCM,
    show G = boundedForFuel body C k + (G - boundedForFuel body C k) from by
      omega,
    execIRStmt_boundedFor_stable idxN cntN hne body hLF hpres (C - k) k C rfl
      state _ hidx hcnt hkC hCM]

/-! ### Fuel bound vs. term size

`execIRFunction` budgets fuel at `sizeOf fn.body + 1`; these lemmas show the
structural fuel bound is always within that budget — the seam the upcoming
`forEach` fragment admission threads through (the literal bound `N` is part
of the compiled loop's `sizeOf` via its `let cnt := lit N` initializer). -/

theorem yulStmt_sizeOf_pos (s : YulStmt) : 0 < sizeOf s := by
  cases s <;> simp

mutual

/-- The structural fuel bound is dominated by term size: the `sizeOf`-based
fuel budget of `execIRFunction` always covers the loop-free bound. -/
theorem stmtFuelBound_le_sizeOf : ∀ (s : YulStmt), stmtFuelBound s ≤ sizeOf s
  | .if_ cond body => by
      have h := stmtsFuelBound_le_sizeOf body
      simp only [stmtFuelBound]
      simp
      omega
  | .block stmts => by
      have h := stmtsFuelBound_le_sizeOf stmts
      simp only [stmtFuelBound]
      simp
      omega
  | .switch e cases dflt => by
      have hc := casesFuelBound_le_sizeOf cases
      have hd := dfltFuelBound_le_sizeOf dflt
      have hmax : Nat.max (casesFuelBound cases) (dfltFuelBound dflt) ≤
          sizeOf cases + sizeOf dflt :=
        Nat.max_le.mpr ⟨Nat.le_trans hc (Nat.le_add_right _ _),
          Nat.le_trans hd (Nat.le_add_left _ _)⟩
      simp only [stmtFuelBound]
      simp
      omega
  | .comment _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .let_ _ e => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .letMany _ _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .assign _ _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .leave => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .exprStmt _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .funcDef _ _ _ _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _
  | .for_ _ _ _ _ => by
      simp only [stmtFuelBound]
      exact yulStmt_sizeOf_pos _

theorem casesFuelBound_le_sizeOf :
    ∀ (cs : List (Nat × List YulStmt)), casesFuelBound cs ≤ sizeOf cs
  | [] => by simp [casesFuelBound]
  | (k, body) :: rest => by
      have h1 := stmtsFuelBound_le_sizeOf body
      have h2 := casesFuelBound_le_sizeOf rest
      have hmax : Nat.max (stmtsFuelBound body) (casesFuelBound rest) ≤
          sizeOf body + sizeOf rest :=
        Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _),
          Nat.le_trans h2 (Nat.le_add_left _ _)⟩
      simp only [casesFuelBound]
      simp
      omega

theorem dfltFuelBound_le_sizeOf :
    ∀ (d : Option (List YulStmt)), dfltFuelBound d ≤ sizeOf d
  | none => by simp [dfltFuelBound]
  | some stmts => by
      have h := stmtsFuelBound_le_sizeOf stmts
      simp only [dfltFuelBound]
      simp
      omega

theorem stmtsFuelBound_le_sizeOf :
    ∀ (xs : List YulStmt), stmtsFuelBound xs ≤ sizeOf xs
  | [] => by simp [stmtsFuelBound]
  | x :: rest => by
      have h1 := stmtFuelBound_le_sizeOf x
      have h2 := stmtsFuelBound_le_sizeOf rest
      have h3 := yulStmt_sizeOf_pos x
      have hmax : Nat.max (stmtFuelBound x) (stmtsFuelBound rest) ≤
          sizeOf x + sizeOf rest :=
        Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _),
          Nat.le_trans h2 (Nat.le_add_left _ _)⟩
      simp only [stmtsFuelBound]
      simp
      omega

end

end Compiler.Proofs.IRGeneration
