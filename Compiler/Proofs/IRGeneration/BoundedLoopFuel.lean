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

/-- `find?` skips entries removed by a name filter that cannot match. -/
private theorem find?_filter_ne_name (other name : String) (h : other ≠ name) :
    ∀ (l : List (String × Nat)),
      (l.filter (·.1 != name)).find? (·.1 == other) =
        l.find? (·.1 == other)
  | [] => rfl
  | (n', v') :: rest => by
      by_cases hn : n' = name
      · subst hn
        rw [List.filter_cons_of_neg (by simp),
          List.find?_cons_of_neg (by simp [Ne.symm h]),
          find?_filter_ne_name other _ h rest]
      · rw [List.filter_cons_of_pos (by simp [hn])]
        by_cases ho : n' = other
        · subst ho
          rw [List.find?_cons_of_pos (by simp),
            List.find?_cons_of_pos (by simp)]
        · rw [List.find?_cons_of_neg (by simp [ho]),
            List.find?_cons_of_neg (by simp [ho]),
            find?_filter_ne_name other name h rest]

/-- Variable lookup after `setVar` at a different name. -/
theorem IRState.getVar_setVar_ne (s : IRState) (name other : String)
    (v : Nat) (h : other ≠ name) :
    (s.setVar name v).getVar other = s.getVar other := by
  simp only [IRState.getVar, IRState.setVar, List.find?_cons]
  have hbeq : ((name, v).1 == other) = false := by
    simp [Ne.symm h]
  rw [hbeq]
  rw [find?_filter_ne_name other name h s.vars]

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
      have hkeqC : k = C := by omega
      subst hkeqC
      have hcond := evalIRExpr_forEach_cond idxN cntN state k k hidx hcnt
        (by omega) hCM
      rw [if_neg (by omega)] at hcond
      have hnil : ∀ (F : Nat), execIRStmts F state [] = .continue state :=
        fun F => by simp [execIRStmts]
      rw [show boundedForFuel body k k + f =
            Nat.succ (boundedForFuel body k k - 1 + f) from by
          unfold boundedForFuel; omega,
        show boundedForFuel body k k =
            Nat.succ (boundedForFuel body k k - 1) from by
          unfold boundedForFuel; omega,
        execIRStmt_for_init_cond_zero _ state state []
          [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
          (.call "lt" [.ident idxN, .ident cntN]) (hnil _) hcond,
        execIRStmt_for_init_cond_zero _ state state []
          [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
          (.call "lt" [.ident idxN, .ident cntN]) (hnil _) hcond]
  | succ gas ih =>
      intro k C hgas state f hidx hcnt hkC hCM
      have hkltC : k < C := by omega
      have hcond := evalIRExpr_forEach_cond idxN cntN state k C hidx hcnt
        (by omega) hCM
      rw [if_pos hkltC] at hcond
      have hnil : ∀ (F : Nat), execIRStmts F state [] = .continue state :=
        fun F => by simp [execIRStmts]
      have hone : (1 : Nat) ≠ 0 := by omega
      set F := boundedForFuel body C (k + 1) with hF
      have hpost2 : 2 ≤ stmtsFuelBound
          [.assign "i" (.call "add" [.ident "i", .lit 1])] := by
        simp [stmtsFuelBound, stmtFuelBound]
      have hFbody : stmtsFuelBound body ≤ F := by
        rw [hF]
        calc stmtsFuelBound body
            ≤ Nat.max (stmtsFuelBound body)
                (stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])]) :=
              Nat.le_max_left _ _
          _ ≤ boundedForFuel body C (k + 1) := by
              unfold boundedForFuel; omega
      have hF2 : 2 ≤ F := by
        rw [hF]
        calc (2 : Nat)
            ≤ stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])] :=
              hpost2
          _ ≤ Nat.max (stmtsFuelBound body)
                (stmtsFuelBound [.assign "i" (.call "add" [.ident "i", .lit 1])]) :=
              Nat.le_max_right _ _
          _ ≤ boundedForFuel body C (k + 1) := by
              unfold boundedForFuel; omega
      rw [show boundedForFuel body C k + f = Nat.succ (F + f) from by
          rw [hF]; unfold boundedForFuel; omega,
        show boundedForFuel body C k = Nat.succ F from by
          rw [hF]; unfold boundedForFuel; omega]
      have hbodyEq : execIRStmts (F + f) state body =
          execIRStmts F state body :=
        execIRStmts_stable_of_le body hLF _ _ state (by omega) hFbody
      cases hbody : execIRStmts F state body with
      | «return» v st =>
          rw [execIRStmt_for_body_noncontinue (F + f) state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.return v st)
              (hnil _) hcond hone (hbodyEq.trans hbody)
              (fun s hh => by cases hh),
            execIRStmt_for_body_noncontinue F state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.return v st)
              (hnil _) hcond hone hbody (fun s hh => by cases hh)]
      | stop st =>
          rw [execIRStmt_for_body_noncontinue (F + f) state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.stop st)
              (hnil _) hcond hone (hbodyEq.trans hbody)
              (fun s hh => by cases hh),
            execIRStmt_for_body_noncontinue F state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.stop st)
              (hnil _) hcond hone hbody (fun s hh => by cases hh)]
      | revert st =>
          rw [execIRStmt_for_body_noncontinue (F + f) state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.revert st)
              (hnil _) hcond hone (hbodyEq.trans hbody)
              (fun s hh => by cases hh),
            execIRStmt_for_body_noncontinue F state state []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1 (.revert st)
              (hnil _) hcond hone hbody (fun s hh => by cases hh)]
      | «continue» s'' =>
          obtain ⟨hidx'', hcnt''⟩ := hpres _ state s'' hbody
          rw [hidx] at hidx''
          rw [hcnt] at hcnt''
          have hpost1 : execIRStmts (F + f) s''
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] =
              .continue (s''.setVar idxN (k + 1)) :=
            execIRStmts_forEach_post idxN _ s'' k hidx'' (by omega) (by omega)
          have hpost2 : execIRStmts F s''
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] =
              .continue (s''.setVar idxN (k + 1)) :=
            execIRStmts_forEach_post idxN _ s'' k hidx'' (by omega) hF2
          rw [execIRStmt_for_one_continue (F + f) state state s''
              (s''.setVar idxN (k + 1)) []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1
              (hnil _) hcond hone (hbodyEq.trans hbody) hpost1,
            execIRStmt_for_one_continue F state state s''
              (s''.setVar idxN (k + 1)) []
              [.assign idxN (.call "add" [.ident idxN, .lit 1])] body
              (.call "lt" [.ident idxN, .ident cntN]) 1
              (hnil _) hcond hone hbody hpost2]
          have hidx3 : (s''.setVar idxN (k + 1)).getVar idxN = some (k + 1) :=
            IRState.getVar_setVar_self s'' idxN (k + 1)
          have hcnt3 : (s''.setVar idxN (k + 1)).getVar cntN = some C := by
            rw [IRState.getVar_setVar_ne s'' idxN cntN (k + 1) (Ne.symm hne)]
            exact hcnt''
          exact ih (k + 1) C (by omega) (s''.setVar idxN (k + 1)) f
            hidx3 hcnt3 (by omega) hCM

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
