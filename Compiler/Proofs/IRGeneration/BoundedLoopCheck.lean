import Compiler.Proofs.IRGeneration.BoundedLoopFuel

/-!
# Decidable counter-preservation checker for the bounded-loop fragment

`execIRStmt_boundedFor_stable` takes the loop-counter preservation of the
body as a semantic hypothesis.  This module provides the executable mirror:
`varUntouchedCheck v` scans a statement for any binding or assignment of
`v` (loops excluded, matching `LoopFree`), and the soundness theorem
discharges the semantic hypothesis for any checked body — so fragment
membership for a concrete compiled `forEach` body is a `decide` obligation,
in the same style as `spliceSimCheck`.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul

/-- The state carried by an execution result. -/
def IRExecResult.state : IRExecResult → IRState
  | .continue s => s
  | .return _ s => s
  | .stop s => s
  | .revert s => s

mutual

/-- Executable check: the statement never binds or assigns `v` (loops are
outside the fragment, mirroring `LoopFree`). -/
def varUntouchedCheck (v : String) : YulStmt → Bool
  | .let_ n _ => n != v
  | .letMany ns _ => !(ns.contains v)
  | .assign n _ => n != v
  | .if_ _ body => varUntouchedCheckList v body
  | .block stmts => varUntouchedCheckList v stmts
  | .switch _ cases dflt =>
      varUntouchedCheckCases v cases && varUntouchedCheckDflt v dflt
  | .for_ _ _ _ _ => false
  | _ => true

def varUntouchedCheckCases (v : String) : List (Nat × List YulStmt) → Bool
  | [] => true
  | c :: rest => varUntouchedCheckList v c.2 && varUntouchedCheckCases v rest

def varUntouchedCheckDflt (v : String) : Option (List YulStmt) → Bool
  | none => true
  | some stmts => varUntouchedCheckList v stmts

def varUntouchedCheckList (v : String) : List YulStmt → Bool
  | [] => true
  | s :: rest => varUntouchedCheck v s && varUntouchedCheckList v rest

end

/-- Yul log emission never touches variables. -/
theorem applyYulLogCall?_vars (state next : IRState) (func : String)
    (argVals : List Nat) (h : applyYulLogCall? state func argVals = some next) :
    next.vars = state.vars := by
  unfold applyYulLogCall? at h
  repeat' split at h
  all_goals ((cases h) <;> rfl)

/-- Expression statements never touch variables: every branch of the
interpreter's `exprStmt` case updates storage, memory, transient storage,
or the event log — never the variable environment. -/
theorem execIRStmt_exprStmt_state_vars (fuel : Nat) (state : IRState)
    (e : YulExpr) :
    ((execIRStmt fuel state (.exprStmt e)).state).vars = state.vars := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [execIRStmt.eq_def]
      repeat' split
      all_goals try subst_vars
      all_goals first
        | rfl
        | exact applyYulLogCall?_vars _ _ _ _ (by assumption)
        | simp_all

/-- `getVar` only depends on `vars`. -/
theorem IRState.getVar_congr_vars (s s' : IRState) (v : String)
    (h : s'.vars = s.vars) : s'.getVar v = s.getVar v := by
  simp [IRState.getVar, h]

/-- Case-branch membership for the checker. -/
theorem varUntouchedCheckCases_mem
    {v : String} {cs : List (Nat × List YulStmt)}
    (h : varUntouchedCheckCases v cs = true)
    {c : Nat × List YulStmt} (hmem : c ∈ cs) :
    varUntouchedCheckList v c.2 = true := by
  induction cs with
  | nil => cases hmem
  | cons x rest ih =>
      obtain ⟨hx, hrest⟩ : varUntouchedCheckList v x.2 = true ∧
          varUntouchedCheckCases v rest = true := by
        simpa [varUntouchedCheckCases, Bool.and_eq_true] using h
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hx
      · exact ih hrest hmem

variable {v : String}

mutual

/-- Soundness: a checked, loop-free statement preserves `getVar v` in every
outcome. -/
theorem execIRStmt_getVar_of_checked :
    ∀ (s : YulStmt), LoopFree s → varUntouchedCheck v s = true →
    ∀ (fuel : Nat) (state : IRState),
      ((execIRStmt fuel state s).state).getVar v = state.getVar v
  | .comment _, _, _, fuel, state => by
      cases fuel <;> rfl
  | .leave, _, _, fuel, state => by
      cases fuel <;> rfl
  | .funcDef _ _ _ _, _, _, fuel, state => by
      cases fuel <;> rfl
  | .letMany _ _, _, _, fuel, state => by
      cases fuel <;> rfl
  | .let_ n value, _, hchk, fuel, state => by
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hne : n ≠ v := by simpa [varUntouchedCheck] using hchk
          show ((match evalIRExpr state value with
            | some w => IRExecResult.continue (state.setVar n w)
            | none => IRExecResult.revert state).state).getVar v =
            state.getVar v
          cases evalIRExpr state value with
          | none => rfl
          | some w =>
              simp only [IRExecResult.state]
              exact IRState.getVar_setVar_ne state n v w (Ne.symm hne)
  | .assign n value, _, hchk, fuel, state => by
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hne : n ≠ v := by simpa [varUntouchedCheck] using hchk
          show ((match evalIRExpr state value with
            | some w => IRExecResult.continue (state.setVar n w)
            | none => IRExecResult.revert state).state).getVar v =
            state.getVar v
          cases evalIRExpr state value with
          | none => rfl
          | some w =>
              simp only [IRExecResult.state]
              exact IRState.getVar_setVar_ne state n v w (Ne.symm hne)
  | .exprStmt e, _, _, fuel, state =>
      IRState.getVar_congr_vars state _ v
        (execIRStmt_exprStmt_state_vars fuel state e)
  | .for_ _ _ _ _, hLF, _, _, _ => absurd hLF (by simp [LoopFree])
  | .if_ cond body, hLF, hchk, fuel, state => by
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hLFb : LoopFreeList body := by simpa [LoopFree] using hLF
          have hchkb : varUntouchedCheckList v body = true := by
            simpa [varUntouchedCheck] using hchk
          show ((match evalIRExpr state cond with
            | some c => if c ≠ 0 then execIRStmts fuel state body
                else IRExecResult.continue state
            | none => IRExecResult.revert state).state).getVar v =
            state.getVar v
          cases evalIRExpr state cond with
          | none => rfl
          | some c =>
              simp only []
              by_cases hc : c ≠ 0
              · rw [if_pos hc]
                exact execIRStmts_getVar_of_checked body hLFb hchkb fuel state
              · rw [if_neg hc]
                rfl
  | .block stmts, hLF, hchk, fuel, state => by
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hLFb : LoopFreeList stmts := by simpa [LoopFree] using hLF
          have hchkb : varUntouchedCheckList v stmts = true := by
            simpa [varUntouchedCheck] using hchk
          show ((execIRStmts fuel state stmts).state).getVar v = state.getVar v
          exact execIRStmts_getVar_of_checked stmts hLFb hchkb fuel state
  | .switch e cases dflt, hLF, hchk, fuel, state => by
      cases fuel with
      | zero => rfl
      | succ fuel =>
          obtain ⟨hLFc, hLFd⟩ : LoopFreeCases cases ∧ LoopFreeDflt dflt := by
            simpa [LoopFree] using hLF
          obtain ⟨hchkc, hchkd⟩ : varUntouchedCheckCases v cases = true ∧
              varUntouchedCheckDflt v dflt = true := by
            simpa [varUntouchedCheck, Bool.and_eq_true] using hchk
          cases heval : evalIRExpr state e with
          | none => simp [execIRStmt, heval, IRExecResult.state]
          | some w =>
              cases hfind : List.find?
                  (fun (c : Nat × List YulStmt) => c.1 == w) cases with
              | some c =>
                  obtain ⟨k, body⟩ := c
                  have hmem := List.mem_of_find?_eq_some hfind
                  simp only [execIRStmt, heval, hfind]
                  exact execIRStmts_getVar_of_checked body
                    (LoopFreeCases.mem hLFc hmem)
                    (varUntouchedCheckCases_mem hchkc hmem) fuel state
              | none =>
                  cases hdd : dflt with
                  | none => simp [execIRStmt, heval, hfind, IRExecResult.state]
                  | some body =>
                      have hLFb : LoopFreeList body := by
                        rw [hdd] at hLFd
                        simpa [LoopFreeDflt] using hLFd
                      have hchkb : varUntouchedCheckList v body = true := by
                        rw [hdd] at hchkd
                        simpa [varUntouchedCheckDflt] using hchkd
                      simp only [execIRStmt, heval, hfind]
                      exact execIRStmts_getVar_of_checked body hLFb hchkb
                        fuel state

/-- List soundness. -/
theorem execIRStmts_getVar_of_checked :
    ∀ (xs : List YulStmt), LoopFreeList xs → varUntouchedCheckList v xs = true →
    ∀ (fuel : Nat) (state : IRState),
      ((execIRStmts fuel state xs).state).getVar v = state.getVar v
  | [], _, _, fuel, state => by
      simp [execIRStmts, IRExecResult.state]
  | x :: rest, hLF, hchk, fuel, state => by
      obtain ⟨hx, hrest⟩ : LoopFree x ∧ LoopFreeList rest := by
        simpa [LoopFreeList] using hLF
      obtain ⟨hchkx, hchkrest⟩ : varUntouchedCheck v x = true ∧
          varUntouchedCheckList v rest = true := by
        simpa [varUntouchedCheckList, Bool.and_eq_true] using hchk
      cases fuel with
      | zero => rfl
      | succ fuel =>
          show ((match execIRStmt fuel state x with
            | .continue s' => execIRStmts fuel s' rest
            | .return w s => IRExecResult.return w s
            | .stop s => IRExecResult.stop s
            | .revert s => IRExecResult.revert s).state).getVar v =
            state.getVar v
          have hhead := execIRStmt_getVar_of_checked x hx hchkx fuel state
          cases hres : execIRStmt fuel state x with
          | «continue» s' =>
              rw [hres] at hhead
              simp only [IRExecResult.state] at hhead
              rw [execIRStmts_getVar_of_checked rest hrest hchkrest fuel s']
              exact hhead
          | «return» w s =>
              rw [hres] at hhead
              exact hhead
          | stop s =>
              rw [hres] at hhead
              exact hhead
          | revert s =>
              rw [hres] at hhead
              exact hhead

end

/-- The bridge to `execIRStmt_boundedFor_stable`'s semantic hypothesis: a
checked body preserves both counters across any `.continue` execution. -/
theorem counter_preservation_of_checked
    (idxN cntN : String) (body : List YulStmt)
    (hLF : LoopFreeList body)
    (hidx : varUntouchedCheckList idxN body = true)
    (hcnt : varUntouchedCheckList cntN body = true) :
    ∀ (g : Nat) (s s' : IRState),
      execIRStmts g s body = .continue s' →
      s'.getVar idxN = s.getVar idxN ∧ s'.getVar cntN = s.getVar cntN := by
  intro g s s' hrun
  constructor
  · have h := execIRStmts_getVar_of_checked (v := idxN) body hLF hidx g s
    rw [hrun] at h
    exact h
  · have h := execIRStmts_getVar_of_checked (v := cntN) body hLF hcnt g s
    rw [hrun] at h
    exact h


/-! ### End-to-end demonstration

A concrete `forEach`-shaped loop body (store the element variable to a
fixed slot) passes both decidable checks, so the stability theorem applies
with every side-condition discharged by `decide` — the per-contract
consumption pattern. -/

example (state : IRState)
    (hidx : state.getVar "__forEach_idx" = some 0)
    (hcnt : state.getVar "__forEach_count" = some 3)
    (F G : Nat)
    (hF : boundedForFuel
      [.assign "v" (.ident "__forEach_idx"),
       .exprStmt (.call "sstore" [.lit 7, .ident "v"])] 3 0 ≤ F)
    (hG : boundedForFuel
      [.assign "v" (.ident "__forEach_idx"),
       .exprStmt (.call "sstore" [.lit 7, .ident "v"])] 3 0 ≤ G) :
    execIRStmt F state
        (.for_ [] (.call "lt" [.ident "__forEach_idx", .ident "__forEach_count"])
          [.assign "__forEach_idx" (.call "add" [.ident "__forEach_idx", .lit 1])]
          [.assign "v" (.ident "__forEach_idx"),
           .exprStmt (.call "sstore" [.lit 7, .ident "v"])]) =
      execIRStmt G state
        (.for_ [] (.call "lt" [.ident "__forEach_idx", .ident "__forEach_count"])
          [.assign "__forEach_idx" (.call "add" [.ident "__forEach_idx", .lit 1])]
          [.assign "v" (.ident "__forEach_idx"),
           .exprStmt (.call "sstore" [.lit 7, .ident "v"])]) :=
  execIRStmt_boundedFor_stable_of_le "__forEach_idx" "__forEach_count"
    (by decide)
    [.assign "v" (.ident "__forEach_idx"),
     .exprStmt (.call "sstore" [.lit 7, .ident "v"])]
    (by constructor <;> trivial)
    (counter_preservation_of_checked "__forEach_idx" "__forEach_count" _
      (by constructor <;> trivial) (by decide) (by decide))
    0 3 state hidx hcnt (by omega) (by decide)
    F G hF hG

end Compiler.Proofs.IRGeneration
