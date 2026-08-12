import Compiler.Proofs.IRGeneration.IRInterpreter

/-!
# Computable fuel bounds for the loop-free fragment (#2276 option (c))

The IR interpreter conflates fuel exhaustion with `.revert`, so naive fuel
monotonicity is false.  For the loop-free fragment, however, a structural
bound suffices: execution at any fuel at or above the bound never hits the
exhaustion branch, so results agree at all such fuels.  This gives the
simulation proofs (nested splice, Tier 4) a way to equate executions at
shifted fuel indices without an interpreter refactor.

Fuel flows non-additively: a statement list at fuel `f+1` runs both its head
and its tail at fuel `f`, so the list bound is the max of its members' bounds
plus one per cons step; `if`/`block`/`switch` add one step above their body
bound.  `for` loops are outside the fragment (`LoopFree` excludes them), and
`funcDef` bodies are skipped by the interpreter.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul

mutual

/-- Structural fuel bound: executing at this fuel or above never exhausts. -/
def stmtFuelBound : YulStmt → Nat
  | .if_ _ body => stmtsFuelBound body + 1
  | .block stmts => stmtsFuelBound stmts + 1
  | .switch _ cases dflt =>
      Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + 1
  | _ => 1

def casesFuelBound : List (Nat × List YulStmt) → Nat
  | [] => 0
  | c :: rest => Nat.max (stmtsFuelBound c.2) (casesFuelBound rest)

def dfltFuelBound : Option (List YulStmt) → Nat
  | none => 0
  | some stmts => stmtsFuelBound stmts

def stmtsFuelBound : List YulStmt → Nat
  | [] => 1
  | s :: rest => Nat.max (stmtFuelBound s) (stmtsFuelBound rest) + 1

end

mutual

/-- The fragment: no `for_` anywhere (interpreted positions only — `funcDef`
bodies are never executed by `execIRStmt`). -/
def LoopFree : YulStmt → Prop
  | .if_ _ body => LoopFreeList body
  | .block stmts => LoopFreeList stmts
  | .switch _ cases dflt => LoopFreeCases cases ∧ LoopFreeDflt dflt
  | .for_ _ _ _ _ => False
  | _ => True

def LoopFreeCases : List (Nat × List YulStmt) → Prop
  | [] => True
  | c :: rest => LoopFreeList c.2 ∧ LoopFreeCases rest

def LoopFreeDflt : Option (List YulStmt) → Prop
  | none => True
  | some stmts => LoopFreeList stmts

def LoopFreeList : List YulStmt → Prop
  | [] => True
  | s :: rest => LoopFree s ∧ LoopFreeList rest

end

/-- Bounds are positive: a bound of `stmtFuelBound` always survives the
`succ` pattern of the interpreter. -/
theorem stmtFuelBound_pos (stmt : YulStmt) : 0 < stmtFuelBound stmt := by
  cases stmt <;> simp [stmtFuelBound]

theorem stmtsFuelBound_pos (stmts : List YulStmt) : 0 < stmtsFuelBound stmts := by
  cases stmts <;> simp [stmtsFuelBound]

/-- Member bounds are dominated by the list bound. -/
theorem stmtFuelBound_le_stmtsFuelBound (s : YulStmt) :
    ∀ (xs : List YulStmt), s ∈ xs → stmtFuelBound s < stmtsFuelBound xs
  | [], h => by cases h
  | x :: rest, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      · exact Nat.lt_succ_of_le (Nat.le_trans
          (Nat.le_of_lt (stmtFuelBound_le_stmtsFuelBound s rest h))
          (Nat.le_max_right _ _))

/-- Case-bound domination by membership. -/
theorem stmtsFuelBound_le_casesFuelBound :
    ∀ (cs : List (Nat × List YulStmt)) (c : Nat × List YulStmt),
      c ∈ cs → stmtsFuelBound c.2 ≤ casesFuelBound cs
  | [], _, h => by cases h
  | _ :: rest, c, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (stmtsFuelBound_le_casesFuelBound rest c h)
          (Nat.le_max_right _ _)

/-- Fragment membership for the branch selected at runtime. -/
theorem LoopFreeCases.mem :
    ∀ {cs : List (Nat × List YulStmt)}, LoopFreeCases cs →
      ∀ {c : Nat × List YulStmt}, c ∈ cs → LoopFreeList c.2 := by
  intro cs h c hmem
  induction cs with
  | nil => cases hmem
  | cons x rest ih =>
      obtain ⟨hx, hrest⟩ := h
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hx
      · exact ih hrest hmem

mutual

/-- Fuel stability: a loop-free statement executes identically at its bound
and at any additional fuel. -/
theorem execIRStmt_stable : ∀ (stmt : YulStmt), LoopFree stmt →
    ∀ (f : Nat) (state : IRState),
      execIRStmt (stmtFuelBound stmt + f) state stmt =
        execIRStmt (stmtFuelBound stmt) state stmt
  | .comment _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .let_ _ _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .letMany _ _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .assign _ _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .leave, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .exprStmt _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .funcDef _ _ _ _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .for_ _ _ _ _, hLF, _, _ => absurd hLF (by simp [LoopFree])
  | .if_ cond body, hLF, f, state => by
      simp only [stmtFuelBound]
      rw [show stmtsFuelBound body + 1 + f = (stmtsFuelBound body + f) + 1 from by omega]
      show (match evalIRExpr state cond with
        | some c => if c ≠ 0 then
            execIRStmts (stmtsFuelBound body + f) state body
          else .continue state
        | none => .revert state) =
      (match evalIRExpr state cond with
        | some c => if c ≠ 0 then
            execIRStmts (stmtsFuelBound body) state body
          else .continue state
        | none => .revert state)
      cases evalIRExpr state cond with
      | none => rfl
      | some c =>
          by_cases hc : c ≠ 0 <;>
            simp [hc, execIRStmts_stable body (by simpa [LoopFree] using hLF) f state]
  | .block stmts, hLF, f, state => by
      simp only [stmtFuelBound]
      rw [show stmtsFuelBound stmts + 1 + f = (stmtsFuelBound stmts + f) + 1 from by omega]
      show execIRStmts (stmtsFuelBound stmts + f) state stmts =
        execIRStmts (stmtsFuelBound stmts) state stmts
      exact execIRStmts_stable stmts (by simpa [LoopFree] using hLF) f state
  | .switch e cases dflt, hLF, f, state => by
      simp only [stmtFuelBound]
      rw [show Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + 1 + f =
        (Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + f) + 1 from by omega]
      obtain ⟨hcases, hdflt⟩ : LoopFreeCases cases ∧ LoopFreeDflt dflt := by
        simpa [LoopFree] using hLF
      cases heval : evalIRExpr state e with
      | none => simp [execIRStmt, heval]
      | some v =>
          cases hfind : List.find? (fun (c : Nat × List YulStmt) => c.1 == v) cases with
          | some c =>
              obtain ⟨k, body⟩ := c
              have hmem := List.mem_of_find?_eq_some hfind
              have hle : stmtsFuelBound body ≤
                  Nat.max (casesFuelBound cases) (dfltFuelBound dflt) :=
                Nat.le_trans (stmtsFuelBound_le_casesFuelBound cases (k, body) hmem)
                  (Nat.le_max_left _ _)
              have hLFb := LoopFreeCases.mem hcases hmem
              simp only [execIRStmt, heval, hfind]
              rw [show Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + f =
                  stmtsFuelBound body + (Nat.max (casesFuelBound cases)
                    (dfltFuelBound dflt) - stmtsFuelBound body + f) from by omega,
                execIRStmts_stable body hLFb _ state,
                show Nat.max (casesFuelBound cases) (dfltFuelBound dflt) =
                  stmtsFuelBound body + (Nat.max (casesFuelBound cases)
                    (dfltFuelBound dflt) - stmtsFuelBound body) from by omega,
                execIRStmts_stable body hLFb _ state]
          | none =>
              cases hdd : dflt with
              | none => simp [execIRStmt, heval, hfind]
              | some body =>
                  have hLFb : LoopFreeList body := by
                    rw [hdd] at hdflt
                    simpa [LoopFreeDflt] using hdflt
                  have hle : stmtsFuelBound body ≤
                      Nat.max (casesFuelBound cases) (dfltFuelBound (some body)) := by
                    have hh : stmtsFuelBound body = dfltFuelBound (some body) := rfl
                    rw [hh]
                    exact Nat.le_max_right _ _
                  simp only [execIRStmt, heval, hfind]
                  rw [show Nat.max (casesFuelBound cases) (dfltFuelBound (some body)) + f =
                      stmtsFuelBound body + (Nat.max (casesFuelBound cases)
                        (dfltFuelBound (some body)) - stmtsFuelBound body + f) from by omega,
                    execIRStmts_stable body hLFb _ state,
                    show Nat.max (casesFuelBound cases) (dfltFuelBound (some body)) =
                      stmtsFuelBound body + (Nat.max (casesFuelBound cases)
                        (dfltFuelBound (some body)) - stmtsFuelBound body) from by omega,
                    execIRStmts_stable body hLFb _ state]

termination_by stmt _ _ _ => sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals try (have h1 := List.sizeOf_lt_of_mem hmem; simp at h1 ⊢; omega)
  all_goals (try simp [*, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec]) <;> omega

/-- Fuel stability for statement lists. -/
theorem execIRStmts_stable : ∀ (xs : List YulStmt), LoopFreeList xs →
    ∀ (f : Nat) (state : IRState),
      execIRStmts (stmtsFuelBound xs + f) state xs =
        execIRStmts (stmtsFuelBound xs) state xs
  | [], _, f, state => by
      simp only [stmtsFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | x :: rest, hLF, f, state => by
      simp only [stmtsFuelBound]
      rw [show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + 1 + f =
        (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f) + 1 from by omega]
      obtain ⟨hx, hrest⟩ : LoopFree x ∧ LoopFreeList rest := by
        simpa [LoopFreeList] using hLF
      have hax : stmtFuelBound x ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound rest) :=
        Nat.le_max_left _ _
      have hbx : stmtsFuelBound rest ≤ Nat.max (stmtFuelBound x) (stmtsFuelBound rest) :=
        Nat.le_max_right _ _
      show (match execIRStmt (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f)
          state x with
        | .continue s₁ => execIRStmts
            (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f) s₁ rest
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) =
      (match execIRStmt (Nat.max (stmtFuelBound x) (stmtsFuelBound rest))
          state x with
        | .continue s₁ => execIRStmts
            (Nat.max (stmtFuelBound x) (stmtsFuelBound rest)) s₁ rest
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s)
      have hhead1 : execIRStmt (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f)
          state x = execIRStmt (stmtFuelBound x) state x := by
        rw [show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f =
          stmtFuelBound x + (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) -
            stmtFuelBound x + f) from by omega]
        exact execIRStmt_stable x hx _ state
      have hhead2 : execIRStmt (Nat.max (stmtFuelBound x) (stmtsFuelBound rest))
          state x = execIRStmt (stmtFuelBound x) state x := by
        rw [show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) =
          stmtFuelBound x + (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) -
            stmtFuelBound x) from by omega]
        exact execIRStmt_stable x hx _ state
      have htail : ∀ s₁ : IRState,
          execIRStmts (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f) s₁ rest =
            execIRStmts (Nat.max (stmtFuelBound x) (stmtsFuelBound rest)) s₁ rest := by
        intro s₁
        rw [show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f =
          stmtsFuelBound rest + (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) -
            stmtsFuelBound rest + f) from by omega,
          execIRStmts_stable rest hrest _ s₁,
          show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) =
            stmtsFuelBound rest + (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) -
              stmtsFuelBound rest) from by omega,
          execIRStmts_stable rest hrest _ s₁]
      rw [hhead1, hhead2]
      cases execIRStmt (stmtFuelBound x) state x with
      | «continue» s₁ => exact htail s₁
      | «return» v s => rfl
      | stop s => rfl
      | revert s => rfl
termination_by xs _ _ _ => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals omega

end

end Compiler.Proofs.IRGeneration
