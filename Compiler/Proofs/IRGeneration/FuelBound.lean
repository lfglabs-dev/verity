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

/-- A loop-free statement certified to execute within `fuel`. -/
def ExecutesWithinStmt (fuel : Nat) (stmt : YulStmt) : Prop :=
  LoopFree stmt ∧ stmtFuelBound stmt ≤ fuel

/-- A loop-free statement list certified to execute within `fuel`. -/
def ExecutesWithinStmts (fuel : Nat) (stmts : List YulStmt) : Prop :=
  LoopFreeList stmts ∧ stmtsFuelBound stmts ≤ fuel

namespace ExecutesWithinStmt

/-- A statement certificate remains valid when the available fuel increases. -/
theorem mono {fuel fuel' : Nat} {stmt : YulStmt}
    (h : ExecutesWithinStmt fuel stmt) (hle : fuel ≤ fuel') :
    ExecutesWithinStmt fuel' stmt :=
  ⟨h.1, h.2.trans hle⟩

end ExecutesWithinStmt

namespace ExecutesWithinStmts

/-- A statement-list certificate remains valid when the available fuel increases. -/
theorem mono {fuel fuel' : Nat} {stmts : List YulStmt}
    (h : ExecutesWithinStmts fuel stmts) (hle : fuel ≤ fuel') :
    ExecutesWithinStmts fuel' stmts :=
  ⟨h.1, h.2.trans hle⟩

end ExecutesWithinStmts

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

/-- Stability at a bound transfers to every larger fuel. -/
private theorem execIRStmt_stable_mono {stmt : YulStmt} {b m : Nat}
    (ih : ∀ (f : Nat) (state : IRState),
      execIRStmt (b + f) state stmt = execIRStmt b state stmt)
    (hle : b ≤ m) (f : Nat) (state : IRState) :
    execIRStmt (m + f) state stmt = execIRStmt m state stmt := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_assoc, ih, ih]

/-- Stability at a bound transfers to every larger fuel (statement lists). -/
private theorem execIRStmts_stable_mono {xs : List YulStmt} {b m : Nat}
    (ih : ∀ (f : Nat) (state : IRState),
      execIRStmts (b + f) state xs = execIRStmts b state xs)
    (hle : b ≤ m) (f : Nat) (state : IRState) :
    execIRStmts (m + f) state xs = execIRStmts m state xs := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_assoc, ih, ih]

/-- One unfolding of `execIRStmts` on a cons at successor fuel. -/
private theorem execIRStmts_succ_cons_eq (n : Nat) (state : IRState) (x : YulStmt)
    (rest : List YulStmt) :
    execIRStmts (n + 1) state (x :: rest) =
      match execIRStmt n state x with
      | .continue s₁ => execIRStmts n s₁ rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := rfl

/-- `if` step of fuel stability, given stability of the body. -/
private theorem execIRStmt_if_stable (cond : YulExpr) (body : List YulStmt)
    (ih : ∀ (f : Nat) (state : IRState),
      execIRStmts (stmtsFuelBound body + f) state body =
        execIRStmts (stmtsFuelBound body) state body)
    (f : Nat) (state : IRState) :
    execIRStmt (stmtFuelBound (.if_ cond body) + f) state (.if_ cond body) =
      execIRStmt (stmtFuelBound (.if_ cond body)) state (.if_ cond body) := by
  simp only [stmtFuelBound]
  rw [show stmtsFuelBound body + 1 + f = (stmtsFuelBound body + f) + 1 from by omega]
  show (match evalIRExpr state cond with
    | some c => if c ≠ 0 then execIRStmts (stmtsFuelBound body + f) state body
      else .continue state
    | none => .revert state) =
    (match evalIRExpr state cond with
    | some c => if c ≠ 0 then execIRStmts (stmtsFuelBound body) state body
      else .continue state
    | none => .revert state)
  cases evalIRExpr state cond with
  | none => rfl
  | some c => by_cases hc : c ≠ 0 <;> simp [hc, ih f state]

/-- `block` step of fuel stability, given stability of the body. -/
private theorem execIRStmt_block_stable (stmts : List YulStmt)
    (ih : ∀ (f : Nat) (state : IRState),
      execIRStmts (stmtsFuelBound stmts + f) state stmts =
        execIRStmts (stmtsFuelBound stmts) state stmts)
    (f : Nat) (state : IRState) :
    execIRStmt (stmtFuelBound (.block stmts) + f) state (.block stmts) =
      execIRStmt (stmtFuelBound (.block stmts)) state (.block stmts) := by
  simp only [stmtFuelBound]
  rw [show stmtsFuelBound stmts + 1 + f = (stmtsFuelBound stmts + f) + 1 from by omega]
  exact ih f state

/-- Fuel stability of a statement list at its structural bound. -/
private abbrev StmtsFuelStable (body : List YulStmt) : Prop :=
  ∀ (f : Nat) (state : IRState),
    execIRStmts (stmtsFuelBound body + f) state body = execIRStmts (stmtsFuelBound body) state body

/-- `switch` step of fuel stability, given stability of every case body and of
the default body. -/
private theorem execIRStmt_switch_stable (e : YulExpr) (cases : List (Nat × List YulStmt))
    (dflt : Option (List YulStmt))
    (ihCase : ∀ k body, (k, body) ∈ cases → StmtsFuelStable body)
    (ihDflt : ∀ body, dflt = some body → StmtsFuelStable body)
    (f : Nat) (state : IRState) :
    execIRStmt (stmtFuelBound (.switch e cases dflt) + f) state (.switch e cases dflt) =
      execIRStmt (stmtFuelBound (.switch e cases dflt)) state (.switch e cases dflt) := by
  simp only [stmtFuelBound]
  rw [show Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + 1 + f =
    (Nat.max (casesFuelBound cases) (dfltFuelBound dflt) + f) + 1 from by omega]
  cases heval : evalIRExpr state e with
  | none => simp [execIRStmt, heval]
  | some v =>
      cases hfind : List.find? (fun (c : Nat × List YulStmt) => c.1 == v) cases with
      | some c =>
          obtain ⟨k, body⟩ := c
          have hmem := List.mem_of_find?_eq_some hfind
          simp only [execIRStmt, heval, hfind]
          exact execIRStmts_stable_mono (ihCase k body hmem) (Nat.le_trans
            (stmtsFuelBound_le_casesFuelBound cases (k, body) hmem) (Nat.le_max_left _ _)) f state
      | none =>
          cases hdd : dflt with
          | none => simp [execIRStmt, heval, hfind]
          | some body =>
              simp only [execIRStmt, heval, hfind]
              exact execIRStmts_stable_mono (ihDflt body hdd)
                (Nat.le_max_right _ (dfltFuelBound (some body))) f state

/-- Cons step of list fuel stability, given stability of the head and the tail. -/
private theorem execIRStmts_cons_stable (x : YulStmt) (rest : List YulStmt)
    (ihHead : ∀ (f : Nat) (state : IRState),
      execIRStmt (stmtFuelBound x + f) state x = execIRStmt (stmtFuelBound x) state x)
    (ihRest : ∀ (f : Nat) (state : IRState),
      execIRStmts (stmtsFuelBound rest + f) state rest =
        execIRStmts (stmtsFuelBound rest) state rest)
    (f : Nat) (state : IRState) :
    execIRStmts (stmtsFuelBound (x :: rest) + f) state (x :: rest) =
      execIRStmts (stmtsFuelBound (x :: rest)) state (x :: rest) := by
  simp only [stmtsFuelBound]
  rw [show Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + 1 + f =
    (Nat.max (stmtFuelBound x) (stmtsFuelBound rest) + f) + 1 from by omega,
    execIRStmts_succ_cons_eq, execIRStmts_succ_cons_eq,
    execIRStmt_stable_mono ihHead (Nat.le_max_left _ _) f state]
  cases execIRStmt (Nat.max (stmtFuelBound x) (stmtsFuelBound rest)) state x with
  | «continue» s₁ => exact execIRStmts_stable_mono ihRest (Nat.le_max_right _ _) f s₁
  | «return» v s => rfl
  | stop s => rfl
  | revert s => rfl

mutual

/-- Fuel stability: a loop-free statement executes identically at its bound
and at any additional fuel. -/
theorem execIRStmt_stable : ∀ (stmt : YulStmt), LoopFree stmt →
    ∀ (f : Nat) (state : IRState),
      execIRStmt (stmtFuelBound stmt + f) state stmt =
        execIRStmt (stmtFuelBound stmt) state stmt
  | .comment _, _, f, state | .let_ _ _, _, f, state | .letMany _ _, _, f, state
  | .assign _ _, _, f, state | .leave, _, f, state | .exprStmt _, _, f, state
  | .funcDef _ _ _ _, _, f, state => by
      simp only [stmtFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | .for_ _ _ _ _, hLF, _, _ => absurd hLF (by simp [LoopFree])
  | .if_ cond body, hLF, f, state =>
      execIRStmt_if_stable cond body
        (execIRStmts_stable body (by simpa [LoopFree] using hLF)) f state
  | .block stmts, hLF, f, state =>
      execIRStmt_block_stable stmts
        (execIRStmts_stable stmts (by simpa [LoopFree] using hLF)) f state
  | .switch e cases dflt, hLF, f, state =>
      have hLF' : LoopFreeCases cases ∧ LoopFreeDflt dflt := by simpa [LoopFree] using hLF
      execIRStmt_switch_stable e cases dflt
        (fun _ body hmem => execIRStmts_stable body (LoopFreeCases.mem hLF'.1 hmem))
        (fun body hdd => execIRStmts_stable body (by subst hdd; simpa [LoopFreeDflt] using hLF'.2))
        f state
termination_by stmt _ _ _ => sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals try (have h1 := List.sizeOf_lt_of_mem hmem; simp at h1 ⊢; omega)
  all_goals (try simp [*, Option.some.sizeOf_spec]); omega

/-- Fuel stability for statement lists. -/
theorem execIRStmts_stable : ∀ (xs : List YulStmt), LoopFreeList xs →
    ∀ (f : Nat) (state : IRState),
      execIRStmts (stmtsFuelBound xs + f) state xs =
        execIRStmts (stmtsFuelBound xs) state xs
  | [], _, f, state => by
      simp only [stmtsFuelBound]
      rw [Nat.add_comm 1 f]
      rfl
  | x :: rest, hLF, f, state =>
      have hLF' : LoopFree x ∧ LoopFreeList rest := by simpa [LoopFreeList] using hLF
      execIRStmts_cons_stable x rest (execIRStmt_stable x hLF'.1)
        (execIRStmts_stable rest hLF'.2) f state
termination_by xs _ _ _ => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Consumer API: any two fuels at or above the bound execute identically. -/
theorem execIRStmts_stable_of_le (xs : List YulStmt) (hLF : LoopFreeList xs)
    (F G : Nat) (state : IRState)
    (hF : stmtsFuelBound xs ≤ F) (hG : stmtsFuelBound xs ≤ G) :
    execIRStmts F state xs = execIRStmts G state xs := by
  rw [show F = stmtsFuelBound xs + (F - stmtsFuelBound xs) from by omega,
    execIRStmts_stable xs hLF _ state,
    show G = stmtsFuelBound xs + (G - stmtsFuelBound xs) from by omega,
    execIRStmts_stable xs hLF _ state]

/-- Statement-level consumer API. -/
theorem execIRStmt_stable_of_le (stmt : YulStmt) (hLF : LoopFree stmt)
    (F G : Nat) (state : IRState)
    (hF : stmtFuelBound stmt ≤ F) (hG : stmtFuelBound stmt ≤ G) :
    execIRStmt F state stmt = execIRStmt G state stmt := by
  rw [show F = stmtFuelBound stmt + (F - stmtFuelBound stmt) from by omega,
    execIRStmt_stable stmt hLF _ state,
    show G = stmtFuelBound stmt + (G - stmtFuelBound stmt) from by omega,
    execIRStmt_stable stmt hLF _ state]

/-- Executions at any two certified fuels for a statement are equal. -/
theorem execIRStmt_eq_of_executesWithin (stmt : YulStmt) (F G : Nat) (state : IRState)
    (hF : ExecutesWithinStmt F stmt) (hG : ExecutesWithinStmt G stmt) :
    execIRStmt F state stmt = execIRStmt G state stmt :=
  execIRStmt_stable_of_le stmt hF.1 F G state hF.2 hG.2

/-- Executions at any two certified fuels for a statement list are equal. -/
theorem execIRStmts_eq_of_executesWithin (stmts : List YulStmt) (F G : Nat)
    (state : IRState) (hF : ExecutesWithinStmts F stmts)
    (hG : ExecutesWithinStmts G stmts) :
    execIRStmts F state stmts = execIRStmts G state stmts :=
  execIRStmts_stable_of_le stmts hF.1 F G state hF.2 hG.2

end Compiler.Proofs.IRGeneration
