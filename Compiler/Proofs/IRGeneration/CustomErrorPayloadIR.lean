import Compiler.Proofs.IRGeneration.ErrorStringPayloadIR

/-!
# Proof-side observable for revert payload blocks

Companion to `ErrorStringPayloadIR` (the `Error(string)` observable) and the
`Panic(uint256)` observable.

The generic-induction step lemmas `compiledStmtStep_requireError` and
`compiledStmtStep_revertError` are already proved, but both are stated modulo
the hypothesis

    hrevertExec : ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next

which nothing in the tree discharged, leaving those two lemmas without
consumers. This module supplies the machinery for that hypothesis: it
characterizes the statement shapes a revert payload is built from
(`NonEscaping` — statements that can only continue or revert), proves that a
list reaching a `revert` call through such statements deterministically reverts
(`RevertsAlways` / `execIRStmts_revertsAlways`), and lifts that through the
`block` wrapper the typed-error payload uses.

Fuel exhaustion is itself modelled as `.revert` by `execIRStmts`, so these
statements hold at every fuel value, including `0`.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.ECM

/-! ## Execution-unfolding helpers -/

theorem execIRStmts_cons_continue'
    (fuel : Nat) (state next : IRState) (stmt : YulStmt) (tail : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .continue next) :
    execIRStmts (fuel + 1) state (stmt :: tail) = execIRStmts fuel next tail := by
  simp [execIRStmts, hstmt]

theorem execIRStmts_cons_revert
    (fuel : Nat) (state next : IRState) (stmt : YulStmt) (tail : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .revert next) :
    execIRStmts (fuel + 1) state (stmt :: tail) = .revert next := by
  simp [execIRStmts, hstmt]

theorem execIRStmts_zero_cons (state : IRState) (stmt : YulStmt)
    (tail : List YulStmt) :
    execIRStmts 0 state (stmt :: tail) = .revert state := by
  simp [execIRStmts]

/-- A `revert` expression statement reverts at every fuel value, including the
out-of-fuel case. -/
theorem execIRStmt_revertCall (fuel : Nat) (state : IRState)
    (offset size : YulExpr) :
    execIRStmt fuel state (.exprStmt (.call "revert" [offset, size])) =
      .revert state := by
  cases fuel <;> simp [execIRStmt]

/-! ## Non-escaping statements -/

/-- A statement whose execution can only `continue` or `revert`: it never
produces a `return`/`stop` observable. Every statement a revert payload is
built from (free-pointer load, `mstore`s, `let`/`assign` temporaries) has this
shape, which is what makes a trailing `revert` unavoidable. -/
def NonEscaping (stmt : YulStmt) : Prop :=
  ∀ (fuel : Nat) (state : IRState),
    (∃ next, execIRStmt fuel state stmt = .continue next) ∨
    (∃ next, execIRStmt fuel state stmt = .revert next)

theorem NonEscaping.let_ (name : String) (value : YulExpr) :
    NonEscaping (.let_ name value) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hval : evalIRExpr state value with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hval]⟩
      | some v => exact Or.inl ⟨state.setVar name v, by simp [execIRStmt, hval]⟩

theorem NonEscaping.assign (name : String) (value : YulExpr) :
    NonEscaping (.assign name value) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hval : evalIRExpr state value with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hval]⟩
      | some v => exact Or.inl ⟨state.setVar name v, by simp [execIRStmt, hval]⟩

theorem NonEscaping.mstore (offset value : YulExpr) :
    NonEscaping (.exprStmt (.call "mstore" [offset, value])) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hoff : evalIRExpr state offset with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hoff]⟩
      | some o =>
          cases hval : evalIRExpr state value with
          | none => exact Or.inr ⟨state, by simp [execIRStmt, hoff, hval]⟩
          | some v =>
              exact Or.inl ⟨{ state with
                memory := fun x => if x = o then v else state.memory x },
                by simp [execIRStmt, hoff, hval]⟩

/-! ## Statement lists that deterministically revert -/

/-- Statement lists that revert from any state at any fuel: a `revert` call
reached through a prefix of statements that can only continue or revert. -/
inductive RevertsAlways : List YulStmt → Prop
  | revertCall {rest : List YulStmt} (offset size : YulExpr) :
      RevertsAlways (.exprStmt (.call "revert" [offset, size]) :: rest)
  | cons {stmt : YulStmt} {rest : List YulStmt} :
      NonEscaping stmt → RevertsAlways rest → RevertsAlways (stmt :: rest)

/-- The core observable: a `RevertsAlways` list reverts from any state at any
fuel. -/
theorem execIRStmts_revertsAlways {stmts : List YulStmt}
    (h : RevertsAlways stmts) :
    ∀ (fuel : Nat) (state : IRState),
      ∃ next, execIRStmts fuel state stmts = .revert next := by
  induction h with
  | revertCall offset size =>
      intro fuel state
      cases fuel with
      | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
      | succ f =>
          exact ⟨state, execIRStmts_cons_revert f state state _ _
            (execIRStmt_revertCall f state offset size)⟩
  | cons hstmt _ ih =>
      intro fuel state
      cases fuel with
      | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
      | succ f =>
          rcases hstmt f state with ⟨next, hcont⟩ | ⟨next, hrev⟩
          · rcases ih f next with ⟨final, hfinal⟩
            exact ⟨final, by
              rw [execIRStmts_cons_continue' f state next _ _ hcont]; exact hfinal⟩
          · exact ⟨next, execIRStmts_cons_revert f state next _ _ hrev⟩

/-- A non-escaping prefix in front of a reverting list still reverts. -/
theorem RevertsAlways.append_left :
    ∀ (pre : List YulStmt) {post : List YulStmt},
      (∀ stmt ∈ pre, NonEscaping stmt) → RevertsAlways post →
      RevertsAlways (pre ++ post)
  | [], _, _, hpost => by simpa using hpost
  | stmt :: rest, _, hpre, hpost =>
      .cons (hpre stmt (by simp))
        (RevertsAlways.append_left rest
          (fun s hs => hpre s (by simp [hs])) hpost)

/-- A block wrapping a reverting list reverts. -/
theorem execIRStmts_block_revertsAlways {body : List YulStmt}
    (h : RevertsAlways body) :
    ∀ (fuel : Nat) (state : IRState),
      ∃ next, execIRStmts fuel state [YulStmt.block body] = .revert next := by
  intro fuel state
  cases fuel with
  | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
  | succ f =>
      cases f with
      | zero =>
          exact ⟨state, execIRStmts_cons_revert 0 state state _ _
            (by simp [execIRStmt])⟩
      | succ g =>
          rcases execIRStmts_revertsAlways h g state with ⟨next, hnext⟩
          refine ⟨next, execIRStmts_cons_revert (g + 1) state next _ _ ?_⟩
          rw [show execIRStmt (g + 1) state (YulStmt.block body) =
            execIRStmts g state body from by simp [execIRStmt]]
          exact hnext

/-! ## Application: the `Error(string)` payload always reverts

`revertWithMessage` already has a proved shape lemma, so it is the cheapest
witness that the machinery above discharges a real `hrevertExec` obligation. -/

theorem revertWithMessage_revertsAlways (message : String) :
    RevertsAlways (revertWithMessage message) := by
  rw [revertWithMessage_shape]
  refine RevertsAlways.append_left (errorStringStmts message) ?_ (.revertCall _ _)
  intro stmt hstmt
  have hmstore : ∀ (o v : YulExpr),
      stmt = .exprStmt (.call "mstore" [o, v]) → NonEscaping stmt := by
    rintro o v rfl
    exact NonEscaping.mstore o v
  simp only [errorStringStmts, List.mem_cons, List.mem_map] at hstmt
  rcases hstmt with rfl | rfl | rfl | ⟨ci, _, rfl⟩
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl

theorem execIRStmts_revertWithMessage_revert (message : String) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next, execIRStmts fuel state (revertWithMessage message) = .revert next :=
  fun state fuel =>
    execIRStmts_revertsAlways (revertWithMessage_revertsAlways message) fuel state

end Compiler.Proofs.IRGeneration
