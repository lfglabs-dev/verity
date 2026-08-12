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

end Compiler.Proofs.IRGeneration
