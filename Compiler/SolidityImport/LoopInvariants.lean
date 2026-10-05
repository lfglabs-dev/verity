import Verity.Core.Model.Denote

namespace Compiler.CompilationModel.Denote

/-- A loop's normal continuation and early exits have separate obligations.
In particular, a revert is not silently accepted by an invariant on states. -/
def LoopOutcomePost (normal : DenoteState → Prop) (exit : StmtOutcome → Prop) :
    StmtOutcome → Prop
  | .continue state => normal state
  | outcome => exit outcome

/-- Indexed invariants for the actual bounded-loop executor. The step premise
includes its binding of the normalized index. Early exits retain their complete
outcome, including revert bytes; the caller chooses their postcondition. -/
theorem execForEachLoop_invariant
    (varName : String) (runBody : DenoteState → StmtOutcome)
    (invariant : Nat → DenoteState → Prop) (exit : StmtOutcome → Prop)
    (step : ∀ index state, invariant index state →
      LoopOutcomePost (invariant (index + 1)) exit
        (runBody { state with bindings := bindValue state.bindings varName (wordNormalize index) }))
    (remaining index : Nat) (state : DenoteState)
    (initial : invariant index state) :
    LoopOutcomePost (invariant (index + remaining)) exit
      (execForEachLoop varName runBody state index remaining) := by
  induction remaining generalizing index state with
  | zero => simpa [execForEachLoop, LoopOutcomePost] using initial
  | succ remaining ih =>
      have next := step index state initial
      simp only [execForEachLoop]
      cases result : runBody { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
      | «continue» after =>
          rw [result] at next
          have preserved := ih (index + 1) after next
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using preserved
      | stop after => simpa [result, LoopOutcomePost] using next
      | «return» value after => simpa [result, LoopOutcomePost] using next
      | revert => simpa [result, LoopOutcomePost] using next
      | revertWithData bytes => simpa [result, LoopOutcomePost] using next

/-- Lift the indexed rule through count evaluation and the actual `.forEach`
statement, including the executor's initial binding even for an empty loop. -/
theorem forEach_invariant (oracle : DenoteOracle) (fields : List Field)
    (varName : String) (count : Expr) (body : List Stmt)
    (invariant : Nat → DenoteState → Prop) (exit : StmtOutcome → Prop)
    (state : DenoteState) (bound : Nat)
    (evaluated : evalExpr oracle fields state count = some bound)
    (initial : invariant 0
      { state with bindings := bindValue state.bindings varName (wordNormalize 0) })
    (step : ∀ index before, invariant index before →
      LoopOutcomePost (invariant (index + 1)) exit
        (execStmtList oracle fields
          { before with bindings := bindValue before.bindings varName (wordNormalize index) } body)) :
    LoopOutcomePost (invariant bound) exit
      (execStmt oracle fields state (.forEach varName count body)) := by
  have result := execForEachLoop_invariant varName
    (fun loopState => execStmtList oracle fields loopState body)
    invariant exit step bound 0 _ initial
  simpa only [execStmt, evaluated, Nat.zero_add] using result

/-- Bounded indexed induction only requires a body proof for iterations that
can execute. Exit outcomes retain the same explicit postcondition as above. -/
theorem execForEachLoop_bounded_invariant
    (varName : String) (runBody : DenoteState → StmtOutcome)
    (limit : Nat) (invariant : Nat → DenoteState → Prop) (exit : StmtOutcome → Prop)
    (step : ∀ index state, index < limit → invariant index state →
      LoopOutcomePost (invariant (index + 1)) exit
        (runBody { state with bindings := bindValue state.bindings varName (wordNormalize index) }))
    (remaining index : Nat) (state : DenoteState)
    (bounded : index + remaining ≤ limit) (initial : invariant index state) :
    LoopOutcomePost (invariant (index + remaining)) exit
      (execForEachLoop varName runBody state index remaining) := by
  induction remaining generalizing index state with
  | zero => simpa [execForEachLoop, LoopOutcomePost] using initial
  | succ remaining ih =>
      have next := step index state (by omega) initial
      simp only [execForEachLoop]
      cases result : runBody { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
      | «continue» after =>
          rw [result] at next
          have preserved := ih (index + 1) after (by omega) next
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using preserved
      | stop after => simpa [result, LoopOutcomePost] using next
      | «return» value after => simpa [result, LoopOutcomePost] using next
      | revert => simpa [result, LoopOutcomePost] using next
      | revertWithData bytes => simpa [result, LoopOutcomePost] using next

/-- The strict loop condition makes the checked uint256 unit increment safe,
even when the bound is the largest representable word. -/
theorem solidityFor_increment_fits (index bound modulus : Nat)
    (condition : index < bound) (boundFits : bound < modulus) :
    index + 1 < modulus := by
  omega

/-- The implicit forEach index is the same mathematical induction variable:
a live iteration stays below the invariant bound. -/
theorem solidityFor_live_index (index remaining bound : Nat)
    (remainingPositive : 0 < remaining) (bounded : index + remaining ≤ bound) :
    index < bound := by
  omega

/-- A zero remainder reaches the false strict Solidity condition exactly at
its fixed bound. This excludes an extra body execution at the boundary. -/
theorem solidityFor_terminal_index (index bound : Nat)
    (atBound : index = bound) : ¬ index < bound := by
  omega

end Compiler.CompilationModel.Denote
