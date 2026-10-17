import Compiler.Proofs.IRGeneration.CreationMemoryFrames
import Verity.Core.Model.Denote
import Compiler.SolidityImport.Proofs

namespace Compiler.Proofs.IRGeneration.ImportedPrefixFrames
open Compiler.CompilationModel Compiler.CompilationModel.Denote CreationMemoryFrames

/-- All fields except caller memory, including complete storage/account functions. -/
def preserves (origin : DenoteState) : StmtOutcome → Prop
  | .continue next | .stop next | .return _ next | .exceptional next =>
      eraseMemory next.world = eraseMemory origin.world
  | .revert | .revertWithData _ | .interpretationError _ => True

/-- Exact primitive whitelist; unknown instructions cannot receive a certificate. -/
def primitive : Stmt → Bool
  | .letVar _ _ | .assignVar _ _ | .mstore _ _ | .panicCode _ | .revertReturndata => true
  | _ => false

theorem primitive_frame (oracle : DenoteOracle) (fields : List Field)
    (statement : Stmt) (safe : primitive statement = true) (state : DenoteState) :
    preserves state (execStmt oracle fields state statement) := by
  cases statement <;> simp only [primitive, Bool.false_eq_true] at safe
  case letVar name value =>
    cases evaluated : evalExpr oracle fields state value <;> simp [execStmt, evaluated, preserves]
  case assignVar name value =>
    cases evaluated : evalExpr oracle fields state value <;> simp [execStmt, evaluated, preserves]
  case mstore offset value =>
    cases evaluatedOffset : evalExpr oracle fields state offset <;>
      cases evaluatedValue : evalExpr oracle fields state value <;>
      simp [execStmt, evaluatedOffset, evaluatedValue, preserves,
        Verity.ContractState.writePhysicalMemoryValue, Verity.ContractState.writePhysicalMemoryWord, install_frame]
  case panicCode code =>
    cases evaluated : evalExpr oracle fields state code <;> simp [execStmt, evaluated, preserves]
  case revertReturndata => simp [execStmt, preserves]

/-- Compose actual loop frames without assuming that any iteration succeeds. -/
theorem loop_frame (name : String) (body : DenoteState → StmtOutcome)
    (frame : ∀ state, preserves state (body state))
    (remaining index : Nat) (state : DenoteState) :
    preserves state (execForEachLoop name body state index remaining) := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    let current := { state with bindings := bindValue state.bindings name (wordNormalize index) }
    have head := frame current
    simp only [execForEachLoop]
    cases executed : body current with
    | «continue» next =>
      have same : eraseMemory next.world = eraseMemory state.world := by
        simpa only [preserves, executed] using head
      have tail := ih (index + 1) next
      simpa only [preserves, same] using tail
    | stop next => simpa only [preserves, executed] using head
    | «return» value next => simpa only [preserves, executed] using head
    | exceptional next => simpa only [preserves, executed] using head
    | revert => trivial
    | revertWithData data => trivial
    | interpretationError message => trivial

mutual
/-- Recursively certify only the memory/local/control constructs actually used. -/
def safeStmt : Stmt → Bool
  | .ite _ yes no => safeList yes && safeList no
  | .forEach _ _ body => safeList body
  | statement => primitive statement

def safeList : List Stmt → Bool
  | [] => true
  | statement :: rest => safeStmt statement && safeList rest
end

mutual
theorem statement_frame (oracle : DenoteOracle) (fields : List Field)
    (statement : Stmt) (safe : safeStmt statement = true) (state : DenoteState) :
    preserves state (execStmt oracle fields state statement) := by
  cases statement <;>
    try exact primitive_frame oracle fields _ (by simpa only [safeStmt] using safe) state
  case ite condition yes no =>
    have parts : safeList yes = true ∧ safeList no = true := by
      simpa only [safeStmt, Bool.and_eq_true] using safe
    cases evaluated : evalExpr oracle fields state condition with
    | none => simp [execStmt, evaluated, preserves]
    | some value =>
      by_cases nonzero : value != 0
      · simpa only [execStmt, evaluated, nonzero, if_true] using list_frame oracle fields yes parts.1 state
      · simpa only [execStmt, evaluated, nonzero, Bool.false_eq_true, if_false] using list_frame oracle fields no parts.2 state
  case forEach name count body =>
    have frame : ∀ before, preserves before (execStmtList oracle fields before body) :=
      fun before => list_frame oracle fields body safe before
    cases evaluated : evalExpr oracle fields state count with
    | none => simp [execStmt, evaluated, preserves]
    | some bound =>
      have result := loop_frame name (fun before => execStmtList oracle fields before body) frame bound 0
        { state with bindings := bindValue state.bindings name (wordNormalize 0) }
      simpa only [execStmt, evaluated, preserves] using result

theorem list_frame (oracle : DenoteOracle) (fields : List Field)
    (statements : List Stmt) (safe : safeList statements = true) (state : DenoteState) :
    preserves state (execStmtList oracle fields state statements) := by
  cases statements with
  | nil => rfl
  | cons statement rest =>
    have parts : safeStmt statement = true ∧ safeList rest = true := by
      simpa only [safeList, Bool.and_eq_true] using safe
    have head := statement_frame oracle fields statement parts.1 state
    simp only [execStmtList]
    cases executed : execStmt oracle fields state statement with
    | «continue» next =>
      have same : eraseMemory next.world = eraseMemory state.world := by
        simpa only [preserves, executed] using head
      have tail := list_frame oracle fields rest parts.2 next
      simpa only [preserves, same] using tail
    | stop next => simpa only [preserves, executed] using head
    | «return» value next => simpa only [preserves, executed] using head
    | exceptional next => simpa only [preserves, executed] using head
    | revert => trivial
    | revertWithData data => trivial
    | interpretationError message => trivial
end

/-- Extract the actual unique effect, with complete nonmemory frames on both
sides. No successful write or postworld is supplied independently. -/
theorem isolate_effect (oracle : DenoteOracle) (fields : List Field)
    (before after : List Stmt) (effect : Stmt) (initial final : DenoteState)
    (beforeSafe : safeList before = true) (afterSafe : safeList after = true)
    (executed : execStmtList oracle fields initial (before ++ effect :: after) = .continue final) :
    ∃ pre post, execStmtList oracle fields initial before = .continue pre ∧
      execStmt oracle fields pre effect = .continue post ∧
      eraseMemory pre.world = eraseMemory initial.world ∧
      eraseMemory final.world = eraseMemory post.world := by
  obtain ⟨pre, ranBefore, ranTail⟩ := SolidityImport.split_prefix_continue
    oracle fields initial final before (effect :: after) executed
  have beforeFrame := list_frame oracle fields before beforeSafe initial
  have beforeSame : eraseMemory pre.world = eraseMemory initial.world := by
    simpa only [preserves, ranBefore] using beforeFrame
  simp only [execStmtList] at ranTail
  cases step : execStmt oracle fields pre effect with
  | «continue» post =>
    rw [step] at ranTail
    have afterFrame := list_frame oracle fields after afterSafe post
    have afterSame : eraseMemory final.world = eraseMemory post.world := by
      simpa only [preserves, ranTail] using afterFrame
    exact ⟨pre, post, ranBefore, step, beforeSame, afterSame⟩
  | stop state => rw [step] at ranTail; cases ranTail
  | «return» value state => rw [step] at ranTail; cases ranTail
  | exceptional state => rw [step] at ranTail; cases ranTail
  | revert => rw [step] at ranTail; cases ranTail
  | revertWithData data => rw [step] at ranTail; cases ranTail
  | interpretationError message => rw [step] at ranTail; cases ranTail

/-- Indexed form used by certificates over actual imported function bodies. -/
theorem isolate_index (oracle : DenoteOracle) (fields : List Field)
    (body : List Stmt) (index : Nat) (bound : index < body.length)
    (initial final : DenoteState)
    (beforeSafe : safeList (body.take index) = true)
    (afterSafe : safeList (body.drop (index + 1)) = true)
    (executed : execStmtList oracle fields initial body = .continue final) :
    ∃ pre post, execStmtList oracle fields initial (body.take index) = .continue pre ∧
      execStmt oracle fields pre body[index] = .continue post ∧
      eraseMemory pre.world = eraseMemory initial.world ∧
      eraseMemory final.world = eraseMemory post.world := by
  have split : body.take index ++ body[index] :: body.drop (index + 1) = body := by
    rw [← List.drop_eq_getElem_cons bound]
    exact List.take_append_drop index body
  apply isolate_effect oracle fields (body.take index) (body.drop (index + 1)) body[index]
    initial final beforeSafe afterSafe
  rw [split]
  exact executed

end Compiler.Proofs.IRGeneration.ImportedPrefixFrames
