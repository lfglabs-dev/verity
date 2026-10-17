import Compiler.Proofs.IRGeneration.ImportedPrefixFrames

namespace Compiler.Proofs.IRGeneration.ImportedLocalFrames
open Compiler.CompilationModel Denote

def preserves (key : String) (before : DenoteState) : StmtOutcome → Prop
  | .continue after | .stop after | .return _ after | .exceptional after =>
      lookupValue after.bindings key = lookupValue before.bindings key
  | .revert | .revertWithData _ | .interpretationError _ => True

def primitive (key : String) : Stmt → Bool
  | .letVar name _ | .assignVar name _ => !(name == key)
  | .mstore _ _ | .panicCode _ | .revertReturndata => true
  | _ => false

theorem primitive_frame (oracle : DenoteOracle) (fields : List Field) (key : String)
    (statement : Stmt) (safe : primitive key statement = true) (state : DenoteState) :
    preserves key state (execStmt oracle fields state statement) := by
  cases statement <;> simp only [primitive, Bool.false_eq_true] at safe
  case letVar name value =>
    have fresh : name ≠ key := by simpa using safe
    cases evaluated : evalExpr oracle fields state value <;> simp only [execStmt, evaluated, preserves]
    exact SolidityImport.lookup_bind_other _ _ _ _ fresh
  case assignVar name value =>
    have fresh : name ≠ key := by simpa using safe
    cases evaluated : evalExpr oracle fields state value <;> simp only [execStmt, evaluated, preserves]
    exact SolidityImport.lookup_bind_other _ _ _ _ fresh
  case mstore offset value =>
    cases evaluatedOffset : evalExpr oracle fields state offset <;>
      cases evaluatedValue : evalExpr oracle fields state value <;>
      simp [execStmt, evaluatedOffset, evaluatedValue, preserves,
        Verity.ContractState.writePhysicalMemoryValue, Verity.ContractState.writePhysicalMemoryWord]
  case panicCode code =>
    cases evaluated : evalExpr oracle fields state code <;> simp [execStmt, evaluated, preserves]
  case revertReturndata => simp [execStmt, preserves]

theorem loop_frame (key name : String) (fresh : name ≠ key) (body : DenoteState → StmtOutcome)
    (frame : ∀ state, preserves key state (body state))
    (remaining index : Nat) (state : DenoteState) :
    preserves key state (execForEachLoop name body state index remaining) := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    let current := { state with bindings := bindValue state.bindings name (wordNormalize index) }
    have head := frame current
    have unchanged : lookupValue current.bindings key = lookupValue state.bindings key :=
      SolidityImport.lookup_bind_other _ _ _ _ fresh
    simp only [execForEachLoop]
    cases executed : body current with
    | «continue» next =>
      have same : lookupValue next.bindings key = lookupValue state.bindings key := by
        exact (show lookupValue next.bindings key = lookupValue current.bindings key from
          by simpa only [preserves, executed] using head).trans unchanged
      have tail := ih (index + 1) next
      simpa only [preserves, same] using tail
    | stop next => simpa only [preserves, executed, unchanged] using head
    | «return» value next => simpa only [preserves, executed, unchanged] using head
    | exceptional next => simpa only [preserves, executed, unchanged] using head
    | revert => trivial
    | revertWithData data => trivial
    | interpretationError message => trivial

mutual
 def safeStmt (key : String) : Stmt → Bool
  | .ite _ yes no => safeList key yes && safeList key no
  | .forEach name _ body => !(name == key) && safeList key body
  | statement => primitive key statement
 def safeList (key : String) : List Stmt → Bool
  | [] => true
  | statement :: rest => safeStmt key statement && safeList key rest
end

mutual
 theorem statement_frame (oracle : DenoteOracle) (fields : List Field) (key : String)
    (statement : Stmt) (safe : safeStmt key statement = true) (state : DenoteState) :
    preserves key state (execStmt oracle fields state statement) := by
  cases statement <;>
    try exact primitive_frame oracle fields key _ (by simpa only [safeStmt] using safe) state
  case ite condition yes no =>
    have parts : safeList key yes = true ∧ safeList key no = true := by simpa only [safeStmt, Bool.and_eq_true] using safe
    cases evaluated : evalExpr oracle fields state condition with
    | none => simp [execStmt, evaluated, preserves]
    | some value =>
      simp only [execStmt, evaluated]
      split
      · exact list_frame oracle fields key yes parts.1 state
      · exact list_frame oracle fields key no parts.2 state
  case forEach name count body =>
    have parts : name ≠ key ∧ safeList key body = true := by simpa [safeStmt] using safe
    have result := loop_frame key name parts.1 (fun s => execStmtList oracle fields s body)
      (fun s => list_frame oracle fields key body parts.2 s)
    cases evaluated : evalExpr oracle fields state count with
    | none => simp [execStmt, evaluated, preserves]
    | some bound =>
      have actual := result bound 0 { state with bindings := bindValue state.bindings name (wordNormalize 0) }
      simpa only [execStmt, evaluated, preserves, SolidityImport.lookup_bind_other _ _ _ _ parts.1] using actual
 theorem list_frame (oracle : DenoteOracle) (fields : List Field) (key : String)
    (statements : List Stmt) (safe : safeList key statements = true) (state : DenoteState) :
    preserves key state (execStmtList oracle fields state statements) := by
  cases statements with
  | nil => rfl
  | cons statement rest =>
    have parts : safeStmt key statement = true ∧ safeList key rest = true := by
      simpa only [safeList, Bool.and_eq_true] using safe
    have head := statement_frame oracle fields key statement parts.1 state
    simp only [execStmtList]
    cases executed : execStmt oracle fields state statement with
    | «continue» next =>
      have same : lookupValue next.bindings key = lookupValue state.bindings key := by
        simpa only [preserves, executed] using head
      have tail := list_frame oracle fields key rest parts.2 next
      simpa only [preserves, same] using tail
    | stop next => simpa only [preserves, executed] using head
    | «return» value next => simpa only [preserves, executed] using head
    | exceptional next => simpa only [preserves, executed] using head
    | revert => trivial
    | revertWithData data => trivial
    | interpretationError message => trivial
end

end Compiler.Proofs.IRGeneration.ImportedLocalFrames
