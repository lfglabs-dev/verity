import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.StorageFrames

namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

private theorem worldFrame_memory (before : DenoteState) (outcome : StmtOutcome)
    (frame : preservesWorld before outcome) : preservesMemory before outcome := by
  cases outcome with
  | «continue» after => exact congrArg Verity.ContractState.memory frame
  | stop after => exact congrArg Verity.ContractState.memory frame
  | «return» value after => exact congrArg Verity.ContractState.memory frame
  | revert => exact True.intro
  | revertWithData bytes => exact True.intro

private theorem scalarWrite_memory (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (value : Expr) :
    preservesMemory state (execStmt oracle fields state (.setStorage name value)) := by
  cases slots : findFieldWriteSlots fields name <;>
    cases evaluated : evalExpr oracle fields state value <;>
    simp [execStmt, slots, evaluated, preservesMemory, writeUintFieldSlots_memory_frame]

mutual
/-- Soundness of the exact recursive whitelist used by ABI-length loop lowering.
Unknown constructs cannot acquire a frame certificate through a default arm. -/
theorem abiHeaderPreservingStmt_memory (oracle : DenoteOracle) (fields : List Field)
    (statement : Stmt) (covered : abiHeaderPreservingStmt statement = true)
    (state : DenoteState) : preservesMemory state (execStmt oracle fields state statement) := by
  cases statement <;>
    simp only [abiHeaderPreservingStmt, stmtCovered, Bool.and_eq_true,
      Bool.false_eq_true] at covered
  case letVar name value =>
    exact worldFrame_memory state _ (execStmt_slice_world oracle fields state _ (by simpa [stmtCovered] using covered))
  case assignVar name value =>
    exact worldFrame_memory state _ (execStmt_slice_world oracle fields state _ (by simpa [stmtCovered] using covered))
  case setStorage name value => exact scalarWrite_memory oracle fields state name value
  case setStructMember name key member value =>
    exact execStmt_setStructMember_memory_frame oracle fields state name member key value
  case setStructMember2 name key1 key2 member value =>
    exact execStmt_setStructMember2_memory_frame oracle fields state name member key1 key2 value
  case ite condition yes no =>
    have yesFrame := abiHeaderPreservingList_memory oracle fields yes covered.1.2 state
    have noFrame := abiHeaderPreservingList_memory oracle fields no covered.2 state
    cases evaluated : evalExpr oracle fields state condition with
    | none => simp [execStmt, evaluated, preservesMemory]
    | some value =>
        by_cases nonzero : value != 0
        · simpa [execStmt, evaluated, nonzero] using yesFrame
        · simpa [execStmt, evaluated, nonzero] using noFrame
  case forEach name count body =>
    have frame : ∀ before, preservesMemory before (execStmtList oracle fields before body) :=
      fun before => abiHeaderPreservingList_memory oracle fields body covered.2 before
    cases evaluated : evalExpr oracle fields state count with
    | none => simp [execStmt, evaluated, preservesMemory]
    | some bound =>
        have result := execForEachLoop_memory_frame name
          (fun before => execStmtList oracle fields before body) frame bound 0
          { state with bindings := bindValue state.bindings name (wordNormalize 0) }
        simpa [execStmt, evaluated, preservesMemory] using result
  case emit name args => exact execStmt_emit_memory_frame oracle fields state name args
  case returnValues args => exact execStmt_returnValues_memory_frame oracle fields state args
  case stop => simp [execStmt, preservesMemory]
  case revertReturndata => simp [execStmt, preservesMemory]
  case panicCode code =>
    cases evaluated : evalExpr oracle fields state code <;> simp [execStmt, evaluated, preservesMemory]
  case panic code => simp [execStmt, preservesMemory]
  case require condition message =>
    exact worldFrame_memory state _ (execStmt_slice_world oracle fields state _ (by simpa [stmtCovered] using covered))
  case requireError condition name args =>
    exact worldFrame_memory state _ (execStmt_slice_world oracle fields state _ (by simpa [stmtCovered] using covered))

theorem abiHeaderPreservingList_memory (oracle : DenoteOracle) (fields : List Field)
    (statements : List Stmt) (covered : abiHeaderPreservingList statements = true)
    (state : DenoteState) : preservesMemory state (execStmtList oracle fields state statements) := by
  cases statements with
  | nil => simp [execStmtList, preservesMemory]
  | cons statement rest =>
      have components : abiHeaderPreservingStmt statement = true ∧ abiHeaderPreservingList rest = true := by
        simpa [abiHeaderPreservingList, Bool.and_eq_true] using covered
      have headFrame := abiHeaderPreservingStmt_memory oracle fields statement components.1 state
      simp only [execStmtList]
      cases executed : execStmt oracle fields state statement with
      | «continue» after =>
          have sameMemory : after.world.memory = state.world.memory := by
            simpa [preservesMemory, executed] using headFrame
          have tailFrame := abiHeaderPreservingList_memory oracle fields rest components.2 after
          simpa [preservesMemory, sameMemory] using tailFrame
      | stop after => simpa [preservesMemory, executed] using headFrame
      | «return» value after => simpa [preservesMemory, executed] using headFrame
      | revert => simp [preservesMemory]
      | revertWithData bytes => simp [preservesMemory]
end

end Compiler.CompilationModel.Denote
