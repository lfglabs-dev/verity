import Verity.Core.Model.Denote

namespace Compiler.CompilationModel.Denote

/-- A scalar write, packed or unpacked, preserves every other persistent slot.
The condition includes all normalized alias destinations. -/
theorem writeUintFieldSlots_storage_frame (fields : List Field) (name : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (outside : (slots.map wordNormalize).contains slot = false) :
    (writeUintFieldSlots fields name world slots value).storage slot = world.storage slot := by
  unfold writeUintFieldSlots
  split
  · rename_i field resolvedSlot found
    cases packed : field.packedBits with
    | none =>
      dsimp only
      split
      · exact congrFun (Verity.ContractState.storage_writeTransientSlots world _ _) slot
      · exact Verity.ContractState.storage_writeSlots_not_mem world _ _ outside
    | some bits =>
      dsimp only
      split
      · exact congrFun (Verity.ContractState.storage_modifyTransientSlots world _ _) slot
      · exact Verity.ContractState.storage_modifySlots_not_mem world _ _ outside
  · exact Verity.ContractState.storage_writeSlots_not_mem world _ _ outside

/-- Lift the physical slot frame rule to a successful actual statement step. -/
theorem execStmt_setStorage_storage_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (name : String) (expression : Expr)
    (slots : List Nat) (slot : Nat)
    (resolved : findFieldWriteSlots fields name = some slots)
    (outside : (slots.map wordNormalize).contains slot = false)
    (executed : execStmt oracle fields before (.setStorage name expression) = .continue after) :
    after.world.storage slot = before.world.storage slot := by
  simp only [execStmt, resolved] at executed
  cases value : evalExpr oracle fields before expression with
  | none => simp [value] at executed
  | some word =>
      simp only [value, StmtOutcome.continue.injEq] at executed
      cases executed
      exact writeUintFieldSlots_storage_frame fields name before.world slots word slot outside

end Compiler.CompilationModel.Denote
