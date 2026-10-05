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

/-- Scalar storage updates cannot alter an ABI array header in memory,
including packed and transient writes. -/
theorem writeUintFieldSlots_memory_frame (fields : List Field) (name : String)
    (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    (writeUintFieldSlots fields name world slots value).memory = world.memory := by
  unfold writeUintFieldSlots
  split
  · rename_i field resolvedSlot found
    cases packed : field.packedBits with
    | none =>
        dsimp only
        split <;> simp [writeTransientTargets, writeUintSlots,
          Verity.ContractState.writeSlots, Verity.ContractState.writeTransientSlots]
    | some bits =>
        dsimp only
        split <;> simp [Verity.ContractState.modifySlots,
          Verity.ContractState.modifyTransientSlots]
  · simp [writeUintSlots, Verity.ContractState.writeSlots]

/-- The actual scalar storage statement preserves memory on success. -/
theorem execStmt_setStorage_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (name : String) (expression : Expr)
    (slots : List Nat) (resolved : findFieldWriteSlots fields name = some slots)
    (executed : execStmt oracle fields before (.setStorage name expression) = .continue after) :
    after.world.memory = before.world.memory := by
  simp only [execStmt, resolved] at executed
  cases value : evalExpr oracle fields before expression with
  | none => simp [value] at executed
  | some word =>
      simp only [value, StmtOutcome.continue.injEq] at executed
      cases executed
      exact writeUintFieldSlots_memory_frame fields name before.world slots word

/-- A memory-only observation. Reverts have no successor state; their bytes
remain observable separately and this predicate asserts nothing about them. -/
def preservesMemory (before : DenoteState) : StmtOutcome → Prop
  | .continue after | .stop after | .return _ after => after.world.memory = before.world.memory
  | .revert | .revertWithData _ => True

/-- Emitting an event changes events, not the decoded ABI memory header. -/
theorem execStmt_emit_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (arguments : List Expr) :
    preservesMemory state (execStmt oracle fields state (.emit name arguments)) := by
  cases evaluated : evalExprList oracle fields state arguments <;>
    simp [execStmt, evaluated, preservesMemory]

/-- Multivalue returns stop execution without the memory-zero store performed
by the separate single-word `.return` constructor. -/
theorem execStmt_returnValues_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (arguments : List Expr) :
    preservesMemory state (execStmt oracle fields state (.returnValues arguments)) := by
  cases evaluated : evalExprList oracle fields state arguments <;>
    simp [execStmt, evaluated, preservesMemory]

/-- Both forms of model local bindings preserve the entire memory grid. -/
theorem execStmt_local_binding_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (value : Expr) :
    preservesMemory state (execStmt oracle fields state (.letVar name value)) ∧
    preservesMemory state (execStmt oracle fields state (.assignVar name value)) := by
  cases evaluated : evalExpr oracle fields state value <;>
    simp [execStmt, evaluated, preservesMemory]

/-- Compose actual memory frame facts without assuming successful execution.
All early outcomes, including their revert bytes, remain the original outcome. -/
theorem execStmtList_memory_frame_of_steps (oracle : DenoteOracle) (fields : List Field)
    (statements : List Stmt)
    (steps : ∀ statement ∈ statements, ∀ before,
      preservesMemory before (execStmt oracle fields before statement))
    (state : DenoteState) :
    preservesMemory state (execStmtList oracle fields state statements) := by
  induction statements generalizing state with
  | nil => simp [execStmtList, preservesMemory]
  | cons statement rest ih =>
      have headFrame := steps statement (by simp) state
      have tailSteps : ∀ statement ∈ rest, ∀ before,
          preservesMemory before (execStmt oracle fields before statement) := by
        intro statement member before
        exact steps statement (by simp [member]) before
      simp only [execStmtList]
      cases executed : execStmt oracle fields state statement with
      | «continue» next =>
          have sameMemory : next.world.memory = state.world.memory := by
            simpa [preservesMemory, executed] using headFrame
          have tailFrame := ih tailSteps next
          simpa [preservesMemory, sameMemory] using tailFrame
      | stop next => simpa [preservesMemory, executed] using headFrame
      | «return» value next => simpa [preservesMemory, executed] using headFrame
      | revert => simp [preservesMemory]
      | revertWithData bytes => simp [preservesMemory]

/-- The bounded executor composes a body memory frame at every actual index.
Updating the index binding does not modify memory. -/
theorem execForEachLoop_memory_frame (name : String) (runBody : DenoteState → StmtOutcome)
    (bodyFrame : ∀ state, preservesMemory state (runBody state))
    (remaining index : Nat) (state : DenoteState) :
    preservesMemory state (execForEachLoop name runBody state index remaining) := by
  induction remaining generalizing index state with
  | zero => simp [execForEachLoop, preservesMemory]
  | succ remaining ih =>
      have frame := bodyFrame
        { state with bindings := bindValue state.bindings name (wordNormalize index) }
      simp only [execForEachLoop]
      cases executed : runBody
          { state with bindings := bindValue state.bindings name (wordNormalize index) } with
      | «continue» next =>
          have sameMemory : next.world.memory = state.world.memory := by
            simpa [preservesMemory, executed] using frame
          have tailFrame := ih (index + 1) next
          simpa [preservesMemory, sameMemory] using tailFrame
      | stop next => simpa [preservesMemory, executed] using frame
      | «return» value next => simpa [preservesMemory, executed] using frame
      | revert => simp [preservesMemory]
      | revertWithData bytes => simp [preservesMemory]

/-- Every mapping target store preserves memory, regardless of alias slots. -/
theorem writeMappingTargets_memory_frame (fields : List Field) (name : String)
    (world : Verity.ContractState) (targets : List Nat) (value : Nat) :
    (writeMappingTargets fields name world targets value).memory = world.memory := by
  unfold writeMappingTargets
  split <;> simp [writeTransientTargets, Verity.ContractState.writeSlots,
    Verity.ContractState.writeTransientSlots]

theorem writeAddressKeyedMappingWordFieldSlots_memory_frame (oracle : DenoteOracle)
    (fields : List Field) (name : String) (world : Verity.ContractState)
    (slots : List Nat) (key offset value : Nat) :
    (writeAddressKeyedMappingWordFieldSlots oracle fields name world slots key offset value).memory =
      world.memory := by
  unfold writeAddressKeyedMappingWordFieldSlots
  exact writeMappingTargets_memory_frame fields name world _ value

theorem writeAddressKeyedMapping2WordFieldSlots_memory_frame (oracle : DenoteOracle)
    (fields : List Field) (name : String) (world : Verity.ContractState)
    (slots : List Nat) (key1 key2 offset value : Nat) :
    (writeAddressKeyedMapping2WordFieldSlots oracle fields name world slots key1 key2 offset value).memory =
      world.memory := by
  unfold writeAddressKeyedMapping2WordFieldSlots
  exact writeMappingTargets_memory_frame fields name world _ value

theorem writeAddressKeyedMappingPackedWordFieldSlots_memory_frame (oracle : DenoteOracle)
    (fields : List Field) (name : String) (world : Verity.ContractState)
    (slots : List Nat) (key offset : Nat) (packed : PackedBits) (value : Nat) :
    (writeAddressKeyedMappingPackedWordFieldSlots oracle fields name world slots key offset packed value).memory =
      world.memory := by
  unfold writeAddressKeyedMappingPackedWordFieldSlots
  split <;> simp [writeAddressKeyedMappingPackedWordSlots,
    Verity.ContractState.modifySlots, Verity.ContractState.modifyTransientSlots]

theorem writeAddressKeyedMapping2PackedWordFieldSlots_memory_frame (oracle : DenoteOracle)
    (fields : List Field) (name : String) (world : Verity.ContractState)
    (slots : List Nat) (key1 key2 offset : Nat) (packed : PackedBits) (value : Nat) :
    (writeAddressKeyedMapping2PackedWordFieldSlots oracle fields name world slots key1 key2 offset packed value).memory =
      world.memory := by
  unfold writeAddressKeyedMapping2PackedWordFieldSlots
  split <;> simp [writeAddressKeyedMapping2PackedWordSlots,
    Verity.ContractState.modifySlots, Verity.ContractState.modifyTransientSlots]

/-- Memory frame for the one-key member-write statement, including packed
writes and failure to resolve a field, member or argument. -/
theorem execStmt_setStructMember_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name member : String) (key value : Expr) :
    preservesMemory state (execStmt oracle fields state (.setStructMember name key member value)) := by
  simp only [execStmt]
  split
  all_goals try exact True.intro
  all_goals split
  all_goals simp only [preservesMemory]
  all_goals try split
  all_goals simp_all only [writeAddressKeyedMappingWordFieldSlots_memory_frame,
    writeAddressKeyedMappingPackedWordFieldSlots_memory_frame, preservesMemory]

/-- The same memory frame for the two-key member-write statement. -/
theorem execStmt_setStructMember2_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name member : String) (key1 key2 value : Expr) :
    preservesMemory state (execStmt oracle fields state (.setStructMember2 name key1 key2 member value)) := by
  simp only [execStmt]
  split
  all_goals try exact True.intro
  all_goals split
  all_goals simp only [preservesMemory]
  all_goals try split
  all_goals simp_all only [writeAddressKeyedMapping2WordFieldSlots_memory_frame,
    writeAddressKeyedMapping2PackedWordFieldSlots_memory_frame, preservesMemory]

end Compiler.CompilationModel.Denote
