import Compiler.Proofs.IRGeneration.NativeSourceMappingStatements

namespace Compiler.Proofs.IRGeneration.NativeSourceMappingExecution
open EvmYul Compiler.CompilationModel SourceSemantics
open NativeCreationWorld NativeSourceMappingWrites NativeSourceMappingStatements
open Compiler.Proofs.Storage.HashedMappingLayout

/-- The source and native words use the same modulo, without changing the value. -/
theorem native_word_normalize (value : Nat) :
    (UInt256.ofNat value).toNat = wordNormalize value := by rfl

/-- The source field's actual transient flag selects the corresponding native write. -/
theorem source_chain_native_dispatch (fields : List Field) (name : String)
    (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement world machine warm) (base : Nat) (keys : List Nat) (value : Nat)
    (tail : Stack UInt256)
    (success : CreationCaller.checkedStep
      { machine with stack := UInt256.ofNat (Entry.location (base, keys, 0)) :: UInt256.ofNat value :: tail }
      (if fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok after) :
    Agreement (writeAddressKeyedMappingChainFieldSlots fields name world [base] keys (wordNormalize value)) after warm := by
  cases transient : fieldIsTransient fields name with
  | false =>
    simp only [transient, Bool.false_eq_true, ite_false] at success
    rw [← native_word_normalize value]
    exact checked_source_persistent_chain_field world machine after warm account present agrees base keys
      fields name transient (UInt256.ofNat value) tail success
  | true =>
    simp only [transient, ite_true] at success
    rw [← native_word_normalize value]
    exact checked_source_transient_chain_write world machine after warm account present agrees base keys
      fields name transient (UInt256.ofNat value) tail success

/-- An actual source write and actual checked machine step share the computed final world. -/
theorem resolved_chain_native (fields : List Field) (events : List EventDef) (state : RuntimeState)
    (name : String) (keys : List Nat) (value base : Nat)
    (slots : findFieldWriteSlots fields name = some [base])
    (machine after : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement state.world machine warm) (tail : Stack UInt256)
    (stack : machine.stack = UInt256.ofNat (Entry.location (base, keys.map wordNormalize, 0)) ::
      UInt256.ofNat value :: tail)
    (success : CreationCaller.checkedStep machine
      (if fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok after) :
    ∃ final, execStmtWithEvents fields events state
      (.setMappingChain name (keys.map Expr.literal) (.literal value)) = .continue final ∧
      Agreement final.world after warm := by
  refine ⟨{ state with world := (writeAddressKeyedMappingChainFieldSlots fields name state.world
    [base] (keys.map wordNormalize) (wordNormalize value)) },
    resolved_chain_statement fields events state name keys value base slots, ?_⟩
  have restored : { machine with stack := (UInt256.ofNat (Entry.location (base, keys.map wordNormalize, 0)) ::
      UInt256.ofNat value :: tail) } = machine := by rw [← stack]
  exact source_chain_native_dispatch fields name state.world machine after warm account present agrees
    base (keys.map wordNormalize) value tail (by simpa only [restored] using success)

/-- Actual typed operands and the actual native write determine the same statement postworld. -/
theorem typed_chain_native (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (initial keyState operandState : RuntimeState) (name : String)
    (keys : List Expr) (value : Expr) (resolvedKeys : List Nat) (resolved base : Nat) (field : Field)
    (keysEvaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel initial keys = .value resolvedKeys keyState)
    (valueEvaluated : SourceExpressionEvaluation.eval
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel keyState value = .value resolved operandState)
    (fieldFound : findFieldWithResolvedSlot fields name = some (field, base))
    (slots : findFieldWriteSlots fields name = some [base])
    (machine after : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement operandState.world machine warm) (tail : Stack UInt256)
    (stack : machine.stack = UInt256.ofNat (Entry.location (base, resolvedKeys.map wordNormalize, 0)) ::
      UInt256.ofNat resolved :: tail)
    (success : CreationCaller.checkedStep machine
      (if fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok after) :
    ∃ final, SourceStatementEvaluation.execStmt spec fields (fuel + 1) initial
      (.setMappingChain name keys value) = .continue final ∧ Agreement final.world after warm := by
  rw [chain_statement_operands spec fields fuel initial keyState operandState name keys value resolvedKeys resolved
    field base keysEvaluated valueEvaluated fieldFound]
  exact resolved_chain_native fields spec.events operandState name resolvedKeys resolved base slots
    machine after warm account present agrees tail stack success

/-- The same actual checked mapping-write step continues the native iterator. -/
theorem source_chain_native_x (fields : List Field) (name : String) (fuel : Nat)
    (machine after : EVM.State)
    (bounded : machine.executionEnv.code.size < UInt256.size)
    (decoded : EVM.Proof.decodeAt machine = ((if fieldIsTransient fields name then .TSTORE else .SSTORE), none))
    (success : CreationCaller.checkedStep machine
      (if fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok after) :
    EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
      EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  apply NativePairedCallerChecks.checked_native_x fuel machine after _ none bounded _ decoded success
  cases fieldIsTransient fields name <;> simp

/-- The complete typed statement and actual native iterator share the same checked write. -/
theorem typed_chain_execution (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (initial keyState operandState : RuntimeState) (name : String)
    (keys : List Expr) (value : Expr) (resolvedKeys : List Nat) (resolved base : Nat) (field : Field)
    (keysEvaluated : SourceExpressionEvaluation.evalArgs
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel initial keys = .value resolvedKeys keyState)
    (valueEvaluated : SourceExpressionEvaluation.eval
      (SourceStatementEvaluation.execStmtsFrame true spec fields fuel)
      spec fields fuel keyState value = .value resolved operandState)
    (fieldFound : findFieldWithResolvedSlot fields name = some (field, base))
    (slots : findFieldWriteSlots fields name = some [base])
    (machine after : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some account)
    (agrees : Agreement operandState.world machine warm) (tail : Stack UInt256)
    (stack : machine.stack = UInt256.ofNat (Entry.location (base, resolvedKeys.map wordNormalize, 0)) ::
      UInt256.ofNat resolved :: tail)
    (nativeFuel : Nat) (bounded : machine.executionEnv.code.size < UInt256.size)
    (decoded : EVM.Proof.decodeAt machine = ((if fieldIsTransient fields name then .TSTORE else .SSTORE), none))
    (success : CreationCaller.checkedStep machine
      (if fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok after) :
    ∃ final, SourceStatementEvaluation.execStmt spec fields (fuel + 1) initial
      (.setMappingChain name keys value) = .continue final ∧ Agreement final.world after warm ∧
      EVM.X (nativeFuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
        EVM.X (nativeFuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  obtain ⟨final, source, related⟩ := typed_chain_native spec fields fuel initial keyState operandState name
    keys value resolvedKeys resolved base field keysEvaluated valueEvaluated fieldFound slots
    machine after warm account present agrees tail stack success
  exact ⟨final, source, related, source_chain_native_x fields name nativeFuel machine after bounded decoded success⟩

end Compiler.Proofs.IRGeneration.NativeSourceMappingExecution
