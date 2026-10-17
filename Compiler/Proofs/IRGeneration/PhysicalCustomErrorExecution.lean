import Compiler.Proofs.IRGeneration.PhysicalSignatureExecution
import Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarBytes
import Compiler.Proofs.IRGeneration.NonReentrantGuardIR

namespace Compiler.Proofs.IRGeneration.PhysicalCustomErrorExecution
open Compiler.Yul Compiler.CompilationModel PhysicalCustomErrorScalarBytes

def selectorExpr : YulExpr :=
  .call "shl" [.lit selectorShift,
    .call "shr" [.lit selectorShift, .ident "__err_hash"]]

theorem evaluate_selector (state : IRState) (hash : Nat)
    (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus) :
    evalIRExpr state selectorExpr = some (selectorWord hash) := by
  have quotientBound : hash / 2^224 < Compiler.Constants.evmModulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) bounded
  have wordBound : selectorWord hash < Compiler.Constants.evmModulus :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) bounded
  have right := FunctionBody.evalIRExpr_shr_of_eval
    (state := state) (shiftExpr := .lit selectorShift) (valueExpr := .ident "__err_hash")
    (shift := selectorShift) (value := hash)
    (by simp [evalIRExpr]) (by simpa [evalIRExpr] using binding)
  have shiftBound : selectorShift < Compiler.Constants.evmModulus := by decide
  have shiftSmall : selectorShift < 256 := by decide
  simp only [Nat.mod_eq_of_lt shiftBound, shiftSmall, if_true,
    Nat.mod_eq_of_lt bounded] at right
  have left := FunctionBody.evalIRExpr_shl_of_eval
    (state := state) (shiftExpr := .lit selectorShift)
    (valueExpr := .call "shr" [.lit selectorShift, .ident "__err_hash"])
    (shift := selectorShift) (value := hash / 2^224)
    (by simp [evalIRExpr]) right
  simp only [Nat.mod_eq_of_lt shiftBound, shiftSmall, if_true,
    Nat.mod_eq_of_lt quotientBound] at left
  change evalIRExpr state selectorExpr = some (selectorWord hash % Compiler.Constants.evmModulus) at left
  simpa only [Nat.mod_eq_of_lt wordBound] using left

def suffixFinal (state : IRState) (hash : Nat) : IRState :=
  (((state.setVar "__err_selector" (selectorWord hash)).writePhysicalMemoryValue
    0 (selectorWord hash)).setVar "__err_tail" 0).captureRevert 0 4

theorem execute_zero_suffix (state : IRState) (hash extra : Nat)
    (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus) :
    execIRStmts (extra + 5) state PhysicalSignatureExecution.zeroSuffix =
      .revert (suffixFinal state hash) := by
  have selected := evaluate_selector state hash binding bounded
  unfold selectorExpr at selected
  have fuel : extra + 5 = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ extra)))) := by omega
  have four : 4 % Compiler.Constants.evmModulus = 4 := by decide
  rw [fuel]
  simp [PhysicalSignatureExecution.zeroSuffix, execIRStmts, execIRStmt,
    selected, four, evalIRExpr, IRState.getVar, IRState.setVar,
    IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory, suffixFinal,
    evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem execute_zero_suffix_payload (state : IRState) (hash extra : Nat)
    (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus) :
    ∃ final, execIRStmts (extra + 5) state PhysicalSignatureExecution.zeroSuffix =
      .revert final ∧ final.revertBytes = some ((Denote.wordBytes hash).take 4) := by
  refine ⟨suffixFinal state hash, execute_zero_suffix state hash extra binding bounded, ?_⟩
  exact observed_zero_argument_payload (state.setVar "__err_selector" (selectorWord hash)) hash

open PhysicalSignatureExecution

def signaturePrefix (bytes : List UInt8) : List YulStmt :=
  pointerStmt :: (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes])

def hashedState (state : IRState) (bytes : List UInt8) : IRState :=
  (PhysicalRevertWrites.applyStores
    (state.setVar "__err_ptr" (state.memory freeMemoryPointer))
    (PhysicalAbiChunkStores.chunkWrites (state.memory freeMemoryPointer)
      (chunkBytes32 bytes))).setVar "__err_hash"
    (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)

theorem execute_zero_body (state : IRState) (bytes : List UInt8) (extra : Nat)
    (extent : state.memory freeMemoryPointer + 32 * (chunkBytes32 bytes).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ final, execIRStmts ((signaturePrefix bytes).length + extra + 5) state
      (signaturePrefix bytes ++ zeroSuffix) = .revert final ∧
      final.revertBytes = some ((Denote.wordBytes
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)).take 4) := by
  have front : execIRStmts ((signaturePrefix bytes).length + extra + 5) state (signaturePrefix bytes) =
      .continue (hashedState state bytes) := by
    have fuel : (signaturePrefix bytes).length + extra + 5 =
        (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + (extra + 4) + 2 := by
      simp only [signaturePrefix, List.length_cons]
      omega
    rw [fuel]
    exact execute_loaded_signature_hash state bytes (extra + 4) extent
  rw [execIRStmts_append_continue zeroSuffix (signaturePrefix bytes)
    _ state (hashedState state bytes) front]
  rw [show (signaturePrefix bytes).length + extra + 5 - (signaturePrefix bytes).length = extra + 5 by omega]
  apply execute_zero_suffix_payload
  · simp [hashedState, IRState.getVar, IRState.setVar]
  · unfold SourceSemantics.keccakMemorySlice abstractKeccakMemorySlice
    exact Nat.mod_lt _ (by decide)

theorem execute_compiled_zero (source : DynamicDataSource) (definition : ErrorDef)
    (params : definition.params = []) (state : IRState) (extra : Nat)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out final, revertWithCustomError source definition [] [] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 7)
        state out = .revert final ∧
      final.revertBytes = some ((Denote.wordBytes
        (SourceSemantics.keccakMemorySlice
          (Denote.signatureMemory (bytesFromString (errorSignature definition)))
          0 (bytesFromString (errorSignature definition)).length)).take 4) := by
  obtain ⟨final, executed, payload⟩ := execute_zero_body state
    (bytesFromString (errorSignature definition)) extra extent
  refine ⟨_, final, compile_zero_shape source definition params, ?_, payload⟩
  rw [show (signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 7 =
    ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 5) + 2 by omega]
  have bodyExecution : execIRStmts
      ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 5)
      state (pointerStmt ::
        (signatureStores (chunkBytes32 (bytesFromString (errorSignature definition))) 0 ++
          [hashStmt (bytesFromString (errorSignature definition))] ++ zeroSuffix)) =
      .revert final := by
    simpa only [signaturePrefix, List.cons_append, List.append_assoc] using executed
  have blockExecution : execIRStmt
      (((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 5) + 1)
      state (.block (pointerStmt ::
        (signatureStores (chunkBytes32 (bytesFromString (errorSignature definition))) 0 ++
          [hashStmt (bytesFromString (errorSignature definition))] ++ zeroSuffix))) =
      .revert final := bodyExecution
  simp only [execIRStmts, blockExecution]

/-- The computed compiler payload and the actual Source custom-error lookup
agree for a uniquely declared zero-parameter error. -/
theorem compiled_zero_source_bytes (source : DynamicDataSource) (definition : ErrorDef)
    (params : definition.params = []) (state : IRState) (extra : Nat)
    (fields : List Field) (runtime : SourceSemantics.RuntimeState)
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out final data, revertWithCustomError source definition [] [] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 7)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [] =
        .revertWithData data := by
  obtain ⟨out, final, compiled, executed, payload⟩ :=
    execute_compiled_zero source definition params state extra extent
  refine ⟨out, final, _, compiled, executed, payload, ?_⟩
  have sourcePayload := SourceCustomErrorBytes.evaluated_payload fields runtime
    definition.name [] [] definition [] (by rfl) resolved
    (by simp [params]) (by simp [params]) (by simp [params])
  simpa [SourceCustomErrorBytes.hash, errorSignature, params, bytesFromString, toString] using sourcePayload

end Compiler.Proofs.IRGeneration.PhysicalCustomErrorExecution
