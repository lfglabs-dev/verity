import Compiler.Proofs.IRGeneration.PhysicalCustomErrorExecution

namespace Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarExecution
open Compiler.Yul Compiler.CompilationModel PhysicalCustomErrorScalarBytes
open PhysicalCustomErrorExecution PhysicalSignatureExecution

def scalarSuffix (encoded : YulExpr) : List YulStmt :=
  [.let_ "__err_selector" selectorExpr,
    .exprStmt (.call "mstore" [.lit 0, .ident "__err_selector"]),
    .let_ "__err_tail" (.lit 32),
    .exprStmt (.call "mstore" [.lit 4, encoded]),
    .exprStmt (.call "revert" [.lit 0, .call "add" [.lit 4, .ident "__err_tail"]])]

def argumentState (state : IRState) (hash : Nat) : IRState :=
  ((state.setVar "__err_selector" (selectorWord hash)).writePhysicalMemoryValue
    0 (selectorWord hash)).setVar "__err_tail" 32

def scalarFinal (state : IRState) (hash value : Nat) : IRState :=
  ((argumentState state hash).writePhysicalMemoryValue 4 value).captureRevert 0 36

/-- Evaluate the argument at the real point of its compiler execution, after
signature scratch writes and selector/tail setup. -/
theorem execute_scalar_suffix (state : IRState) (hash value extra : Nat) (encoded : YulExpr)
    (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus)
    (argument : evalIRExpr (argumentState state hash) encoded = some value) :
    execIRStmts (extra + 6) state (scalarSuffix encoded) =
      .revert (scalarFinal state hash value) := by
  have selected := evaluate_selector state hash binding bounded
  have fuel : extra + 6 = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ extra))))) := by omega
  have four : 4 % Compiler.Constants.evmModulus = 4 := by decide
  have thirtySix : 36 % Compiler.Constants.evmModulus = 36 := by decide
  rw [fuel]
  simp only [scalarSuffix, execIRStmts, execIRStmt, selected]
  simp [argumentState, IRState.setVar, IRState.writePhysicalMemoryValue,
    IRState.installPhysicalMemory] at argument
  simp [evalIRExpr, IRState.getVar, IRState.setVar, IRState.writePhysicalMemoryValue,
    IRState.installPhysicalMemory, argument, scalarFinal, argumentState, thirtySix, four,
    evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem execute_scalar_suffix_payload (state : IRState) (hash value extra : Nat)
    (encoded : YulExpr) (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus)
    (argument : evalIRExpr (argumentState state hash) encoded = some value) :
    ∃ final, execIRStmts (extra + 6) state (scalarSuffix encoded) = .revert final ∧
      final.revertBytes = some ((Denote.wordBytes hash).take 4 ++ Denote.wordBytes value) := by
  refine ⟨scalarFinal state hash value,
    execute_scalar_suffix state hash value extra encoded binding bounded argument, ?_⟩
  exact observed_payload
    ((state.setVar "__err_selector" (selectorWord hash)).setVar "__err_tail" 32) hash value

def staticScalar : ParamType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => true
  | _ => false

theorem compile_scalar_shape (source : DynamicDataSource) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (params : definition.params = [ty]) (scalar : staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded) :
    revertWithCustomError source definition [srcExpr] [argExpr] = .ok
      [.block (signaturePrefix (bytesFromString (errorSignature definition)) ++ scalarSuffix encoded)] := by
  unfold revertWithCustomError signaturePrefix pointerStmt signatureStores hashStmt
    scalarSuffix selectorExpr
  cases ty <;> simp_all [staticScalar, revertWithCustomError.attachOffsets,
    abiHeadSize, eventHeadWordSize, paramHeadSize, List.append_assoc]

/-- Execute the real signature prefix at the scalar payload's budget. -/
theorem execute_scalar_signature (state : IRState) (bytes : List UInt8) (extra : Nat)
    (extent : state.memory freeMemoryPointer + 32 * (chunkBytes32 bytes).length ≤
      Verity.Core.Uint256.modulus) :
    execIRStmts ((signaturePrefix bytes).length + extra + 6) state
      (signaturePrefix bytes) = .continue (hashedState state bytes) := by
  have fuel : (signaturePrefix bytes).length + extra + 6 =
      (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + (extra + 5) + 2 := by
    simp only [signaturePrefix, List.length_cons]
    omega
  rw [fuel]
  exact execute_loaded_signature_hash state bytes (extra + 5) extent

theorem execute_compiled_scalar (source : DynamicDataSource) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (params : definition.params = [ty]) (scalar : staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr
      (argumentState (hashedState state (bytesFromString (errorSignature definition)))
        (SourceSemantics.keccakMemorySlice
          (Denote.signatureMemory (bytesFromString (errorSignature definition))) 0
          (bytesFromString (errorSignature definition)).length)) encoded = some value) :
    ∃ out final, revertWithCustomError source definition [srcExpr] [argExpr] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 8)
        state out = .revert final ∧
      final.revertBytes = some ((Denote.wordBytes
        (SourceSemantics.keccakMemorySlice
          (Denote.signatureMemory (bytesFromString (errorSignature definition))) 0
          (bytesFromString (errorSignature definition)).length)).take 4 ++ Denote.wordBytes value) := by
  let bytes := bytesFromString (errorSignature definition)
  have front := execute_scalar_signature state bytes extra extent
  have suffix := execute_scalar_suffix_payload (hashedState state bytes)
    (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)
    value extra encoded (by simp [hashedState, IRState.getVar, IRState.setVar])
    (by unfold SourceSemantics.keccakMemorySlice abstractKeccakMemorySlice
        exact Nat.mod_lt _ (by decide)) argument
  obtain ⟨final, executed, payload⟩ := suffix
  have bodyExecution : execIRStmts ((signaturePrefix bytes).length + extra + 6) state
      (signaturePrefix bytes ++ scalarSuffix encoded) = .revert final := by
    rw [execIRStmts_append_continue (scalarSuffix encoded) (signaturePrefix bytes)
      _ state (hashedState state bytes) front]
    rw [show (signaturePrefix bytes).length + extra + 6 - (signaturePrefix bytes).length =
      extra + 6 by omega]
    exact executed
  refine ⟨_, final, compile_scalar_shape source definition ty srcExpr argExpr encoded
    params scalar encoding, ?_, payload⟩
  have blockExecution : execIRStmt (((signaturePrefix bytes).length + extra + 6) + 1)
      state (.block (signaturePrefix bytes ++ scalarSuffix encoded)) = .revert final := bodyExecution
  change execIRStmts ((signaturePrefix bytes).length + extra + 8) state
    [.block (signaturePrefix bytes ++ scalarSuffix encoded)] = .revert final
  rw [show (signaturePrefix bytes).length + extra + 8 =
    (((signaturePrefix bytes).length + extra + 6) + 1) + 1 by omega]
  simp only [execIRStmts, blockExecution]

theorem scalar_type_name (ty : ParamType) (typeName : String)
    (supported : Denote.errorScalarType ty = some typeName) :
    paramTypeToSolidityString ty = typeName := by
  cases ty <;> simp_all [Denote.errorScalarType, paramTypeToSolidityString]

theorem compiled_scalar_source_bytes (source : DynamicDataSource) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (params : definition.params = [ty]) (scalar : staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr
      (argumentState (hashedState state (bytesFromString (errorSignature definition)))
        (SourceSemantics.keccakMemorySlice
          (Denote.signatureMemory (bytesFromString (errorSignature definition))) 0
          (bytesFromString (errorSignature definition)).length)) encoded = some value) :
    ∃ out final data, revertWithCustomError source definition [srcExpr] [argExpr] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 8)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [srcExpr] =
        .revertWithData data := by
  obtain ⟨out, final, compiled, executed, payload⟩ := execute_compiled_scalar source definition
    ty srcExpr argExpr encoded params scalar encoding state value extra extent argument
  refine ⟨out, final, _, compiled, executed, payload, ?_⟩
  have sourcePayload := SourceCustomErrorBytes.evaluated_payload fields runtime
    definition.name [srcExpr] [value] definition [typeName] evaluated resolved
    (by simp [params]) (by simp [params, canonical]) (by simp [params, supported])
  have nameEq := scalar_type_name ty typeName supported
  simpa [SourceCustomErrorBytes.hash, errorSignature, params, bytesFromString, toString,
    nameEq] using sourcePayload

end Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarExecution
