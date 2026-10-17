import Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarBytes
import Compiler.Proofs.IRGeneration.SourceCustomErrorBytes
import Compiler.Proofs.IRGeneration.PhysicalSignatureHash
import Compiler.Proofs.IRGeneration.PhysicalSignatureExecution
import Compiler.Proofs.IRGeneration.PhysicalCustomErrorExecution
import Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarExecution
import Compiler.Proofs.IRGeneration.CustomErrorScalarEncoding
import Compiler.Proofs.IRGeneration.CustomErrorExpressionFrame
import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorBytes
import Compiler.Proofs.IRGeneration.TypedRevertStep
import Compiler.Proofs.IRGeneration.GenericInduction.ErrorRevert

namespace SolidityImportSmoke.PhysicalCustomErrorChecks
open Compiler.Proofs.IRGeneration Compiler.CompilationModel Compiler.Yul
open PhysicalCustomErrorScalarBytes

example (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus) :
    abstractKeccakMemorySlice (PhysicalRevertWrites.applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).memory base bytes.length =
      SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length :=
  PhysicalSignatureHash.hash_eq state base bytes extent

example (chunks : List (List UInt8)) (state : IRState) (base extra : Nat)
    (pointer : state.getVar "__err_ptr" = some base) :
    execIRStmts ((PhysicalSignatureExecution.signatureStores chunks 0).length + extra + 1)
      state (PhysicalSignatureExecution.signatureStores chunks 0) =
      .continue (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base chunks)) :=
  PhysicalSignatureExecution.execute_signatureStores chunks state base extra pointer

example (state : IRState) (base : Nat) (bytes : List UInt8) (extra : Nat)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (pointer : state.getVar "__err_ptr" = some base) :
    execIRStmt (extra + 1)
      (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes)))
      (PhysicalSignatureExecution.hashStmt bytes) =
      .continue ((PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) :=
  PhysicalSignatureExecution.execute_hash state base bytes extent pointer extra

example (state : IRState) (bytes : List UInt8) (extra : Nat)
    (extent : state.memory freeMemoryPointer + 32 * (chunkBytes32 bytes).length ≤
      Verity.Core.Uint256.modulus) :
    execIRStmts
      ((PhysicalSignatureExecution.signatureStores (chunkBytes32 bytes) 0 ++
        [PhysicalSignatureExecution.hashStmt bytes]).length + extra + 2)
      state (PhysicalSignatureExecution.pointerStmt ::
        (PhysicalSignatureExecution.signatureStores (chunkBytes32 bytes) 0 ++
          [PhysicalSignatureExecution.hashStmt bytes])) =
      .continue ((PhysicalRevertWrites.applyStores
        (state.setVar "__err_ptr" (state.memory freeMemoryPointer))
        (PhysicalAbiChunkStores.chunkWrites (state.memory freeMemoryPointer)
          (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) :=
  PhysicalSignatureExecution.execute_loaded_signature_hash state bytes extra extent

example (source : DynamicDataSource) (definition : ErrorDef) (params : definition.params = []) :
    revertWithCustomError source definition [] [] = .ok
      [.block (PhysicalSignatureExecution.pointerStmt ::
        (PhysicalSignatureExecution.signatureStores
          (chunkBytes32 (bytesFromString (errorSignature definition))) 0 ++
          [PhysicalSignatureExecution.hashStmt (bytesFromString (errorSignature definition))] ++
          PhysicalSignatureExecution.zeroSuffix))] :=
  PhysicalSignatureExecution.compile_zero_shape source definition params

example (source : DynamicDataSource) (definition : ErrorDef)
    (params : definition.params = []) (state : IRState) (extra : Nat)
    (fields : List Field) (runtime : SourceSemantics.RuntimeState)
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out final data, revertWithCustomError source definition [] [] = .ok out ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [] =
        .revertWithData data :=
  PhysicalCustomErrorExecution.compiled_zero_source_bytes source definition params state extra
    fields runtime resolved extent

example (state : IRState) (hash extra : Nat)
    (binding : state.getVar "__err_hash" = some hash)
    (bounded : hash < Compiler.Constants.evmModulus) :
    ∃ final, execIRStmts (extra + 5) state PhysicalSignatureExecution.zeroSuffix =
      .revert final ∧ final.revertBytes = some ((Denote.wordBytes hash).take 4) :=
  PhysicalCustomErrorExecution.execute_zero_suffix_payload state hash extra binding bounded

example (state : IRState) :
    execIRStmts 0 state PhysicalSignatureExecution.zeroSuffix = .revert state := rfl

open PhysicalCustomErrorScalarExecution PhysicalCustomErrorExecution

example (source : DynamicDataSource) (definition : ErrorDef)
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
        .revertWithData data :=
  compiled_scalar_source_bytes source definition ty srcExpr argExpr encoded params scalar encoding
    state value extra fields runtime typeName evaluated resolved canonical supported extent argument

open CustomErrorScalarEncoding

example (source : DynamicDataSource) (definition : ErrorDef)
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
    (argument : evalIRExpr state argExpr = some value)
    (independent : ScratchIndependent argExpr) :
    ∃ out final data, revertWithCustomError source definition [srcExpr] [argExpr] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 8)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [srcExpr] =
        .revertWithData data :=
  compiled_atomic_source_bytes source definition ty srcExpr argExpr encoded params scalar encoding
    state value extra fields runtime typeName evaluated resolved canonical supported extent
    argument independent

example (state : IRState) (expr encoded : YulExpr) (value : Nat)
    (evaluated : evalIRExpr state expr = some value)
    (canonical : value < 256)
    (encoding : encodeStaticCustomErrorArg "E" .uint8 expr = .ok encoded) :
    evalIRExpr state encoded = some value :=
  evaluate_encoding state "E" .uint8 expr encoded value "uint8" rfl
    (by simpa [Denote.errorScalarValueValid] using canonical) evaluated encoding

example : ¬ ScratchIndependent (.ident "__err_hash") := by
  simp [ScratchIndependent]

open CustomErrorExpressionFrame

example (source : DynamicDataSource) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (params : definition.params = [ty]) (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
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
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr) :
    ∃ out final data, revertWithCustomError source definition [srcExpr] [argExpr] = .ok out ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 8)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [srcExpr] =
        .revertWithData data :=
  compiled_recursive_source_bytes source definition ty srcExpr argExpr encoded params scalar encoding
    state value extra fields runtime typeName evaluated resolved canonical supported extent
    argument supportedExpr

example : ScratchExpr (.call "add" [.lit 7, .call "sload" [.lit 1]]) :=
  .call "add" _ (by decide) (by decide)
    (.cons (.lit 7) (.cons (.call "sload" _ (by decide) (by decide) (.cons (.lit 1) .nil)) .nil))

example (offset : YulExpr) : ¬ ScratchExpr (.call "mload" [offset]) := by
  intro supported
  cases supported with
  | call func args noLoad noHash nested => exact noLoad rfl

example
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (definition : ErrorDef) (extra : Nat)
    (params : definition.params = [])
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition])
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out sourceResult irExec,
      Compiler.CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.revertError definition.name []) = .ok out ∧
      SourceSemantics.execStmt fields runtime (.revertError definition.name []) = sourceResult ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError definition.name []))
        sourceResult irExec :=
  compiled_revertError_zero_exact_bytes fields scope errors runtime state definition extra
    params compilerLookup runtimeLookup extent

example (definition : ErrorDef) (fields : List Field)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (scope : List String) (errors : List ErrorDef)
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals fields .calldata [] [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty]) (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (runtime : SourceSemantics.RuntimeState) (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr) :
    ∃ out sourceResult irExec,
      Compiler.CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.revertError definition.name [srcExpr]) = .ok out ∧
      SourceSemantics.execStmt fields runtime (.revertError definition.name [srcExpr]) = sourceResult ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError definition.name [srcExpr]))
        sourceResult irExec :=
  compiled_revertError_scalar_exact_bytes definition fields ty srcExpr argExpr encoded scope errors
    compilerLookup compiledArgs params scalar encoding state value extra runtime typeName
    evaluated resolved canonical supported extent argument supportedExpr

example
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (definition : ErrorDef) (cond : Expr) (failCond : YulExpr) (extra : Nat)
    (params : definition.params = [])
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition])
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out data final,
      Compiler.CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.requireError cond definition.name []) = .ok [.if_ failCond out] ∧
      SourceSemantics.execStmt fields runtime (.requireError cond definition.name []) =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9)
        state [.if_ failCond out] = .revert final ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond definition.name []))
        (.revertWithData data) (.revert final) :=
  compiled_requireError_zero_failure_exact_bytes fields scope errors runtime state definition cond
    failCond extra params compilerLookup runtimeLookup condition sourceCond compiledCond extent

example
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compilerLookup : spec.errors.find? (·.name == definition.name) = some definition)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (compiled : Compiler.CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.revertError definition.name []) = .ok out) :
    CompiledErrorStepWithin spec fields scope (.revertError definition.name []) out
      ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 5) :=
  compiledStmtStep_revertError_zeroArg spec fields scope definition out params compilerLookup unique compiled

example
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (name : String) (args : List Expr) (out : List YulStmt)
    (helperFuel extraFuel : Nat) (data : List UInt8)
    (compiled : Compiler.CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.revertError name args) = .ok out)
    (sourcePayload : SourceSemantics.typedErrorRevertResult fields runtime name args = .revertWithData data)
    (executed : execIRStmts (out.length + extraFuel + 1) state out = .revert final)
    (payload : final.revertBytes = some data) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime (.revertError name args) = sourceResult ∧
      execIRStmts (out.length + extraFuel + 1) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError name args)) sourceResult irExec :=
  compiledStmtStep_revertError spec fields scope runtime state final name args out helperFuel extraFuel data
    compiled sourcePayload executed payload

example
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt) (helperFuel extraFuel : Nat) (data : List UInt8)
    (compiled : Compiler.CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.requireError cond name args) = .ok [.if_ failCond out])
    (sourceCondition : SourceSemantics.evalExprWithHelpers spec fields helperFuel runtime cond = some 0)
    (compiledCondition : evalIRExpr state failCond = some 1)
    (sourcePayload : SourceSemantics.typedErrorRevertResult fields runtime name args = .revertWithData data)
    (executed : execIRStmts extraFuel state out = .revert final)
    (payload : final.revertBytes = some data) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (.requireError cond name args) = sourceResult ∧
      execIRStmts ([YulStmt.if_ failCond out].length + extraFuel + 1) state
        [.if_ failCond out] = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args)) sourceResult irExec :=
  compiledStmtStep_requireError spec fields scope runtime state final cond name args failCond out
    helperFuel extraFuel data compiled sourceCondition compiledCondition sourcePayload executed payload

example (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (mismatched : runtime.errors ≠ spec.errors) : ¬ CustomErrorDomain spec runtime state := by
  intro domain
  exact mismatched domain.declarations

def dirty : IRState := (IRState.initial 0).writePhysicalMemoryValue 0 (2^256 - 1)

example (hash value fuel : Nat) :
    ∃ final, execIRStmts ((writes hash value).length + fuel + 2) dirty
      (PhysicalRevertWrites.stores (writes hash value) ++ [.exprStmt (.call "revert" [.lit 0, .lit 36])]) =
      .revert final ∧ final.revertBytes =
        some ((Denote.wordBytes hash).take 4 ++ Denote.wordBytes value) :=
  execute_payload dirty hash value fuel

example (hash fuel : Nat) :
    ∃ final, execIRStmts (fuel + 3) dirty
      (PhysicalRevertWrites.stores [(0, selectorWord hash)] ++
        [.exprStmt (.call "revert" [.lit 0, .lit 4])]) =
      .revert final ∧ final.revertBytes = some ((Denote.wordBytes hash).take 4) :=
  execute_zero_argument_payload dirty hash fuel

example : ((PhysicalRevertWrites.applyStores dirty
    (writes (0x01020304 * 2^224 + 0xdeadbeef) (2^256 - 1))).captureRevert 0 36).revertBytes =
    some ([1, 2, 3, 4] ++ List.replicate 32 255) := by decide +kernel

example : ((dirty.writePhysicalMemoryValue 0
    (selectorWord (0x01020304 * 2^224 + 0xdeadbeef))).captureRevert 0 4).revertBytes =
    some [1, 2, 3, 4] := by decide +kernel

example (fields : List Field) (runtime : SourceSemantics.RuntimeState)
    (name : String) (args : List Expr) (values : List Nat) (definition : ErrorDef)
    (types : List String)
    (evaluated : SourceSemantics.evalExprList fields runtime args = some values)
    (resolved : runtime.errors.filter (·.name == name) = [definition])
    (arity : definition.params.length = values.length)
    (canonical : (definition.params.zip values).all
      (fun pair => Denote.errorScalarValueValid pair.1 pair.2) = true)
    (scalarTypes : definition.params.mapM Denote.errorScalarType = some types) :
    SourceSemantics.typedErrorRevertResult fields runtime name args =
      .revertWithData ((Denote.wordBytes (SourceCustomErrorBytes.hash name types)).take 4 ++
        values.flatMap Denote.wordBytes) :=
  SourceCustomErrorBytes.evaluated_payload fields runtime name args values definition types
    evaluated resolved arity canonical scalarTypes

end SolidityImportSmoke.PhysicalCustomErrorChecks
