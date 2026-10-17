import Compiler.Proofs.IRGeneration.CustomErrorScalarEncoding

namespace Compiler.Proofs.IRGeneration.CustomErrorExpressionFrame
open Compiler.Yul Compiler.CompilationModel

/-- Erase only the temporary variable/memory observations modified by the
custom-error scratch prefix. All other context fields stay visible. -/
def eraseScratch (state : IRState) : IRState :=
  { state with vars := [], memory := fun _ => 0, byteMemory := DenoteMemory.Memory.empty }

structure Frame (left right : IRState) : Prop where
  context : eraseScratch left = eraseScratch right
  binding : ∀ name, name ≠ "__err_ptr" → name ≠ "__err_hash" →
    name ≠ "__err_selector" → name ≠ "__err_tail" → left.getVar name = right.getVar name

mutual
  inductive ScratchExpr : YulExpr → Prop where
    | lit (value : Nat) : ScratchExpr (.lit value)
    | hex (value : Nat) : ScratchExpr (.hex value)
    | str (value : String) : ScratchExpr (.str value)
    | ident (name : String) (ptr : name ≠ "__err_ptr") (hash : name ≠ "__err_hash")
        (selector : name ≠ "__err_selector") (tail : name ≠ "__err_tail") :
        ScratchExpr (.ident name)
    | call (func : String) (args : List YulExpr)
        (noLoad : func ≠ "mload") (noHash : func ≠ "keccak256")
        (nested : ScratchExprs args) : ScratchExpr (.call func args)
  inductive ScratchExprs : List YulExpr → Prop where
    | nil : ScratchExprs []
    | cons {head tail} : ScratchExpr head → ScratchExprs tail → ScratchExprs (head :: tail)
end

private theorem call_frame (left right : IRState) (frame : Frame left right)
    (func : String) (args : List YulExpr) (noLoad : func ≠ "mload")
    (noHash : func ≠ "keccak256")
    (arguments : evalIRExprs left args = evalIRExprs right args) :
    evalIRCall left func args = evalIRCall right func args := by
  have storage := congrArg IRState.storage frame.context
  simp only [eraseScratch] at storage
  have transientStorage := congrArg IRState.transientStorage frame.context
  simp only [eraseScratch] at transientStorage
  have codeSize := congrArg IRState.codeSize frame.context
  simp only [eraseScratch] at codeSize
  have returndata := congrArg IRState.returndata frame.context
  simp only [eraseScratch] at returndata
  have sender := congrArg IRState.sender frame.context
  simp only [eraseScratch] at sender
  have msgValue := congrArg IRState.msgValue frame.context
  simp only [eraseScratch] at msgValue
  have thisAddress := congrArg IRState.thisAddress frame.context
  simp only [eraseScratch] at thisAddress
  have blockTimestamp := congrArg IRState.blockTimestamp frame.context
  simp only [eraseScratch] at blockTimestamp
  have blockNumber := congrArg IRState.blockNumber frame.context
  simp only [eraseScratch] at blockNumber
  have chainId := congrArg IRState.chainId frame.context
  simp only [eraseScratch] at chainId
  have blobBaseFee := congrArg IRState.blobBaseFee frame.context
  simp only [eraseScratch] at blobBaseFee
  have txOrigin := congrArg IRState.txOrigin frame.context
  simp only [eraseScratch] at txOrigin
  have selector := congrArg IRState.selector frame.context
  simp only [eraseScratch] at selector
  have calldata := congrArg IRState.calldata frame.context
  simp only [eraseScratch] at calldata
  simp only [evalIRCall, arguments, noLoad, noHash, if_false, storage, transientStorage, codeSize, returndata, sender, msgValue, thisAddress, blockTimestamp, blockNumber, chainId, blobBaseFee, txOrigin, selector, calldata]

mutual
  theorem expression_frame (left right : IRState) (frame : Frame left right)
      (expr : YulExpr) (supported : ScratchExpr expr) :
      evalIRExpr left expr = evalIRExpr right expr := by
    cases supported with
    | lit value => simp [evalIRExpr]
    | hex value => simp [evalIRExpr]
    | str value => simp [evalIRExpr]
    | ident name ptr hash selector tail =>
        simpa only [evalIRExpr] using frame.binding name ptr hash selector tail
    | call func args noLoad noHash nested =>
        simp only [evalIRExpr]
        exact call_frame left right frame func args noLoad noHash
          (arguments_frame left right frame args nested)
  theorem arguments_frame (left right : IRState) (frame : Frame left right)
      (args : List YulExpr) (supported : ScratchExprs args) :
      evalIRExprs left args = evalIRExprs right args := by
    cases supported with
    | nil => simp [evalIRExprs]
    | @cons head tail first rest =>
        simp only [evalIRExprs, expression_frame left right frame head first,
          arguments_frame left right frame tail rest]
end

private theorem erase_write (state : IRState) (offset value : Nat) :
    eraseScratch (state.writePhysicalMemoryValue offset value) = eraseScratch state := rfl
private theorem erase_setVar (state : IRState) (name : String) (value : Nat) :
    eraseScratch (state.setVar name value) = eraseScratch state := rfl
private theorem erase_stores (state : IRState) (writes : List (Nat × Nat)) :
    eraseScratch (PhysicalRevertWrites.applyStores state writes) = eraseScratch state := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      rw [PhysicalRevertWrites.applyStores, ih, erase_write]

theorem argument_state_frame (state : IRState) (bytes : List UInt8) :
    Frame (PhysicalCustomErrorScalarExecution.argumentState
      (PhysicalCustomErrorExecution.hashedState state bytes)
      (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) state := by
  constructor
  · simp only [PhysicalCustomErrorScalarExecution.argumentState,
      PhysicalCustomErrorExecution.hashedState, erase_setVar, erase_write, erase_stores]
  · intro name ptr hash selector tail
    have atomic := CustomErrorScalarEncoding.argument_frame state bytes (.ident name)
      (Or.inr (Or.inr (Or.inl ⟨name, rfl, ptr, hash, selector, tail⟩)))
    simpa only [evalIRExpr] using atomic

theorem argument_expression_frame (state : IRState) (bytes : List UInt8)
    (expr : YulExpr) (supported : ScratchExpr expr) :
    evalIRExpr (PhysicalCustomErrorScalarExecution.argumentState
      (PhysicalCustomErrorExecution.hashedState state bytes)
      (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) expr =
      evalIRExpr state expr :=
  expression_frame _ state (argument_state_frame state bytes) expr supported

open PhysicalCustomErrorScalarExecution PhysicalCustomErrorExecution

theorem compiled_recursive_source_bytes (source : DynamicDataSource) (definition : ErrorDef)
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
        .revertWithData data := by
  apply compiled_scalar_source_bytes source definition ty srcExpr argExpr encoded params scalar
    encoding state value extra fields runtime typeName evaluated resolved canonical supported extent
  apply CustomErrorScalarEncoding.evaluate_encoding _ definition.name ty argExpr encoded value typeName
    supported canonical
  · rw [argument_expression_frame state (bytesFromString (errorSignature definition)) argExpr supportedExpr]
    exact argument
  · exact encoding

end Compiler.Proofs.IRGeneration.CustomErrorExpressionFrame
