import Compiler.Proofs.IRGeneration.PhysicalSignatureHash
import Compiler.Proofs.IRGeneration.PhysicalEventMemory

namespace Compiler.Proofs.IRGeneration.PhysicalSignatureExecution
open Compiler.Yul Compiler.CompilationModel

private theorem stores_vars (state : IRState) (writes : List (Nat × Nat)) :
    (PhysicalRevertWrites.applyStores state writes).vars = state.vars := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih => exact ih _

/-- The compiler's indexed signature stores, with its actual pointer name. -/
def signatureStores (chunks : List (List UInt8)) (start : Nat) : List YulStmt :=
  (chunks.zipIdx start).map (fun (chunk, index) =>
    .exprStmt (.call "mstore" [
      .call "add" [.ident "__err_ptr", .lit (index * 32)], .hex (wordFromBytes chunk)]))

set_option maxRecDepth 2048 in
theorem signatureStores_continue (chunks : List (List UInt8)) (state : IRState)
    (base start : Nat) (pointer : state.getVar "__err_ptr" = some base) :
    PhysicalStoresContinueTo state (signatureStores chunks start)
      (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites (base + start * 32) chunks)) := by
  induction chunks generalizing state start with
  | nil => rfl
  | cons chunk tail ih =>
      simp only [signatureStores, List.zipIdx_cons, List.map_cons,
        PhysicalStoresContinueTo, PhysicalAbiChunkStores.chunkWrites,
        PhysicalRevertWrites.applyStores]
      have added := FunctionBody.evalIRExpr_add_of_eval
        (state := state) (lhs := .ident "__err_ptr") (rhs := .lit (start * 32))
        (a := base) (b := start * 32)
        (by simpa [evalIRExpr] using pointer) (by simp [evalIRExpr])
      refine ⟨state.writePhysicalMemoryValue
        (Verity.Core.Uint256.ofNat (base + start * 32)).val (wordFromBytes chunk), ?_, ?_⟩
      · intro extra
        simpa only [Verity.Core.Uint256.val_ofNat, Compiler.Constants.evmModulus,
          Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Nat.mod_mod] using
          execIRStmt_physical_mstore_of_eval state
            (.call "add" [.ident "__err_ptr", .lit (start * 32)])
            (.hex (wordFromBytes chunk))
            ((base + start * 32) % Compiler.Constants.evmModulus)
            (wordFromBytes chunk) extra added (by simp [evalIRExpr])
      · have nextPointer :
            (state.writePhysicalMemoryValue
              (Verity.Core.Uint256.ofNat (base + start * 32)).val
              (wordFromBytes chunk)).getVar "__err_ptr" = some base := pointer
        have tailResult := ih _ (start + 1) nextPointer
        have address : base + (start + 1) * 32 = base + start * 32 + 32 := by omega
        simpa only [signatureStores, address] using tailResult

theorem execute_signatureStores (chunks : List (List UInt8)) (state : IRState)
    (base extra : Nat) (pointer : state.getVar "__err_ptr" = some base) :
    execIRStmts ((signatureStores chunks 0).length + extra + 1) state
      (signatureStores chunks 0) =
      .continue (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base chunks)) := by
  simpa only [Nat.zero_mul, Nat.add_zero] using
    execIRStmts_of_physicalStoresContinueTo
      (signatureStores_continue chunks state base 0 pointer) extra

/-- The actual custom-error compiler's hash statement. -/
def hashStmt (bytes : List UInt8) : YulStmt :=
  .let_ "__err_hash" (.call "keccak256" [.ident "__err_ptr", .lit bytes.length])

/-- Execute the actual hash statement after physical signature placement.
The pointer is an observed variable binding, not an assumed hash result. -/
theorem execute_hash (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (pointer : state.getVar "__err_ptr" = some base) (extra : Nat) :
    execIRStmt (extra + 1)
      (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))) (hashStmt bytes) =
      .continue ((PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) := by
  have binding : (PhysicalRevertWrites.applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).getVar "__err_ptr" =
      some base := by
    unfold IRState.getVar
    rw [stores_vars]
    exact pointer
  have hashed := PhysicalSignatureHash.hash_eq state base bytes extent
  simp [hashStmt, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, binding, hashed]

/-- Execute the complete signature-writing/hash segment of the custom-error
prefix, retaining the actual computed hash in the actual compiler variable. -/
theorem execute_signature_hash (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (pointer : state.getVar "__err_ptr" = some base) (extra : Nat) :
    execIRStmts
      ((signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + extra + 1)
      state (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]) =
      .continue ((PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) := by
  have front := signatureStores_continue (chunkBytes32 bytes) state base 0 pointer
  simp only [Nat.zero_mul, Nat.add_zero] at front
  have back : PhysicalStoresContinueTo
      (PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))) [hashStmt bytes]
      ((PhysicalRevertWrites.applyStores state
        (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) :=
    ⟨_, execute_hash state base bytes extent pointer, rfl⟩
  exact execIRStmts_of_physicalStoresContinueTo
    (physicalStoresContinueTo_append front back) extra

def pointerStmt : YulStmt :=
  .let_ "__err_ptr" (.call "mload" [.lit freeMemoryPointer])

theorem execute_pointer (state : IRState) (extra : Nat) :
    execIRStmt (extra + 1) state pointerStmt =
      .continue (state.setVar "__err_ptr" (state.memory freeMemoryPointer)) := by
  simp [pointerStmt, execIRStmt, evalIRExpr]

/-- The actual free-pointer load followed by all signature writes and hashing.
The extent obligation is on the pointer read from the actual initial memory. -/
theorem execute_loaded_signature_hash (state : IRState) (bytes : List UInt8) (extra : Nat)
    (extent : state.memory freeMemoryPointer + 32 * (chunkBytes32 bytes).length ≤
      Verity.Core.Uint256.modulus) :
    execIRStmts
      ((signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + extra + 2)
      state (pointerStmt :: (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes])) =
      .continue ((PhysicalRevertWrites.applyStores
        (state.setVar "__err_ptr" (state.memory freeMemoryPointer))
        (PhysicalAbiChunkStores.chunkWrites (state.memory freeMemoryPointer)
          (chunkBytes32 bytes))).setVar "__err_hash"
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) := by
  have step := execute_pointer state
    ((signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + extra)
  rw [show (signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + extra + 2 =
    ((signatureStores (chunkBytes32 bytes) 0 ++ [hashStmt bytes]).length + extra + 1) + 1 by omega]
  simp only [execIRStmts, step]
  exact execute_signature_hash
    (state.setVar "__err_ptr" (state.memory freeMemoryPointer))
    (state.memory freeMemoryPointer) bytes extent
    (by simp [IRState.getVar, IRState.setVar]) extra

/-- Remaining zero-argument instructions, unchanged from the ABI compiler. -/
def zeroSuffix : List YulStmt :=
  [.let_ "__err_selector"
      (.call "shl" [.lit selectorShift,
        .call "shr" [.lit selectorShift, .ident "__err_hash"]]),
    .exprStmt (.call "mstore" [.lit 0, .ident "__err_selector"]),
    .let_ "__err_tail" (.lit 0),
    .exprStmt (.call "revert" [.lit 0, .call "add" [.lit 4, .ident "__err_tail"]])]

theorem compile_zero_shape (source : DynamicDataSource) (definition : ErrorDef)
    (params : definition.params = []) :
    revertWithCustomError source definition [] [] = .ok
      [.block (pointerStmt ::
        (signatureStores (chunkBytes32 (bytesFromString (errorSignature definition))) 0 ++
          [hashStmt (bytesFromString (errorSignature definition))] ++ zeroSuffix))] := by
  unfold revertWithCustomError pointerStmt signatureStores hashStmt zeroSuffix
  simp [params]
  rfl

end Compiler.Proofs.IRGeneration.PhysicalSignatureExecution
