import Compiler.Proofs.IRGeneration.IRRuntimeTypes
import Verity.Core.Model.PhysicalMemory
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel.DenoteMemory

def PhysicalMemoryMatches (world : Verity.ContractState) (state : IRState) : Prop :=
  world.byteMemory = state.byteMemory ∧
  ∀ offset, (world.memory offset).val = state.memory offset

theorem writePhysicalMemoryValue_matches (world : Verity.ContractState) (state : IRState)
    (offset value : Nat) (physical : world.byteMemory = state.byteMemory) :
    PhysicalMemoryMatches
      (world.writePhysicalMemoryValue offset (Verity.Core.Uint256.ofNat value))
      (state.writePhysicalMemoryValue offset value) := by
  unfold PhysicalMemoryMatches Verity.ContractState.writePhysicalMemoryValue
    Verity.ContractState.writePhysicalMemoryWord IRState.writePhysicalMemoryValue
  rw [physical]
  exact ⟨rfl, fun _ => rfl⟩
/-- Expose the source write as a bounded head-step equation, so continuation
proofs need not normalize the entire byte-backed state. -/
theorem source_mstore_of_eval
    (fields : List Compiler.CompilationModel.Field)
    (runtime : SourceSemantics.RuntimeState)
    (offset value : Compiler.CompilationModel.Expr) (offsetNat valueNat : Nat)
    (hOffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hValue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmt fields runtime (.mstore offset value) =
      .continue { runtime with
        world := runtime.world.writePhysicalMemoryValue offsetNat (Verity.Core.Uint256.ofNat valueNat) } := by
  simp only [SourceSemantics.execStmt, hOffset, hValue]

/-- A successful source mstore delegates the whole tail to its exact poststate. -/
theorem source_mstore_cons_of_eval
    (fields : List Compiler.CompilationModel.Field)
    (runtime : SourceSemantics.RuntimeState)
    (offset value : Compiler.CompilationModel.Expr) (offsetNat valueNat : Nat)
    (rest : List Compiler.CompilationModel.Stmt)
    (hOffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hValue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.mstore offset value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with
          world := runtime.world.writePhysicalMemoryValue offsetNat (Verity.Core.Uint256.ofNat valueNat) } rest := by
  rw [SourceSemantics.execStmtList,
    source_mstore_of_eval fields runtime offset value offsetNat valueNat hOffset hValue]

/-- Exact transient write head, with the same normalized key as EVM tstore. -/
theorem source_tstore_of_eval
    (fields : List Compiler.CompilationModel.Field)
    (runtime : SourceSemantics.RuntimeState)
    (offset value : Compiler.CompilationModel.Expr) (offsetNat valueNat : Nat)
    (hOffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hValue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmt fields runtime (.tstore offset value) =
      .continue { runtime with
        world := runtime.world.writeTransient
          (offsetNat % Compiler.Constants.evmModulus) (Verity.Core.Uint256.ofNat valueNat) } := by
  simp only [SourceSemantics.execStmt, hOffset, hValue]
  rfl

/-- Preserve the exact transient-write poststate when handing execution to the tail. -/
theorem source_tstore_cons_of_eval
    (fields : List Compiler.CompilationModel.Field)
    (runtime : SourceSemantics.RuntimeState)
    (offset value : Compiler.CompilationModel.Expr) (offsetNat valueNat : Nat)
    (rest : List Compiler.CompilationModel.Stmt)
    (hOffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hValue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.tstore offset value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with
          world := runtime.world.writeTransient
            (offsetNat % Compiler.Constants.evmModulus) (Verity.Core.Uint256.ofNat valueNat) } rest := by
  rw [SourceSemantics.execStmtList,
    source_tstore_of_eval fields runtime offset value offsetNat valueNat hOffset hValue]

end Compiler.Proofs.IRGeneration
