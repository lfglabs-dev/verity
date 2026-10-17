import Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes

namespace Compiler.Proofs.IRGeneration.ImportedAbiWordCopy
open Compiler.CompilationModel Denote DenoteMemory PhysicalMemory

/-- A coherent overlapping word load returns exactly its physical32-byte window. -/
theorem load_word (world : Verity.ContractState) (coherent : Coherent world) (source : Nat) :
    valueWord (world.memory source) = world.byteMemory.readWord source := by
  rw [coherent source, valueWord_wordValue]

/-- A single actual word load/store is an exact32-byte snapshot copy, including
expansion, ALL overlapping word views and every nonmemory world component.
No alignment or source/destination disjointness is necessary for one word. -/
theorem copied_world (world : Verity.ContractState) (coherent : Coherent world) (source destination : Nat) :
    world.writePhysicalMemoryValue destination (world.memory source) =
      world.copyPhysicalBytes world.physicalByte destination source 32 := by
  unfold Verity.ContractState.writePhysicalMemoryValue Verity.ContractState.writePhysicalMemoryWord
  rw [load_word world coherent source]
  change world.installPhysicalMemory (world.byteMemory.writeWord destination (world.byteMemory.readWord source)) =
    world.installPhysicalMemory (world.byteMemory.copyFrom world.physicalByte destination source 32)
  rfl

/-- Execute an actual mstore(mload) with resolved pointer expressions, deriving
its complete snapshot-copy poststate rather than assuming output bytes. -/
theorem executed (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceExpr destinationExpr : Expr) (source destination : Nat)
    (coherent : Coherent state.world)
    (read : evalExpr oracle fields state sourceExpr = some source)
    (write : evalExpr oracle fields state destinationExpr = some destination) :
    execStmt oracle fields state (.mstore destinationExpr (.mload sourceExpr)) =
      .continue { state with world := state.world.copyPhysicalBytes state.world.physicalByte destination source 32 } := by
  have loaded : evalExpr oracle fields state (.mload sourceExpr) = some (state.world.memory source).val := by
    rw [evalExpr, read]
    rfl
  rw [execStmt_mstore_physical oracle fields state destinationExpr (.mload sourceExpr)
    destination (state.world.memory source).val write loaded]
  have word : Verity.Core.Uint256.ofNat (state.world.memory source).val = state.world.memory source := by
    apply Verity.Core.Uint256.ext
    exact Nat.mod_eq_of_lt (state.world.memory source).isLt
  rw [word, copied_world state.world coherent source destination]

end Compiler.Proofs.IRGeneration.ImportedAbiWordCopy
