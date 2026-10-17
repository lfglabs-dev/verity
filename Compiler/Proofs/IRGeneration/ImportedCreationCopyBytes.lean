import Compiler.SolidityImport.AbiMemory
import Compiler.Proofs.IRGeneration.CreationRelocatedCopies

namespace Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes
open Compiler.CompilationModel Denote DenoteMemory PhysicalMemory
open CreationRelocatedCopies

/-- The actual generated-loop invariant describes physical bytes, including
all addresses outside the copied interval, rather than only aligned word cells. -/
theorem invariant_physical (inputs : AbiCopyInputs) (initial final : DenoteState) (size : Nat)
    (coherent : Coherent initial.world)
    (copied : AbiCopyLoopInvariant inputs initial size final) (address : Nat) :
    final.world.physicalByte address =
      if inputs.destination + inputs.start ≤ address ∧
          address < inputs.destination + inputs.start + size then
        initial.world.physicalByte (inputs.source + (address - (inputs.destination + inputs.start)))
      else initial.world.physicalByte address := by
  apply Fin.ext
  have bytes := copied.2.1 address
  simp only [abiMemoryByte_physical final.world _ copied.2.2.1,
    abiMemoryByte_physical initial.world _ coherent] at bytes
  split <;> split at bytes <;> first | exact bytes | contradiction

/-- Compare the executed loop's bytes with an actual snapshot copy. No final
memory, output byte equality, or zero-lane postcondition is supplied. -/
theorem invariant_copy (inputs : AbiCopyInputs) (initial final : DenoteState) (size : Nat)
    (coherent : Coherent initial.world)
    (copied : AbiCopyLoopInvariant inputs initial size final) (address : Nat) :
    final.world.physicalByte address =
      (initial.world.copyPhysicalBytes initial.world.physicalByte
        (inputs.destination + inputs.start) inputs.source size).physicalByte address := by
  rw [invariant_physical inputs initial final size coherent copied address]
  split
  · rename_i inside
    have point := Verity.ContractState.copyPhysicalBytes_at initial.world initial.world.physicalByte
      (inputs.destination + inputs.start) inputs.source size
      ⟨address - (inputs.destination + inputs.start), by omega⟩
    have same : inputs.destination + inputs.start +
        (address - (inputs.destination + inputs.start)) = address := by omega
    rw [same] at point
    exact point.symm
  · rename_i outside
    exact (Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (by omega)).symm

/-- The whole requested CREATE2 slice of the real loop equals its original
source snapshot, at an independently chosen destination pointer. -/
theorem invariant_slice (inputs : AbiCopyInputs) (initial final : DenoteState) (size : Nat)
    (coherent : Coherent initial.world)
    (copied : AbiCopyLoopInvariant inputs initial size final) :
    Verity.Core.Model.Create2.physicalInitcodeBytes final.world
        (inputs.destination + inputs.start) size =
      Verity.Core.Model.Create2.physicalInitcodeBytes initial.world inputs.source size := by
  apply relocated_slice
  intro index bound
  rw [invariant_physical inputs initial final size coherent copied _]
  rw [if_pos (by omega)]
  congr 1
  omega

/-- All nonmemory fields survive the loop, from its actual complete frame. -/
theorem invariant_world (inputs : AbiCopyInputs) (initial final : DenoteState) (size : Nat)
    (copied : AbiCopyLoopInvariant inputs initial size final) :
    CreationMemoryFrames.Related final.world initial.world := by
  have projected := congrArg (fun state : DenoteState => state.world) copied.2.2.2
  dsimp only [abiCopyFrame] at projected
  exact projected

/-- Execute the real generated loop and derive its exact physical code slice.
Freshness, bounds, nonoverlap and initial zero bytes remain input obligations. -/
theorem executed_slice (oracle : DenoteOracle) (fields : List Field)
    (inputs : AbiCopyInputs) (state : DenoteState) (sizeExpr : Expr)
    (indexName byteName addressName : String) (size : Nat)
    (sizeEval : evalExpr oracle fields state sizeExpr = some size)
    (coherent : Coherent state.world) (held : inputs.Holds state)
    (indexFresh : inputs.Fresh indexName) (byteFresh : inputs.Fresh byteName)
    (addressFresh : inputs.Fresh addressName)
    (distinct : addressName ≠ byteName) (byteIndex : byteName ≠ indexName)
    (addressIndex : addressName ≠ indexName)
    (sourceAligned : inputs.source % 32 = 0) (destinationAligned : inputs.destination % 32 = 0)
    (sourceBound : inputs.source + size < Verity.Core.Uint256.modulus)
    (destinationBound : inputs.destination + (inputs.start + size) < Verity.Core.Uint256.modulus)
    (disjoint : inputs.source + size ≤ inputs.destination + inputs.start ∨
      inputs.destination + inputs.start + size ≤ inputs.source)
    (zero : ∀ index, index < size →
      abiMemoryByte state.world.memory (inputs.destination + inputs.start + index) = 0) :
    ∃ after, execStmt oracle fields state (SolidityImport.AbiEncoding.copyBytes
      (.localVar inputs.sourceName) (.localVar inputs.destinationName) (.localVar inputs.startName)
      sizeExpr indexName byteName addressName) = .continue after ∧
      AbiCopyLoopInvariant inputs state size after ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes after.world
        (inputs.destination + inputs.start) size =
        Verity.Core.Model.Create2.physicalInitcodeBytes state.world inputs.source size := by
  obtain ⟨after, executed, invariant⟩ := execStmt_copyBytes oracle fields inputs state sizeExpr
    indexName byteName addressName size sizeEval coherent held indexFresh byteFresh addressFresh
    distinct byteIndex addressIndex sourceAligned destinationAligned sourceBound destinationBound disjoint zero
  exact ⟨after, executed, invariant, invariant_slice inputs state after size coherent invariant⟩

end Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes

