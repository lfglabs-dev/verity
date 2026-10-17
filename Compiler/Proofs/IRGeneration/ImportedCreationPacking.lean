import Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes

namespace Compiler.Proofs.IRGeneration.ImportedCreationPacking
open Compiler.CompilationModel Denote DenoteMemory PhysicalMemory
open ImportedCreationCopyBytes CreationRelocatedCopies

/-- The first real copy preserves the initial zero payload area. -/
theorem header_preserves_zero (inputs : AbiCopyInputs) (initial header : DenoteState)
    (hsize index : Nat)
    (copied : AbiCopyLoopInvariant inputs initial hsize header)
    (zero : abiMemoryByte initial.world.memory
      (inputs.destination + inputs.start + hsize + index) = 0) :
    abiMemoryByte header.world.memory
      (inputs.destination + inputs.start + hsize + index) = 0 := by
  rw [copied.2.1, if_neg (by omega)]
  exact zero

/-- The second copy's live source is still the pre-header snapshot whenever
that source lies outside the header's write interval. -/
theorem header_preserves_source (inputs : AbiCopyInputs) (initial header : DenoteState)
    (hsize source size : Nat) (coherent : Coherent initial.world)
    (copied : AbiCopyLoopInvariant inputs initial hsize header)
    (disjoint : source + size ≤ inputs.destination + inputs.start ∨
      inputs.destination + inputs.start + hsize ≤ source) :
    ∀ index < size, header.world.physicalByte (source + index) =
      initial.world.physicalByte (source + index) := by
  intro index inside
  rw [invariant_physical inputs initial header hsize coherent copied]
  rw [if_neg (by rcases disjoint with before | after <;> omega)]

/-- Compose the two actually executed loop invariants. The resulting complete
slice equals two true copies from the ORIGINAL snapshots, with distinct input
pointers and arbitrary payload size. No final-byte equality is assumed. -/
theorem packed_snapshot (hinputs pinputs : AbiCopyInputs) (initial header final : DenoteState)
    (hsize psize : Nat) (coherent : Coherent initial.world)
    (hcopy : AbiCopyLoopInvariant hinputs initial hsize header)
    (pcopy : AbiCopyLoopInvariant pinputs header psize final)
    (adjacent : pinputs.destination + pinputs.start = hinputs.destination + hinputs.start + hsize)
    (disjoint : pinputs.source + psize ≤ hinputs.destination + hinputs.start ∨
      hinputs.destination + hinputs.start + hsize ≤ pinputs.source) :
    Verity.Core.Model.Create2.physicalInitcodeBytes final.world
      (hinputs.destination + hinputs.start) (hsize + psize) =
    Verity.Core.Model.Create2.physicalInitcodeBytes
      ((initial.world.copyPhysicalBytes initial.world.physicalByte
        (hinputs.destination + hinputs.start) hinputs.source hsize).copyPhysicalBytes
          initial.world.physicalByte (pinputs.destination + pinputs.start) pinputs.source psize)
      (hinputs.destination + hinputs.start) (hsize + psize) := by
  apply relocated_slice
  intro index bound
  rw [invariant_physical pinputs header final psize hcopy.2.2.1 pcopy]
  by_cases head : index < hsize
  · rw [if_neg (by omega), invariant_physical hinputs initial header hsize coherent hcopy,
      if_pos (by omega)]
    rw [Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (Or.inl (by omega)),
      Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index, head⟩]
    simp only [Nat.add_sub_cancel_left]
  · have tail : index - hsize < psize := by omega
    rw [if_pos (by omega)]
    have position : hinputs.destination + hinputs.start + index =
        pinputs.destination + pinputs.start + (index - hsize) := by omega
    have relative : hinputs.destination + hinputs.start + index -
        (pinputs.destination + pinputs.start) = index - hsize := by omega
    rw [relative, header_preserves_source hinputs initial header hsize pinputs.source psize
      coherent hcopy disjoint (index - hsize) tail, position,
      Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨index - hsize, tail⟩]

end Compiler.Proofs.IRGeneration.ImportedCreationPacking
