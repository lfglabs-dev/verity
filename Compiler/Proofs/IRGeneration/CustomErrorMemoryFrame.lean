import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorDomain
import Compiler.Proofs.IRGeneration.IRMemoryCoherence

namespace Compiler.Proofs.IRGeneration.CustomErrorMemoryFrame
open Compiler.CompilationModel DenoteMemory IRMemoryCoherence

/-- A disjoint copy preserves the legacy word only from a coherent initial
carrier. Zero-length copies preserve the state without any coherence premise. -/
theorem word_outside_copy (state : IRState) (source : Nat → Byte)
    (dst src size query : Nat) (coherent : Coherent state)
    (outside : query + 32 ≤ dst ∨ dst + size ≤ query) :
    (state.copyPhysicalBytes source dst src size).memory query = state.memory query := by
  by_cases zero : size = 0
  · simp only [zero, IRState.copyPhysicalBytes_zero]
  · simp only [IRState.copyPhysicalBytes, zero, if_false]
    change (wordValue ((state.byteMemory.copyFrom source dst src size).readWord query)).val = _
    have initial := coherent
    unfold Coherent at initial
    rw [Memory.readWord_copyFrom_outside _ _ _ _ _ _ outside, ← initial query]

theorem domain_store (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (offset value : Nat) (domain : CustomErrorDomain spec runtime state)
    (coherent : Coherent state)
    (outside : freeMemoryPointer + 32 ≤ offset ∨ offset + 32 ≤ freeMemoryPointer) :
    CustomErrorDomain spec runtime (state.writePhysicalMemoryValue offset value) := by
  refine ⟨domain.declarations, ?_⟩
  intro definition member
  rw [word_outside_store state offset value freeMemoryPointer coherent outside]
  exact domain.extents definition member

/-- A zero-byte copy is the identity even for a legacy incoherent carrier.
No disjointness or physical coherence is needed for this case. -/
theorem domain_copy_zero (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (source : Nat → Byte) (dst src : Nat)
    (domain : CustomErrorDomain spec runtime state) :
    CustomErrorDomain spec runtime (state.copyPhysicalBytes source dst src 0) := by
  simpa only [IRState.copyPhysicalBytes_zero] using domain

theorem domain_copy (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (source : Nat → Byte) (dst src size : Nat)
    (domain : CustomErrorDomain spec runtime state) (coherent : Coherent state)
    (outside : freeMemoryPointer + 32 ≤ dst ∨ dst + size ≤ freeMemoryPointer) :
    CustomErrorDomain spec runtime (state.copyPhysicalBytes source dst src size) := by
  refine ⟨domain.declarations, ?_⟩
  intro definition member
  rw [word_outside_copy state source dst src size freeMemoryPointer coherent outside]
  exact domain.extents definition member

/-- Allocating scratch memory requires checking the new physical pointer,
including the signature extent. This does not claim arbitrary pointer writes
preserve the previous bound. -/
theorem domain_pointer_update (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (pointer : Nat) (domain : CustomErrorDomain spec runtime state)
    (fits : ∀ definition ∈ spec.errors,
      (Verity.Core.Uint256.ofNat pointer).val +
        32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
          Verity.Core.Uint256.modulus) :
    CustomErrorDomain spec runtime (state.writePhysicalMemoryValue freeMemoryPointer pointer) := by
  refine ⟨domain.declarations, ?_⟩
  intro definition member
  rw [IRState.writePhysicalMemoryValue_at]
  exact fits definition member

end Compiler.Proofs.IRGeneration.CustomErrorMemoryFrame
