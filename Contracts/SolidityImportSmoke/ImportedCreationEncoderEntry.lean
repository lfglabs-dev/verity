import Contracts.SolidityImportSmoke.ImportedCreationDecodedPrefix
import Contracts.SolidityImportSmoke.ImportedCreationEncodedPacking

namespace Contracts.SolidityImportSmoke.ImportedCreationEncoderEntry
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationDecodedPrefix

def head (state : DenoteState) := free state + count state * 128

theorem held (oracle : DenoteOracle) (state : DenoteState) :
    lookupValue (completed oracle state).bindings "_verity_slice_tmp_0_memory" = 128 := by
  rw [completed, binding_frame oracle _ _ (by decide) (by decide)]
  exact (ImportedCreationDecodedMarket.prefix_bindings state).2

theorem array_pointer (oracle : DenoteOracle) (state : DenoteState) :
    ImportedCreationArrayDescriptors.pointer (completed oracle state) 128 = 384 := by
  unfold ImportedCreationArrayDescriptors.pointer
  rw [completed, (memory_frame oracle _).2, ImportedCreationDecodedMarket.prefix_array_pointer]
  decide

theorem array_count (oracle : DenoteOracle) (state : DenoteState)
    (budget : head state ≤ 2^64 - 1) :
    ImportedCreationArrayDescriptors.count (completed oracle state) 128 = count state := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have bound : count state < Verity.Core.Uint256.modulus := by
    unfold head at budget
    have geometry : free state = 384 + 32 * (count state + 1) := rfl
    rw [geometry] at budget
    omega
  unfold ImportedCreationArrayDescriptors.count
  rw [array_pointer, completed, (memory_frame oracle _).2, ImportedCreationDecodedMarket.prefix_count_word,
    Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bound]

theorem aligned (state : DenoteState) : head state % 32 = 0 := by
  unfold head
  have geometry : free state = 384 + 32 * (count state + 1) := rfl
  rw [geometry]
  omega

theorem before (state : DenoteState) : 128 + 256 ≤ head state := by
  unfold head
  have geometry : free state = 384 + 32 * (count state + 1) := rfl
  rw [geometry]
  omega

theorem array_before (state : DenoteState) : 384 + 32 + 32 * count state ≤ head state := by
  unfold head
  have geometry : free state = 384 + 32 * (count state + 1) := rfl
  rw [geometry]
  omega

theorem source_at (oracle : DenoteOracle) (state : DenoteState) (index : Nat)
    (live : index < count state) (budget : head state ≤ 2^64 - 1) :
    ImportedAbiArray.sourceAt (completed oracle state).world 416 index = free state + index * 128 := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have bound : free state + index * 128 < Verity.Core.Uint256.modulus := by
    unfold head at budget
    omega
  unfold ImportedAbiArray.sourceAt
  rw [completed, (memory_frame oracle _).2,
    ImportedCreationDecodedMarket.prefix_array_word _ _ (by omega)]
  rw [Nat.mul_comm 32 index, ImportedCreationDecodedArray.pointer_cell state index live,
    Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bound]

theorem source_bounds (state : DenoteState) (index : Nat) (live : index < count state) :
    96 ≤ free state + index * 128 ∧ free state + index * 128 + 128 ≤ head state := by
  unfold head
  have geometry : free state = 384 + 32 * (count state + 1) := rfl
  rw [geometry]
  constructor <;> omega

/-- All encoder geometry comes from the actual original-transaction decoder. -/
theorem execute_encoder (oracle : DenoteOracle) (state : DenoteState)
    (budget : head state + (320 + 128 * count state) + 32 +
      32 * ((11 + (320 + 128 * count state) + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle actualFields (completed oracle state)
        ImportedCreationEncodedPacking.segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world
        (head state + (320 + 128 * count state) + 32) (11 + (320 + 128 * count state)) =
        ImportedCreationHeaderAllocation.prefixBytes ++
          ImportedCreationAbiLayout.abiBytes (completed oracle state) 128 := by
  have small : head state ≤ 2^64 - 1 := by omega
  have size : ImportedCreationAbiLayout.payloadSize (completed oracle state) 128 =
      320 + 128 * count state := by
    unfold ImportedCreationAbiLayout.payloadSize
    rw [array_count oracle state small]
  have run := ImportedCreationEncodedPacking.execute oracle actualFields (completed oracle state)
    128 (head state) (coherent oracle state) (pointer oracle state small) (held oracle state)
    (by decide) (before state) (aligned state)
    (by rw [array_pointer]; decide)
    (by rw [array_pointer, array_count oracle state small]; exact array_before state)
    (by
      rw [array_count oracle state small, array_pointer]
      intro i live
      rw [show 384 + 32 = 416 by decide, source_at oracle state i live small]
      exact source_bounds state i live)
    (by rw [size]; exact budget)
  simpa only [size] using run

end Contracts.SolidityImportSmoke.ImportedCreationEncoderEntry

