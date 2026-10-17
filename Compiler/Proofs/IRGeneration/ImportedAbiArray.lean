import Compiler.Proofs.IRGeneration.ImportedAbiWords

namespace Compiler.Proofs.IRGeneration.ImportedAbiArray
open Compiler.CompilationModel DenoteMemory PhysicalMemory

def sourceAt (world : Verity.ContractState) (base index : Nat) : Nat :=
  (world.memory (base + 32 * index)).val

/-- Original pointer-array words select structs; each iteration still reads its
four source words from the current physical world. -/
def copyElements (world : Verity.ContractState) (base destination : Nat) : Nat → Verity.ContractState
  | 0 => world
  | count + 1 => ImportedAbiWords.copyWords (copyElements world base destination count)
      (sourceAt world base count) (destination + 128 * count) 4

theorem coherent (world : Verity.ContractState) (base destination count : Nat)
    (initial : Coherent world) : Coherent (copyElements world base destination count) := by
  induction count with
  | zero => exact initial
  | succ count ih => exact ImportedAbiWords.coherent _ _ _ _ ih

/-- Every byte outside the total array destination is preserved. -/
theorem frame (world : Verity.ContractState) (base destination count query : Nat)
    (outside : query < destination ∨ destination + 128 * count ≤ query) :
    (copyElements world base destination count).physicalByte query = world.physicalByte query := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [copyElements, ImportedAbiWords.frame _ _ _ _ _ (by omega)]
      exact ih (by omega)

/-- Coherence turns a complete32-byte physical frame into an exact word frame. -/
theorem word_of_bytes (before after : Verity.ContractState) (query : Nat)
    (initial : Coherent before) (final : Coherent after)
    (bytes : ∀ offset : Fin 32, after.physicalByte (query + offset.val) =
      before.physicalByte (query + offset.val)) : after.memory query = before.memory query := by
  rw [final query, initial query]
  congr 1
  funext offset
  exact bytes offset

/-- All pointer-array words before the destination retain their original values. -/
theorem word_frame (world : Verity.ContractState) (base destination count query : Nat)
    (initial : Coherent world) (outside : query + 32 ≤ destination ∨ destination + 128 * count ≤ query) :
    (copyElements world base destination count).memory query = world.memory query := by
  apply word_of_bytes world _ query initial (coherent world base destination count initial)
  intro offset
  exact frame world base destination count (query + offset.val) (by have := offset.isLt; omega)

/-- Complete arbitrary-count array contents: each output element is the ORIGINAL
pointed-to struct snapshot, even when different elements share their source. -/
theorem element_bytes (world : Verity.ContractState) (base destination count : Nat)
    (sources : ∀ index < count, sourceAt world base index + 128 ≤ destination)
    (index : Fin count) (offset : Fin 128) :
    (copyElements world base destination count).physicalByte (destination + 128 * index.val + offset.val) =
      world.physicalByte (sourceAt world base index.val + offset.val) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have position := index.isLt
      have byte := offset.isLt
      have earlier : ∀ i < count, sourceAt world base i + 128 ≤ destination := fun i h => sources i (by omega)
      by_cases previous : index.val < count
      · rw [copyElements, ImportedAbiWords.frame _ _ _ _ _ (Or.inl (by omega))]
        exact ih earlier ⟨index.val, previous⟩
      · have last : index.val = count := by omega
        rw [last, copyElements, ImportedAbiWords.copied _ _ _ 4 (Or.inl (by have := sources count (by omega); omega)) offset]
        exact frame world base destination count (sourceAt world base count + offset.val)
          (Or.inl (by have := sources count (by omega); omega))

end Compiler.Proofs.IRGeneration.ImportedAbiArray
