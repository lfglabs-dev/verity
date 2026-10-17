import Compiler.Proofs.IRGeneration.ImportedAbiWordCopy

namespace Compiler.Proofs.IRGeneration.ImportedAbiWords
open Compiler.CompilationModel DenoteMemory PhysicalMemory

/-- Sequential word copies read each word at its actual execution point. -/
def copyWords (world : Verity.ContractState) (source destination : Nat) : Nat → Verity.ContractState
  | 0 => world
  | count + 1 => let before := copyWords world source destination count
    before.copyPhysicalBytes before.physicalByte (destination + 32 * count) (source + 32 * count) 32

/-- All bytes outside the complete destination interval are preserved. -/
theorem frame (world : Verity.ContractState) (source destination count query : Nat)
    (outside : query < destination ∨ destination + 32 * count ≤ query) :
    (copyWords world source destination count).physicalByte query = world.physicalByte query := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [copyWords, Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (by omega)]
      exact ih (by omega)

/-- Separation of the complete regions derives original-source snapshot bytes
for arbitrarily many real sequential word copies. No output equality is assumed. -/
theorem copied (world : Verity.ContractState) (source destination count : Nat)
    (separate : source + 32 * count ≤ destination ∨ destination + 32 * count ≤ source)
    (offset : Fin (32 * count)) :
    (copyWords world source destination count).physicalByte (destination + offset.val) =
      world.physicalByte (source + offset.val) := by
  induction count with
  | zero => exact Fin.elim0 offset
  | succ count ih =>
      have size := offset.isLt
      have smaller : source + 32 * count ≤ destination ∨ destination + 32 * count ≤ source := by omega
      by_cases previous : offset.val < 32 * count
      · rw [copyWords, Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (Or.inl (by omega))]
        exact ih smaller ⟨offset.val, previous⟩
      · have lane : offset.val - 32 * count < 32 := by omega
        have target : destination + offset.val = destination + 32 * count + (offset.val - 32 * count) := by omega
        have origin : source + 32 * count + (offset.val - 32 * count) = source + offset.val := by omega
        rw [copyWords, target, Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ ⟨_, lane⟩, origin]
        exact frame world source destination count (source + offset.val) (by omega)

/-- Physical word coherence is retained, including the zero-copy case. -/
theorem coherent (world : Verity.ContractState) (source destination count : Nat)
    (initial : Coherent world) : Coherent (copyWords world source destination count) := by
  cases count with
  | zero => exact initial
  | succ count => exact copyPhysicalMemory_coherent _ _ _ _ _

end Compiler.Proofs.IRGeneration.ImportedAbiWords
