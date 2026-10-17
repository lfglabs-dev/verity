import Compiler.Proofs.IRGeneration.PhysicalErrorStringHeader

namespace Compiler.Proofs.IRGeneration.PhysicalErrorStringWords
open Compiler.CompilationModel DenoteMemory PhysicalPayloadStores

private theorem applyStores_coherent (state : IRState) (writes : List (Nat × Nat))
    (coherent : ∀ query, state.memory query = (wordValue (state.byteMemory.readWord query)).val) :
    ∀ query, (applyStores state writes).memory query =
      (wordValue ((applyStores state writes).byteMemory.readWord query)).val := by
  induction writes generalizing state with
  | nil => exact coherent
  | cons pair tail ih => exact ih _ (fun _ => rfl)

theorem full_coherent (state : IRState) (message : String) :
    ∀ query, (applyStores state (PhysicalErrorStringExecution.writes message)).memory query =
      (wordValue ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readWord query)).val := by
  simp only [PhysicalErrorStringExecution.writes, List.cons_append,
    List.nil_append, applyStores]
  exact applyStores_coherent _ _ (fun _ => rfl)

private theorem selector_tail_agrees :
    ∀ (index : Fin 32) (lower : 4 ≤ index.val),
      (valueWord (Verity.Core.Uint256.ofNat 32))
        ⟨index.val - 4, by have := index.isLt; omega⟩ =
      (valueWord (Verity.Core.Uint256.ofNat Compiler.Constants.errorStringSelectorWord)) index := by
  decide +kernel

theorem selector_word (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).memory 0 =
      Compiler.Constants.errorStringSelectorWord := by
  rw [full_coherent]
  have word : (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readWord 0 =
      valueWord (Verity.Core.Uint256.ofNat Compiler.Constants.errorStringSelectorWord) := by
    funext index
    change (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      (0 + index.val) = _
    simp only [Nat.zero_add]
    by_cases small : index.val < 4
    · exact PhysicalErrorStringHeader.full_selector_byte state message extent ⟨index.val, small⟩
    · have lower : 4 ≤ index.val := by omega
      have location : index.val = 4 + (index.val - 4) := by omega
      rw [location, PhysicalErrorStringHeader.full_offset_byte state message extent
        ⟨index.val - 4, by have := index.isLt; omega⟩]
      exact selector_tail_agrees index lower
  rw [word, wordValue_valueWord]
  decide +kernel

theorem offset_word (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).memory 4 = 32 := by
  rw [full_coherent]
  have word : (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readWord 4 =
      valueWord (Verity.Core.Uint256.ofNat 32) := by
    funext index
    exact PhysicalErrorStringHeader.full_offset_byte state message extent index
  rw [word, wordValue_valueWord]
  rfl

theorem length_word (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).memory 36 =
      (bytesFromString message).length := by
  rw [full_coherent]
  have word : (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readWord 36 =
      valueWord (Verity.Core.Uint256.ofNat (bytesFromString message).length) := by
    funext index
    exact PhysicalErrorStringHeader.full_length_byte state message extent index
  rw [word, wordValue_valueWord, Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  have chunks := PhysicalAbiChunkIndex.chunk_count (bytesFromString message)
  omega

end Compiler.Proofs.IRGeneration.PhysicalErrorStringWords
