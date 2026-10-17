import Compiler.Proofs.IRGeneration.PhysicalAbiWordBytes

namespace Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarBytes
open Compiler.CompilationModel DenoteMemory PhysicalRevertWrites

def selectorWord (hash : Nat) : Nat := hash / 2^224 * 2^224
def writes (hash value : Nat) : List (Nat × Nat) := [(0, selectorWord hash), (4, value)]

/-- Clearing the low 224 bits does not change the selector's four bytes. -/
theorem selector_byte (hash : Nat) (index : Fin 4) :
    UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat (selectorWord hash)))
      ⟨index.val, by have := index.isLt; omega⟩).val =
    UInt8.ofNat (hash / 2^(8*(31-index.val)) % 256) := by
  rw [PhysicalAbiWordBytes.byte_encoding_unbounded]
  have bound := index.isLt
  have exponent : 224 + 8 * (3 - index.val) = 8 * (31 - index.val) := by omega
  have factor : 2^(8*(31-index.val)) = 2^224 * 2^(8*(3-index.val)) := by
    rw [← Nat.pow_add, exponent]
  simp only [selectorWord, factor]
  rw [Nat.mul_comm (hash / 2^224) (2^224),
    Nat.mul_div_mul_left _ _ (by decide : 0 < 2^224)]
  rw [Nat.div_div_eq_div_mul]

theorem header_byte (state : IRState) (hash value : Nat) (index : Fin 4) :
    UInt8.ofNat ((applyStores state (writes hash value)).byteMemory.readByte index.val).val =
    UInt8.ofNat (hash / 2^(8*(31-index.val)) % 256) := by
  have outside : ∀ pair ∈ [(4, value)],
      (Verity.Core.Uint256.ofNat 0).val + index.val < (Verity.Core.Uint256.ofNat pair.1).val ∨
      (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤ (Verity.Core.Uint256.ofNat 0).val + index.val := by
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    left
    have bound := index.isLt
    change 0 + index.val < 4
    omega
  have written := applyStores_byte_written state 0 (selectorWord hash) [(4, value)]
    ⟨index.val, by have := index.isLt; omega⟩ outside
  change UInt8.ofNat ((applyStores state ((0, selectorWord hash) :: [(4, value)])).byteMemory.readByte index.val).val = _
  have zero : (Verity.Core.Uint256.ofNat 0).val = 0 := by decide
  simp only [zero, Nat.zero_add] at written
  rw [written]
  exact selector_byte hash index

theorem argument_byte (state : IRState) (hash value : Nat) (index : Fin 32) :
    UInt8.ofNat ((applyStores state (writes hash value)).byteMemory.readByte (4 + index.val)).val =
    UInt8.ofNat (value / 2^(8*(31-index.val)) % 256) := by
  have written := Memory.readByte_writeWord_at
    (state.writePhysicalMemoryValue 0 (selectorWord hash)).byteMemory 4
    (valueWord (Verity.Core.Uint256.ofNat value)) index
  change UInt8.ofNat (((state.writePhysicalMemoryValue 0 (selectorWord hash)).writePhysicalMemoryValue
    4 value).byteMemory.readByte (4 + index.val)).val = _
  rw [show ((state.writePhysicalMemoryValue 0 (selectorWord hash)).writePhysicalMemoryValue 4 value).byteMemory =
    (state.writePhysicalMemoryValue 0 (selectorWord hash)).byteMemory.writeWord 4
      (valueWord (Verity.Core.Uint256.ofNat value)) by rfl, written]
  exact PhysicalAbiWordBytes.byte_encoding_unbounded value index

theorem observed_payload (state : IRState) (hash value : Nat) :
    ((applyStores state (writes hash value)).captureRevert 0 36).revertBytes =
      some ((Denote.wordBytes hash).take 4 ++ Denote.wordBytes value) := by
  rw [IRRevertObservation.capture_bytes]
  congr 1
  apply List.ext_getElem
  · simp [Denote.wordBytes]
  · intro index left right
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    have length : (Denote.wordBytes hash).length = 32 := by simp [Denote.wordBytes]
    have prefixLength : ((Denote.wordBytes hash).take 4).length = 4 := by simp [length]
    by_cases header : index < 4
    · rw [List.getElem_append_left (by simpa only [prefixLength] using header), List.getElem_take]
      simp only [Denote.wordBytes, List.getElem_map, List.getElem_range]
      exact header_byte state hash value ⟨index, header⟩
    · have argument : index - 4 < 32 := by
        have : index < 36 := by simpa using left
        omega
      rw [List.getElem_append_right (by simpa only [prefixLength] using (show 4 ≤ index by omega))]
      simp only [Denote.wordBytes, List.getElem_map, List.getElem_range]
      have location : index = 4 + (index - 4) := by omega
      conv_lhs => rw [location]
      exact argument_byte state hash value ⟨index - 4, argument⟩

/-- Physical stores and sufficient fuel prove every byte of the scalar error
tail. Selector-hash/argument evaluation in the compiler prefixLength is a separate
obligation, not an assumed oracle equality in this theorem. -/
theorem execute_payload (state : IRState) (hash value fuel : Nat) :
    ∃ final, execIRStmts ((writes hash value).length + fuel + 2) state
      (stores (writes hash value) ++ [.exprStmt (.call "revert" [.lit 0, .lit 36])]) =
      .revert final ∧ final.revertBytes =
        some ((Denote.wordBytes hash).take 4 ++ Denote.wordBytes value) := by
  exact ⟨_, exec_stores_revert _ state fuel 0 36, observed_payload state hash value⟩

theorem observed_zero_argument_payload (state : IRState) (hash : Nat) :
    ((state.writePhysicalMemoryValue 0 (selectorWord hash)).captureRevert 0 4).revertBytes =
      some ((Denote.wordBytes hash).take 4) := by
  rw [IRRevertObservation.capture_bytes]
  congr 1
  apply List.ext_getElem
  · simp [Denote.wordBytes]
  · intro index left right
    have bound : index < 4 := by simpa using left
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add, List.getElem_take,
      Denote.wordBytes]
    have written := Memory.readByte_writeWord_at state.byteMemory 0
      (valueWord (Verity.Core.Uint256.ofNat (selectorWord hash)))
      ⟨index, by omega⟩
    change UInt8.ofNat ((state.byteMemory.writeWord 0
      (valueWord (Verity.Core.Uint256.ofNat (selectorWord hash)))).readByte index).val = _
    simp only [Nat.zero_add] at written
    rw [written]
    exact selector_byte hash ⟨index, bound⟩

theorem execute_zero_argument_payload (state : IRState) (hash fuel : Nat) :
    ∃ final, execIRStmts (fuel + 3) state
      (stores [(0, selectorWord hash)] ++ [.exprStmt (.call "revert" [.lit 0, .lit 4])]) =
      .revert final ∧ final.revertBytes = some ((Denote.wordBytes hash).take 4) := by
  refine ⟨_, ?_, observed_zero_argument_payload state hash⟩
  have zero : (Verity.Core.Uint256.ofNat 0).val = 0 := by decide
  simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, applyStores, zero, Nat.reduceAdd] using
    exec_stores_revert [(0, selectorWord hash)] state fuel 0 4

end Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarBytes
