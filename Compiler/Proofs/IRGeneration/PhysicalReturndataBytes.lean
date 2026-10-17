import Compiler.Proofs.IRGeneration.PhysicalCopyRevert
import Compiler.Proofs.IRGeneration.PhysicalAbiWordBytes

namespace Compiler.Proofs.IRGeneration.PhysicalReturndataBytes
open Compiler.CompilationModel DenoteMemory

/-- The whole-word physical source has the Source ABI encoding for every
natural-number word, since both retain exactly the low 256 bits. -/
theorem buffer_encoding_unbounded (words : List Nat) :
    (List.range (32 * words.length)).map (fun index =>
      UInt8.ofNat (wordListByte words index).val) =
      words.flatMap Denote.wordBytes := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    have extent : 32 * (word :: words).length = 32 + 32 * words.length := by
      simp [Nat.mul_add, Nat.add_comm]
    rw [extent, List.range_add, List.map_append, List.map_map, List.flatMap_cons]
    congr 1
    · apply List.map_congr_left
      intro index member
      have bound : index < 32 := List.mem_range.mp member
      have quotient : index / 32 = 0 := Nat.div_eq_of_lt bound
      have remainder : index % 32 = index := Nat.mod_eq_of_lt bound
      simp only [wordListByte, quotient, List.getD_cons_zero, remainder]
      exact PhysicalAbiWordBytes.byte_encoding_unbounded word ⟨index, bound⟩
    · rw [← ih]
      apply List.map_congr_left
      intro index _
      have quotient : (32 + index) / 32 = index / 32 + 1 := by omega
      have remainder : (32 + index) % 32 = index % 32 := by omega
      simp only [Function.comp_apply, wordListByte, quotient, remainder, List.getD_cons_succ]

theorem captured_buffer_unbounded (state : IRState) :
    ((state.copyPhysicalReturndata 0 0 (32 * state.returndata.length)).captureRevert
      0 (32 * state.returndata.length)).revertBytes =
      some (state.returndata.flatMap Denote.wordBytes) := by
  rw [PhysicalCopyRevert.returndata_payload, buffer_encoding_unbounded state.returndata]

/-- Compatibility interface; no word bound is needed by the stronger law. -/
theorem buffer_encoding (words : List Nat)
    (_bounded : ∀ value ∈ words, value < Verity.Core.Uint256.modulus) :
    (List.range (32 * words.length)).map (fun index =>
      UInt8.ofNat (wordListByte words index).val) =
      words.flatMap Denote.wordBytes := buffer_encoding_unbounded words

theorem captured_buffer (state : IRState)
    (_bounded : ∀ value ∈ state.returndata, value < Verity.Core.Uint256.modulus) :
    ((state.copyPhysicalReturndata 0 0 (32 * state.returndata.length)).captureRevert
      0 (32 * state.returndata.length)).revertBytes =
      some (state.returndata.flatMap Denote.wordBytes) := captured_buffer_unbounded state

end Compiler.Proofs.IRGeneration.PhysicalReturndataBytes
