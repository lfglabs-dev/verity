import Compiler.Proofs.IRGeneration.PhysicalAbiChunkIndex
import Compiler.Proofs.IRGeneration.SourceCustomErrorBytes

namespace Compiler.Proofs.IRGeneration.PhysicalSignatureHash
open Compiler.CompilationModel DenoteMemory PhysicalRevertWrites

private def signatureWord (bytes : List UInt8) (offset : Nat) : Word :=
  fun index => PhysicalAbiWordRecovery.toByte ((bytes[offset + index.val]?).getD 0)

private theorem signatureWord_value (bytes : List UInt8) (offset : Nat) :
    wordValue (signatureWord bytes offset) = Denote.signatureMemory bytes offset := by
  have digits : List.ofFn (signatureWord bytes offset) =
      (List.range 32).map (fun index => PhysicalAbiWordRecovery.toByte
        ((bytes[offset + index]?).getD 0)) := by
    apply List.ext_getElem
    · simp
    · intro index left right
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, signatureWord]
  simp only [wordValue, digits, List.foldl_map, Denote.signatureMemory,
    PhysicalAbiWordRecovery.toByte]

private theorem stores_preserve_coherence (state : IRState) (writes : List (Nat × Nat))
    (coherent : ∀ query, state.memory query = (wordValue (state.byteMemory.readWord query)).val) :
    ∀ query, (applyStores state writes).memory query =
      (wordValue ((applyStores state writes).byteMemory.readWord query)).val := by
  induction writes generalizing state with
  | nil => exact coherent
  | cons pair tail ih => exact ih _ (fun _ => rfl)

/-- Each physical signature word is the Source encoder's corresponding word,
including the last word's zero padding, from arbitrary initial memory. -/
theorem signature_word (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (index : Nat) (present : index < (chunkBytes32 bytes).length) :
    (applyStores state (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).memory
      (base + 32 * index) = (Denote.signatureMemory bytes (32 * index)).val := by
  have coherent : ∀ query,
      (applyStores state (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).memory query =
        (wordValue ((applyStores state (PhysicalAbiChunkStores.chunkWrites base
          (chunkBytes32 bytes))).byteMemory.readWord query)).val := by
    cases chunks : chunkBytes32 bytes with
    | nil => simp [chunks] at present
    | cons head tail =>
        simp only [PhysicalAbiChunkStores.chunkWrites, applyStores]
        exact stores_preserve_coherence _ _ (fun _ => rfl)
  rw [coherent]
  have word : (applyStores state (PhysicalAbiChunkStores.chunkWrites base
      (chunkBytes32 bytes))).byteMemory.readWord (base + 32 * index) =
      signatureWord bytes (32 * index) := by
    funext byte
    change (applyStores state (PhysicalAbiChunkStores.chunkWrites base
      (chunkBytes32 bytes))).byteMemory.readByte (base + 32 * index + byte.val) = _
    by_cases original : 32 * index + byte.val < bytes.length
    · have stored := PhysicalAbiChunkIndex.read_original state base bytes extent
        (32 * index + byte.val) original
      simpa only [signatureWord, List.getElem?_eq_getElem original, Option.getD_some,
        Nat.add_assoc] using stored
    · have allocated : 32 * index + byte.val < 32 * (chunkBytes32 bytes).length := by
        have bound := byte.isLt
        omega
      have stored := PhysicalAbiChunkIndex.read_padding state base bytes extent
        (32 * index + byte.val) (by omega) allocated
      have absent : bytes[32 * index + byte.val]? = none := List.getElem?_eq_none (by omega)
      have zero : PhysicalAbiWordRecovery.toByte (0 : UInt8) = zeroByte := by decide
      simpa only [signatureWord, absent, Option.getD_none, zero, Nat.add_assoc] using stored
  rw [word, signatureWord_value]

theorem signature_words (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus) :
    memorySliceWords (applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).memory base bytes.length =
      memorySliceWords (fun address => (Denote.signatureMemory bytes address).val) 0 bytes.length := by
  unfold memorySliceWords
  apply List.map_congr_left
  intro index member
  have present : index < (chunkBytes32 bytes).length := by
    rw [PhysicalAbiChunkIndex.chunk_count]
    exact List.mem_range.mp member
  have address256 : base + 32 * index < Verity.Core.Uint256.modulus := by omega
  have logical256 : 32 * index < Verity.Core.Uint256.modulus := by omega
  have address : base + 32 * index < Compiler.Constants.evmModulus := address256
  have logical : 32 * index < Compiler.Constants.evmModulus := logical256
  simp only [Nat.zero_add, Nat.mul_comm index 32,
    Nat.mod_eq_of_lt address, Nat.mod_eq_of_lt logical]
  exact signature_word state base bytes extent index present

/-- Relocating the actual signature stores preserves the exact hash input,
so the actual hash computation equals Source's signature-memory computation. -/
theorem hash_eq (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus) :
    abstractKeccakMemorySlice (applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).memory base bytes.length =
      SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length := by
  unfold abstractKeccakMemorySlice SourceSemantics.keccakMemorySlice irMemorySliceBytesBE
  rw [signature_words state base bytes extent]
  rfl

end Compiler.Proofs.IRGeneration.PhysicalSignatureHash
