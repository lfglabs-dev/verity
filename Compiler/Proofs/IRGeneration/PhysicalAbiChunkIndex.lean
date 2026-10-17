import Compiler.Proofs.IRGeneration.PhysicalAbiChunkStores

/-! Logical byte positions of the actual compiler's 32-byte chunks. -/
namespace Compiler.Proofs.IRGeneration.PhysicalAbiChunkIndex
open Compiler.CompilationModel

theorem chunk_count (bytes : List UInt8) :
    (chunkBytes32 bytes).length = (bytes.length + 31) / 32 := by
  cases bytes with
  | nil => simp [chunkBytes32]
  | cons byte rest =>
      rw [chunkBytes32]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.length_cons]
      rw [chunk_count ((byte :: rest).drop 32)]
      simp only [List.length_drop, List.length_cons]
      omega
termination_by bytes.length
decreasing_by
  simp_wf
  omega

theorem chunk_get (bytes : List UInt8) (index : Nat)
    (present : index < (chunkBytes32 bytes).length) :
    (chunkBytes32 bytes)[index] = (bytes.drop (32 * index)).take 32 := by
  induction index generalizing bytes with
  | zero =>
      cases bytes with
      | nil => simp [chunkBytes32] at present
      | cons byte rest =>
          have shape : chunkBytes32 (byte :: rest) =
              (byte :: rest).take 32 :: chunkBytes32 ((byte :: rest).drop 32) := by
            rw [chunkBytes32]
            rfl
          simp only [shape, List.getElem_cons_zero, Nat.mul_zero, List.drop_zero]
  | succ index ih =>
      cases bytes with
      | nil => simp [chunkBytes32] at present
      | cons byte rest =>
          have shape : chunkBytes32 (byte :: rest) =
              (byte :: rest).take 32 :: chunkBytes32 ((byte :: rest).drop 32) := by
            rw [chunkBytes32]
            rfl
          have tailPresent : index < (chunkBytes32 ((byte :: rest).drop 32)).length := by
            simpa only [shape, List.length_cons, Nat.succ_lt_succ_iff] using present
          simp only [shape, List.getElem_cons_succ]
          rw [ih _ tailPresent, List.drop_drop]
          congr 2
          omega

/-- Chunk-byte indexing is exactly the original UTF-8 byte indexing. -/
theorem chunk_original_byte (bytes : List UInt8) (chunkIndex : Nat)
    (present : chunkIndex < (chunkBytes32 bytes).length)
    (byteIndex : Nat) (bytePresent : byteIndex < ((chunkBytes32 bytes)[chunkIndex]).length) :
    ((chunkBytes32 bytes)[chunkIndex])[byteIndex] = bytes[32 * chunkIndex + byteIndex]'(by
      rw [chunk_get bytes chunkIndex present] at bytePresent
      simp only [List.length_take, List.length_drop] at bytePresent
      omega) := by
  simp only [chunk_get bytes chunkIndex present, List.getElem_take, List.getElem_drop]

/-- Arbitrary original bytes survive the complete sequence of physical
chunk stores, at their exact logical byte index. -/
theorem read_original (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < bytes.length) :
    (PhysicalRevertWrites.applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).byteMemory.readByte
      (base + query) = PhysicalAbiWordRecovery.toByte bytes[query] := by
  have chunkPresent : query / 32 < (chunkBytes32 bytes).length := by
    rw [chunk_count]
    omega
  have bytePresent : query % 32 < ((chunkBytes32 bytes)[query / 32]).length := by
    rw [chunk_get bytes (query / 32) chunkPresent]
    simp only [List.length_take, List.length_drop]
    omega
  have bounded : ∀ chunk ∈ chunkBytes32 bytes, chunk.length ≤ 32 :=
    fun _ member => PhysicalAbiBytes.chunk_length_le member
  have result := PhysicalAbiChunkStores.read_chunk state base (chunkBytes32 bytes)
    bounded extent (query / 32) chunkPresent ⟨query % 32, Nat.mod_lt _ (by decide)⟩
  have position : base + 32 * (query / 32) + query % 32 = base + query := by omega
  simp only [position, PhysicalAbiWordRecovery.paddedWord,
    PhysicalAbiWordRecovery.paddedBytes, List.getElem_append_left bytePresent] at result
  rw [chunk_original_byte bytes (query / 32) chunkPresent (query % 32) bytePresent] at result
  simpa only [show 32 * (query / 32) + query % 32 = query by omega] using result

/-- Every trailing ABI padding byte is actually zero in physical memory. -/
theorem read_padding (state : IRState) (base : Nat) (bytes : List UInt8)
    (extent : base + 32 * (chunkBytes32 bytes).length ≤ Verity.Core.Uint256.modulus)
    (query : Nat) (padding : bytes.length ≤ query)
    (present : query < 32 * (chunkBytes32 bytes).length) :
    (PhysicalRevertWrites.applyStores state
      (PhysicalAbiChunkStores.chunkWrites base (chunkBytes32 bytes))).byteMemory.readByte
      (base + query) = Compiler.CompilationModel.DenoteMemory.zeroByte := by
  have chunkPresent : query / 32 < (chunkBytes32 bytes).length := by omega
  have bytePadding : ((chunkBytes32 bytes)[query / 32]).length ≤ query % 32 := by
    rw [chunk_get bytes (query / 32) chunkPresent]
    simp only [List.length_take, List.length_drop]
    omega
  have bounded : ∀ chunk ∈ chunkBytes32 bytes, chunk.length ≤ 32 :=
    fun _ member => PhysicalAbiBytes.chunk_length_le member
  have result := PhysicalAbiChunkStores.read_chunk state base (chunkBytes32 bytes)
    bounded extent (query / 32) chunkPresent ⟨query % 32, Nat.mod_lt _ (by decide)⟩
  have position : base + 32 * (query / 32) + query % 32 = base + query := by omega
  simp only [position, PhysicalAbiWordRecovery.paddedWord,
    PhysicalAbiWordRecovery.paddedBytes, List.getElem_append_right bytePadding,
    List.getElem_replicate] at result
  exact result

end Compiler.Proofs.IRGeneration.PhysicalAbiChunkIndex
