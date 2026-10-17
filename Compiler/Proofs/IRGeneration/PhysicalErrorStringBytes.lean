import Compiler.Proofs.IRGeneration.PhysicalAbiWordBytes

namespace Compiler.Proofs.IRGeneration.PhysicalErrorStringBytes
open Compiler.CompilationModel DenoteMemory PhysicalRevertWrites

private theorem selector_encoding (index : Fin 4) :
    UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat Compiler.Constants.errorStringSelectorWord))
      ⟨index.val, by have := index.isLt; omega⟩).val =
      ([0x08, 0xc3, 0x79, 0xa0] : List UInt8)[index.val] := by
  have bound := index.isLt
  rcases index with ⟨index, bound⟩
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel +revert

theorem wordBytes_length (value : Nat) : (Denote.wordBytes value).length = 32 := by
  simp only [Denote.wordBytes, List.length_map, List.length_range]

theorem padding_extent (length : Nat) :
    length + ((32 - length % 32) % 32) = (length + 31) / 32 * 32 := by omega

/-- Exact payload extent, including UTF-8 length and final zero padding. -/
theorem payload_length (message : String) :
    (Denote.errorStringBytes message).length =
      68 + ((bytesFromString message).length + 31) / 32 * 32 := by
  simp only [Denote.errorStringBytes, List.length_append, List.length_cons,
    List.length_nil, wordBytes_length, List.length_replicate]
  change 4 + 32 + 32 + (bytesFromString message).length +
    ((32 - (bytesFromString message).length % 32) % 32) = _
  have padded := padding_extent (bytesFromString message).length
  omega

/-- Complete physical payload data region equals the original message byte. -/
theorem full_original_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (bytesFromString message).length) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      (68 + query) = PhysicalAbiWordRecovery.toByte (bytesFromString message)[query] := by
  change (applyStores state
    (PhysicalErrorStringHeader.headerWrites (bytesFromString message).length ++
      PhysicalErrorStringExecution.dataWrites message)).byteMemory.readByte _ = _
  rw [applyStores_append, PhysicalAbiChunkStores.dataWrites_eq]
  exact PhysicalAbiChunkIndex.read_original _ 68 _ extent query present

theorem full_padding_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (padding : (bytesFromString message).length ≤ query)
    (present : query < 32 * (chunkBytes32 (bytesFromString message)).length) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      (68 + query) = zeroByte := by
  change (applyStores state
    (PhysicalErrorStringHeader.headerWrites (bytesFromString message).length ++
      PhysicalErrorStringExecution.dataWrites message)).byteMemory.readByte _ = _
  rw [applyStores_append, PhysicalAbiChunkStores.dataWrites_eq]
  exact PhysicalAbiChunkIndex.read_padding _ 68 _ extent query padding present

private theorem payload_selector_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length)
    (selector : query < 4) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  have observed := PhysicalErrorStringHeader.full_selector_byte state message extent ⟨query, selector⟩
  rw [observed, selector_encoding]
  simp only [Denote.errorStringBytes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, wordBytes_length]
  simp only [show query < 4 + 32 + 32 + message.toUTF8.data.toList.length by omega,
    show query < 4 + 32 + 32 by omega, show query < 4 + 32 by omega, selector, dif_pos]

private theorem payload_offset_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length)
    (selector : ¬ query < 4) (offset : query < 36) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  have observed := PhysicalErrorStringHeader.full_offset_byte state message extent
    ⟨query - 4, by omega⟩
  have position : 4 + (query - 4) = query := by omega
  rw [position] at observed
  rw [observed, PhysicalAbiWordBytes.byte_encoding 32 (by decide)]
  simp only [Denote.errorStringBytes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, wordBytes_length]
  simp only [show query < 4 + 32 + 32 + message.toUTF8.data.toList.length by omega,
    show query < 4 + 32 + 32 by omega, show query < 4 + 32 by omega, selector,
    dif_pos, Denote.wordBytes, List.getElem_map, List.getElem_range]
  simp

private theorem payload_length_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length)
    (lengthWord : query < 68) (offset : ¬ query < 36) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  have lengthBound : (bytesFromString message).length < Verity.Core.Uint256.modulus := by
    rw [PhysicalAbiChunkIndex.chunk_count] at extent
    omega
  have observed := PhysicalErrorStringHeader.full_length_byte state message extent
    ⟨query - 36, by omega⟩
  have position : 36 + (query - 36) = query := by omega
  rw [position] at observed
  rw [observed, PhysicalAbiWordBytes.byte_encoding _ lengthBound]
  simp only [Denote.errorStringBytes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, wordBytes_length]
  simp only [show query < 4 + 32 + 32 + message.toUTF8.data.toList.length by omega,
    show query < 4 + 32 + 32 by omega, show ¬ query < 4 + 32 by omega,
    dif_pos, Denote.wordBytes, List.getElem_map, List.getElem_range]
  rfl

private theorem payload_original_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length)
    (lengthWord : ¬ query < 68)
    (original : query - 68 < (bytesFromString message).length) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  have observed := full_original_byte state message extent (query - 68) original
  have position : 68 + (query - 68) = query := by omega
  rw [position] at observed
  rw [observed]
  simp only [PhysicalAbiWordRecovery.toByte, UInt8.ofNat_toNat]
  simp only [Denote.errorStringBytes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, wordBytes_length]
  simp only [show query < 4 + 32 + 32 + message.toUTF8.data.toList.length by
    change query < 68 + (bytesFromString message).length; omega,
    show ¬ query < 4 + 32 + 32 by omega, dif_pos]
  simp [bytesFromString]

private theorem payload_padding_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length)
    (lengthWord : ¬ query < 68)
    (original : ¬ query - 68 < (bytesFromString message).length) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  have queryBound : query - 68 < 32 * (chunkBytes32 (bytesFromString message)).length := by
    rw [payload_length] at present
    rw [PhysicalAbiChunkIndex.chunk_count]
    omega
  have observed := full_padding_byte state message extent (query - 68) (by omega) queryBound
  have position : 68 + (query - 68) = query := by omega
  rw [position] at observed
  rw [observed]
  simp only [zeroByte]
  simp only [Denote.errorStringBytes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, wordBytes_length]
  simp only [show ¬ query < 4 + 32 + 32 + message.toUTF8.data.toList.length by
    change ¬ query < 68 + (bytesFromString message).length; omega,
    List.getElem_replicate]
  rfl

theorem payload_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (present : query < (Denote.errorStringBytes message).length) :
    UInt8.ofNat ((applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte
      query).val = (Denote.errorStringBytes message)[query] := by
  by_cases selector : query < 4
  · exact payload_selector_byte state message extent query present selector
  · by_cases offset : query < 36
    · exact payload_offset_byte state message extent query present selector offset
    · by_cases lengthWord : query < 68
      · exact payload_length_byte state message extent query present lengthWord offset
      · by_cases original : query - 68 < (bytesFromString message).length
        · exact payload_original_byte state message extent query present lengthWord original
        · exact payload_padding_byte state message extent query present lengthWord original

/-- Exact complete ABI revert bytes from the compiler's actual physical stores. -/
theorem observed_payload (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ((applyStores state (PhysicalErrorStringExecution.writes message)).captureRevert 0
      (68 + ((bytesFromString message).length + 31) / 32 * 32)).revertBytes =
      some (Denote.errorStringBytes message) := by
  rw [IRRevertObservation.capture_bytes]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, payload_length]
  · intro query left right
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    exact payload_byte state message extent query right

/-- With sufficient fuel, actual compiler execution produces the complete
Source ABI payload; an out-of-fuel revert is not given a byte certificate. -/
theorem execute_payload (state : IRState) (message : String) (fuel : Nat)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts ((PhysicalErrorStringExecution.writes message).length + fuel + 2)
        state (revertWithMessage message) = .revert finalState ∧
      finalState.revertBytes = some (Denote.errorStringBytes message) := by
  refine ⟨_, PhysicalErrorStringExecution.execute message state fuel, ?_⟩
  exact observed_payload state message extent

end Compiler.Proofs.IRGeneration.PhysicalErrorStringBytes
