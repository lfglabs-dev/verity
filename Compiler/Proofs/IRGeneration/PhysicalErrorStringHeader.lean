import Compiler.Proofs.IRGeneration.PhysicalAbiChunkIndex

/-! Exact byte observations of the overlapping Error(string) header stores. -/
namespace Compiler.Proofs.IRGeneration.PhysicalErrorStringHeader
open Compiler.CompilationModel PhysicalPayloadStores DenoteMemory

def headerWrites (length : Nat) : List (Nat × Nat) :=
  [(0, Compiler.Constants.errorStringSelectorWord), (4, 32), (36, length)]

private theorem zeroOffset : (Verity.Core.Uint256.ofNat 0).val = 0 := by decide
private theorem fourOffset : (Verity.Core.Uint256.ofNat 4).val = 4 := by decide
private theorem lengthOffset : (Verity.Core.Uint256.ofNat 36).val = 36 := by decide

theorem selector_byte (state : IRState) (length : Nat) (index : Fin 4) :
    (applyStores state (headerWrites length)).byteMemory.readByte index.val =
      valueWord (Verity.Core.Uint256.ofNat Compiler.Constants.errorStringSelectorWord)
        ⟨index.val, by have := index.isLt; omega⟩ := by
  have outside : ∀ pair ∈ [(4, 32), (36, length)],
      (Verity.Core.Uint256.ofNat 0).val + index.val <
        (Verity.Core.Uint256.ofNat pair.1).val ∨
      (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤
        (Verity.Core.Uint256.ofNat 0).val + index.val := by
    intro pair member
    simp at member
    rcases member with rfl | rfl <;>
      simp only [zeroOffset, fourOffset, lengthOffset, Nat.zero_add] <;>
      left <;> have := index.isLt <;> omega
  have result := applyStores_byte_written state 0 Compiler.Constants.errorStringSelectorWord [(4, 32), (36, length)]
    ⟨index.val, by have := index.isLt; omega⟩ outside
  simpa only [headerWrites, zeroOffset, Nat.zero_add] using result

theorem offset_byte (state : IRState) (length : Nat) (index : Fin 32) :
    (applyStores state (headerWrites length)).byteMemory.readByte (4 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat 32) index := by
  have outside : ∀ pair ∈ [(36, length)],
      (Verity.Core.Uint256.ofNat 4).val + index.val <
        (Verity.Core.Uint256.ofNat pair.1).val ∨
      (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤
        (Verity.Core.Uint256.ofNat 4).val + index.val := by
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    simp only [fourOffset, lengthOffset]
    left
    have := index.isLt
    omega
  have result := applyStores_byte_written
    (state.writePhysicalMemoryValue (Verity.Core.Uint256.ofNat 0).val
      Compiler.Constants.errorStringSelectorWord) 4 32 [(36, length)] index outside
  simpa only [headerWrites, applyStores, fourOffset] using result

theorem length_byte (state : IRState) (length : Nat) (index : Fin 32) :
    (applyStores state (headerWrites length)).byteMemory.readByte (36 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat length) index := by
  simp only [headerWrites, applyStores]
  have result := Memory.readByte_writeWord_at
    ((state.writePhysicalMemoryValue 0 Compiler.Constants.errorStringSelectorWord).writePhysicalMemoryValue 4 32).byteMemory 36
    (valueWord (Verity.Core.Uint256.ofNat length)) index
  simpa only [IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory,
    zeroOffset, fourOffset, lengthOffset] using result

/-- Data stores cannot overwrite any of the 68 header bytes. -/
theorem data_preserves_header (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (header : query < 68) :
    (applyStores state (PhysicalErrorStringExecution.dataWrites message)).byteMemory.readByte query =
      state.byteMemory.readByte query := by
  rw [PhysicalAbiChunkStores.dataWrites_eq]
  apply applyStores_byte_outside
  intro pair member
  have bounds := PhysicalAbiChunkStores.chunkWrites_extent 68 _ pair member
  have pairBound : pair.1 < Verity.Core.Uint256.modulus := by omega
  simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt pairBound]
  left
  omega

/-- The complete compiler payload retains exactly the computed header bytes. -/
theorem full_header_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus)
    (query : Nat) (header : query < 68) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte query =
      (applyStores state (headerWrites (bytesFromString message).length)).byteMemory.readByte query := by
  change (applyStores state (headerWrites (bytesFromString message).length ++
    PhysicalErrorStringExecution.dataWrites message)).byteMemory.readByte query = _
  rw [applyStores_append]
  exact data_preserves_header _ message extent query header

theorem full_selector_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) (index : Fin 4) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte index.val =
      valueWord (Verity.Core.Uint256.ofNat Compiler.Constants.errorStringSelectorWord)
        ⟨index.val, by have := index.isLt; omega⟩ := by
  rw [full_header_byte state message extent _ (by have := index.isLt; omega)]
  exact selector_byte _ _ index

theorem full_offset_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) (index : Fin 32) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte (4 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat 32) index := by
  rw [full_header_byte state message extent _ (by have := index.isLt; omega)]
  exact offset_byte _ _ index

theorem full_length_byte (state : IRState) (message : String)
    (extent : 68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤
      Verity.Core.Uint256.modulus) (index : Fin 32) :
    (applyStores state (PhysicalErrorStringExecution.writes message)).byteMemory.readByte (36 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (bytesFromString message).length) index := by
  rw [full_header_byte state message extent _ (by have := index.isLt; omega)]
  exact length_byte _ _ index

end Compiler.Proofs.IRGeneration.PhysicalErrorStringHeader
