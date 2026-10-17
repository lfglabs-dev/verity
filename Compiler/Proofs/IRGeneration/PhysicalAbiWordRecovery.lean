import Compiler.Proofs.IRGeneration.PhysicalAbiBytes
import Verity.Core.Model.ByteMemoryInverse
import Mathlib.Data.List.OfFn

/-! Byte-by-byte recovery of the compiler's padded ABI chunks, through the
physical word carrier rather than the historical offset-to-word map. -/
namespace Compiler.Proofs.IRGeneration.PhysicalAbiWordRecovery
open Compiler.CompilationModel PhysicalAbiBytes DenoteMemory

def paddedBytes (bytes : List UInt8) : List UInt8 :=
  bytes ++ List.replicate (32 - bytes.length) 0

def toByte (byte : UInt8) : Byte := ⟨byte.toNat, UInt8.toNat_lt byte⟩

def paddedWord (bytes : List UInt8) (bound : bytes.length ≤ 32) : Word :=
  fun index => toByte ((paddedBytes bytes)[index.val]'(by
    rw [show (paddedBytes bytes).length = 32 from padded_length bound]
    exact index.isLt))

theorem paddedWord_list (bytes : List UInt8) (bound : bytes.length ≤ 32) :
    List.ofFn (paddedWord bytes bound) = (paddedBytes bytes).map toByte := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
    exact (padded_length bound).symm
  · intro index left right
    simp only [List.getElem_ofFn, List.getElem_map, paddedWord]

theorem paddedWord_value (bytes : List UInt8) (bound : bytes.length ≤ 32) :
    wordValue (paddedWord bytes bound) = Verity.Core.Uint256.ofNat (wordFromBytes bytes) := by
  unfold wordValue
  rw [paddedWord_list, List.foldl_map]
  rfl

/-- Every padded compiler chunk recovers exactly, including all zero padding. -/
theorem word_recovery (bytes : List UInt8) (bound : bytes.length ≤ 32) :
    valueWord (Verity.Core.Uint256.ofNat (wordFromBytes bytes)) = paddedWord bytes bound := by
  rw [← paddedWord_value bytes bound]
  exact valueWord_wordValue _

theorem word_byte (bytes : List UInt8) (bound : bytes.length ≤ 32) (index : Fin 32) :
    valueWord (Verity.Core.Uint256.ofNat (wordFromBytes bytes)) index =
      paddedWord bytes bound index := congrFun (word_recovery bytes bound) index

/-- Original bytes are retained at their exact position, not merely as a word. -/
theorem word_original_byte (bytes : List UInt8) (bound : bytes.length ≤ 32)
    (index : Fin bytes.length) :
    (valueWord (Verity.Core.Uint256.ofNat (wordFromBytes bytes))
      ⟨index.val, by omega⟩).val = bytes[index.val].toNat := by
  rw [word_byte bytes bound]
  simp only [paddedWord, paddedBytes, List.getElem_append_left index.isLt, toByte]

/-- The final short chunk explicitly writes zero bytes through its padded tail. -/
theorem word_padding_byte (bytes : List UInt8) (bound : bytes.length ≤ 32)
    (index : Fin 32) (padding : bytes.length ≤ index.val) :
    (valueWord (Verity.Core.Uint256.ofNat (wordFromBytes bytes)) index).val = 0 := by
  rw [word_byte bytes bound]
  simp only [paddedWord, paddedBytes, List.getElem_append_right padding,
    List.getElem_replicate, toByte]
  rfl

/-- The actual IR payload store recovers the complete chunk byte, even
when earlier state memory is nonempty and later stores are unaligned. -/
theorem stored_chunk_byte (state : IRState) (bytes : List UInt8)
    (bound : bytes.length ≤ 32) (offset : Nat) (tail : List (Nat × Nat))
    (index : Fin 32)
    (outside : ∀ pair ∈ tail,
      (Verity.Core.Uint256.ofNat offset).val + index.val <
        (Verity.Core.Uint256.ofNat pair.1).val ∨
      (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤
        (Verity.Core.Uint256.ofNat offset).val + index.val) :
    (PhysicalRevertWrites.applyStores state
      ((offset, wordFromBytes bytes) :: tail)).byteMemory.readByte
      ((Verity.Core.Uint256.ofNat offset).val + index.val) =
      paddedWord bytes bound index := by
  rw [PhysicalRevertWrites.applyStores_byte_written state offset _ tail index outside]
  exact word_byte bytes bound index

end Compiler.Proofs.IRGeneration.PhysicalAbiWordRecovery
