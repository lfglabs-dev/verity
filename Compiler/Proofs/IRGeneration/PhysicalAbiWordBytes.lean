import Compiler.Proofs.IRGeneration.PhysicalErrorStringHeader
import Verity.Core.Model.Denote

namespace Compiler.Proofs.IRGeneration.PhysicalAbiWordBytes
open Compiler.CompilationModel DenoteMemory

/-- Extracting any ABI byte is invariant under uint256 normalization, even
for the legacy unbounded natural-number word carrier. -/
theorem byte_encoding_unbounded (value : Nat) (index : Fin 32) :
    UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat value)) index).val =
      UInt8.ofNat (value / 2^(8*(31-index.val)) % 256) := by
  have bound := index.isLt
  have exponentSum : 8 * (31 - index.val) + (256 - 8 * (31 - index.val)) = 256 := by omega
  have remainderSum : 8 + (248 - 8 * (31 - index.val)) =
      256 - 8 * (31 - index.val) := by omega
  have modulusFactor : Verity.Core.Uint256.modulus =
      2^(8*(31-index.val)) * 2^(256 - 8*(31-index.val)) := by
    rw [← Nat.pow_add, exponentSum]
    rfl
  have remainderFactor : 2^(256 - 8*(31-index.val)) =
      256 * 2^(248 - 8*(31-index.val)) := by
    rw [← remainderSum, Nat.pow_add]
  have power (exponent : Nat) : 256 ^ exponent = 2 ^ (8 * exponent) := by
    rw [Nat.pow_mul]
  simp only [valueWord, Verity.Core.Uint256.val_ofNat, power]
  rw [modulusFactor, Nat.mod_mul_right_div_self, remainderFactor, Nat.mod_mul_right_mod]

theorem byte_encoding (value : Nat) (bound : value < Verity.Core.Uint256.modulus)
    (index : Fin 32) :
    UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat value)) index).val =
      UInt8.ofNat (value / 2^(8*(31-index.val)) % 256) := by
  have power (exponent : Nat) : 256 ^ exponent = 2 ^ (8 * exponent) := by
    rw [Nat.pow_mul]
  simp only [valueWord, Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bound, power]

theorem word_encoding (value : Nat) (bound : value < Verity.Core.Uint256.modulus) :
    List.ofFn (fun index : Fin 32 =>
      UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat value)) index).val) =
      Denote.wordBytes value := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, Denote.wordBytes, List.length_map, List.length_range]
  · intro index left right
    simp only [List.getElem_ofFn, Denote.wordBytes, List.getElem_map, List.getElem_range]
    exact byte_encoding value bound _

end Compiler.Proofs.IRGeneration.PhysicalAbiWordBytes
