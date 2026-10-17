import Verity.Core.Model.ByteMemoryRoundtrip
import Verity.Core.Model.PhysicalMemory

namespace Compiler.CompilationModel.DenoteMemory

/-- Mathematical big-endian encoding of a variable-width byte vector. -/
def byteDigitsValue (width : Nat) (digits : Fin width → Byte) : Nat :=
  (List.ofFn digits).foldl (fun acc byte => acc * 256 + byte.val) 0

theorem byteDigitsValue_succ (width : Nat) (digits : Fin (width + 1) → Byte) :
    byteDigitsValue (width + 1) digits =
      byteDigitsValue width (fun i => digits i.castSucc) * 256 + (digits (Fin.last width)).val := by
  simp only [byteDigitsValue, List.ofFn_succ_last, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem byteDigitsValue_bound (width : Nat) (digits : Fin width → Byte) :
    byteDigitsValue width digits < 256 ^ width := by
  induction width with
  | zero => simp [byteDigitsValue]
  | succ width ih =>
      rw [byteDigitsValue_succ, Nat.pow_succ]
      have leadingDigits := ih (fun i => digits i.castSucc)
      have last := (digits (Fin.last width)).isLt
      omega

theorem boundedDigits_of_byteDigitsValue (width : Nat) (digits : Fin width → Byte) :
    boundedDigits width (byteDigitsValue width digits) = digits := by
  induction width with
  | zero => funext i; exact Fin.elim0 i
  | succ width ih =>
      let leadingDigits : Fin width → Byte := fun i => digits i.castSucc
      let value := byteDigitsValue (width + 1) digits
      have reconstruction : value = byteDigitsValue width leadingDigits * 256 +
          (digits (Fin.last width)).val := byteDigitsValue_succ width digits
      have lastBound := (digits (Fin.last width)).isLt
      have quotient : value / 256 = byteDigitsValue width leadingDigits := by omega
      have remainder : value % 256 = (digits (Fin.last width)).val := by omega
      have precedingDigits : (fun i : Fin width => boundedDigits (width + 1) value i.castSucc) =
          boundedDigits width (value / 256) := by
        funext i
        apply Fin.ext
        have exponent : width + 1 - 1 - i.val = (width - 1 - i.val) + 1 := by
          have := i.isLt
          omega
        simp only [boundedDigits, Fin.val_castSucc, exponent, Nat.pow_succ]
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm 256]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply Fin.ext
        change value / 256 ^ (width + 1 - 1 - width) % 256 = _
        simpa only [Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one] using remainder
      · have prefixEqual := congrFun precedingDigits j
        rw [quotient, ih leadingDigits] at prefixEqual
        exact prefixEqual

/-- Every physical word, including arbitrary zero bytes, survives the
word-value projection. This direction is needed by physical ABI byte frames. -/
theorem valueWord_wordValue (word : Word) : valueWord (wordValue word) = word := by
  have bounded := byteDigitsValue_bound 32 word
  have modulus : 256 ^ 32 = Verity.Core.Uint256.modulus := by decide
  have normalized : (wordValue word).val = byteDigitsValue 32 word := by
    change byteDigitsValue 32 word % Verity.Core.Uint256.modulus = _
    rw [Nat.mod_eq_of_lt (by simpa only [modulus] using bounded)]
  change boundedDigits 32 (wordValue word).val = word
  rw [normalized]
  exact boundedDigits_of_byteDigitsValue 32 word

end Compiler.CompilationModel.DenoteMemory

namespace Compiler.CompilationModel.DenoteMemory

/-- Exact bridge from a coherent physical word projection to each actual byte. -/
theorem physicalByte_word_grid (world : Verity.ContractState)
    (coherent : Compiler.CompilationModel.PhysicalMemory.Coherent world) (address : Nat) :
    valueWord (world.memory (address / 32 * 32))
      ⟨address % 32, Nat.mod_lt _ (by decide)⟩ = world.physicalByte address := by
  rw [coherent (address / 32 * 32), valueWord_wordValue]
  change world.byteMemory.readByte (address / 32 * 32 + address % 32) =
    world.byteMemory.readByte address
  congr 1
  omega

/-- The aligned arithmetic byte observation used by ABI layout proofs is
exactly the physical byte; the coherence obligation is explicit. -/
theorem physicalByte_word_grid_value (world : Verity.ContractState)
    (coherent : Compiler.CompilationModel.PhysicalMemory.Coherent world) (address : Nat) :
    (world.physicalByte address).val =
      (world.memory (address / 32 * 32)).val / 256 ^ (31 - address % 32) % 256 := by
  have byte := congrArg Fin.val (physicalByte_word_grid world coherent address)
  exact byte.symm

end Compiler.CompilationModel.DenoteMemory
