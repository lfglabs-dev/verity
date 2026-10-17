import Verity.Core.ByteMemory

namespace Compiler.CompilationModel.DenoteMemory

/-- Big-endian digits for a variable byte width, used to bound the proof by
one digit per induction step rather than reducing a complete execution. -/
def boundedDigits (width value : Nat) : Fin width → Byte :=
  fun index => ⟨value / 256^(width - 1 - index.val) % 256, Nat.mod_lt _ (by decide)⟩

theorem boundedDigits_fold (width value : Nat) (bound : value < 256^width) :
    (List.ofFn (boundedDigits width value)).foldl
      (fun acc byte => acc * 256 + byte.val) 0 = value := by
  induction width generalizing value with
  | zero =>
      have zero : value = 0 := by simpa using bound
      simp [zero]
  | succ width ih =>
      have precedingDigits : (fun i : Fin width => boundedDigits (width + 1) value i.castSucc) =
          boundedDigits width (value / 256) := by
        funext i
        apply Fin.ext
        have exponent : width + 1 - 1 - i.val = (width - 1 - i.val) + 1 := by
          have := i.isLt
          omega
        simp only [boundedDigits, Fin.val_castSucc, exponent, Nat.pow_succ]
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm 256]
      have smaller : value / 256 < 256^width := by
        have positive : 0 < 256^width := Nat.pow_pos (by decide)
        rw [Nat.pow_succ] at bound
        omega
      rw [List.ofFn_succ_last, precedingDigits, List.foldl_append, ih _ smaller]
      simp only [List.foldl_cons, List.foldl_nil, boundedDigits, Fin.val_last]
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]
      have reconstruction := Nat.mod_add_div value 256
      omega

/-- The byte encoding of a bounded EVM word reconstructs that exact word. -/
theorem wordValue_valueWord (value : Verity.Core.Uint256) :
    wordValue (valueWord value) = value := by
  have bound : value.val < 256^32 := by
    have modulus : 256^32 = Verity.Core.UINT256_MODULUS := by decide
    rw [modulus]
    exact value.isLt
  have digits : valueWord value = boundedDigits 32 value.val := rfl
  unfold wordValue
  rw [digits, boundedDigits_fold _ _ bound]
  cases value with
  | mk value bound =>
      unfold Verity.Core.Uint256.ofNat
      congr
      exact Nat.mod_eq_of_lt bound

end Compiler.CompilationModel.DenoteMemory
