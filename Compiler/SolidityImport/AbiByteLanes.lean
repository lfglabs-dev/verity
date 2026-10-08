import Mathlib.Data.Nat.Basic

namespace Compiler.CompilationModel.SolidityImport.AbiByteLanes

/-- Insert a byte into a lane known to be zero. Lane zero is least significant;
the encoder converts the big-endian byte index to `31 - index % 32`. -/
def insert (word byte lane : Nat) : Nat := word + 256^lane * byte

theorem inserted_byte (word byte lane : Nat)
    (empty : word / 256^lane % 256 = 0) (bounded : byte < 256) :
    insert word byte lane / 256^lane % 256 = byte := by
  have positive : 0 < 256^lane := Nat.pow_pos (by decide)
  rw [insert, Nat.add_mul_div_left _ _ positive]
  simp [Nat.add_mod, empty, Nat.mod_eq_of_lt bounded]

theorem lower_bytes_preserved (word byte lane : Nat) :
    insert word byte lane % 256^lane = word % 256^lane := by
  simp [insert, Nat.add_mod]

theorem higher_bytes_preserved (word byte lane : Nat)
    (empty : word / 256^lane % 256 = 0) (bounded : byte < 256) :
    insert word byte lane / (256^lane * 256) = word / (256^lane * 256) := by
  have positive : 0 < 256^lane := Nat.pow_pos (by decide)
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  rw [insert, Nat.add_mul_div_left _ _ positive]
  omega

/-- Inserting into a zero lane of an EVM-sized word does not overflow it.
Together with lane preservation, this justifies using modular word addition
for the byte-copy step rather than assuming unbounded arithmetic. -/
theorem insertion_bounded (word byte lane : Nat)
    (wordBound : word < 256^32) (laneBound : lane < 32)
    (empty : word / 256^lane % 256 = 0) (byteBound : byte < 256) :
    insert word byte lane < 256^32 := by
  have split : 256^32 = (256^lane * 256) * 256^(31-lane) := by
    rw [← Nat.pow_succ, ← Nat.pow_add]
    congr 1
    omega
  have same : insert word byte lane / 256^32 = word / 256^32 := by
    have higher := congrArg (fun n => n / 256^(31-lane))
      (higher_bytes_preserved word byte lane empty byteBound)
    simpa only [Nat.div_div_eq_div_mul, ← split] using higher
  have zero : insert word byte lane / 256^32 = 0 :=
    same.trans (Nat.div_eq_of_lt wordBound)
  exact (Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide))).mp zero

/-- No EVM normalization changes a byte insertion satisfying the loop's
zero-lane and size invariant. This lemma states the exact modulo boundary. -/
theorem insertion_modulus (word byte lane : Nat)
    (wordBound : word < 256^32) (laneBound : lane < 32)
    (empty : word / 256^lane % 256 = 0) (byteBound : byte < 256) :
    insert word byte lane % 256^32 = insert word byte lane := by
  exact Nat.mod_eq_of_lt (insertion_bounded word byte lane wordBound laneBound empty byteBound)

/-- Every other byte remains unchanged, including bytes in the same word.
This is the byte-level frame needed to compose adjacent copy iterations. -/
theorem other_byte_preserved (word byte lane other : Nat)
    (empty : word / 256^lane % 256 = 0) (bounded : byte < 256)
    (different : other ≠ lane) :
    insert word byte lane / 256^other % 256 = word / 256^other % 256 := by
  rcases Nat.lt_or_gt_of_ne different with below | above
  · have split : 256^lane = 256^other * (256 * 256^(lane-other-1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]
      congr 1
      omega
    have positive : 0 < 256^other := Nat.pow_pos (by decide)
    rw [insert, split, Nat.mul_assoc, Nat.add_mul_div_left _ _ positive]
    simp [Nat.mul_assoc, Nat.add_mod]
  · have split : 256^other = (256^lane * 256) * 256^(other-lane-1) := by
      rw [← Nat.pow_succ, ← Nat.pow_add]
      congr 1
      omega
    have higher := congrArg (fun n => n / 256^(other-lane-1) % 256)
      (higher_bytes_preserved word byte lane empty bounded)
    simpa only [Nat.div_div_eq_div_mul, ← split] using higher

/-- Shifting and masking selects exactly the arithmetic byte lane. -/
theorem shift_mask_byte (word lane : Nat) :
    (word >>> (8 * lane)) &&& 255 = word / 256^lane % 256 := by
  have power : 2^(8 * lane) = 256^lane := by rw [Nat.pow_mul]
  rw [Nat.shiftRight_eq_div_pow, power]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

/-- Left shift positions a byte at its arithmetic insertion weight. -/
theorem shift_byte (byte lane : Nat) :
    byte <<< (8 * lane) = 256^lane * byte := by
  rw [Nat.shiftLeft_eq, Nat.pow_mul]
  change byte * 256^lane = 256^lane * byte
  exact Nat.mul_comm _ _

end Compiler.CompilationModel.SolidityImport.AbiByteLanes
