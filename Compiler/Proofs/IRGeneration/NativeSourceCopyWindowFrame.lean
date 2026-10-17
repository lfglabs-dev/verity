import Compiler.Proofs.IRGeneration.NativeSourceFirstCopyProvenance

namespace Compiler.Proofs.IRGeneration.NativeSourceCopyWindowFrame
open EvmYul

theorem read_below (memory : ByteArray) (dest source size start length : Nat)
    (copyPositive : 0 < size) (sourceInside : source + size ≤ memory.size)
    (fits : dest + size ≤ memory.size) (positive : 0 < length) (bounded : length < 2 ^ 64)
    (below : start + length ≤ dest) :
    (memory.write source memory dest size).readWithPadding start length =
      memory.readWithPadding start length := by
  rw [NativeSourceMcopyGrowth.write_snapshot memory dest source size copyPositive sourceInside (by
    rw [Nat.sub_eq_zero_of_le (by omega : dest ≤ memory.size)]
    exact Nat.two_pow_pos _)]
  apply ByteArray.readWithPadding_write_of_le _ memory dest size start length copyPositive _ fits positive bounded below
  rw [ByteArray.size_extract]
  omega

theorem read_above (memory : ByteArray) (dest source size start length : Nat)
    (copyPositive : 0 < size) (sourceInside : source + size ≤ memory.size)
    (fits : dest + size ≤ memory.size) (positive : 0 < length) (bounded : length < 2 ^ 64)
    (above : dest + size ≤ start) (inside : start + length ≤ memory.size) :
    (memory.write source memory dest size).readWithPadding start length =
      memory.readWithPadding start length := by
  rw [NativeSourceMcopyGrowth.write_snapshot memory dest source size copyPositive sourceInside (by
    rw [Nat.sub_eq_zero_of_le (by omega : dest ≤ memory.size)]
    exact Nat.two_pow_pos _)]
  apply ByteArray.readWithPadding_write_of_ge _ memory dest size start length copyPositive _ fits positive bounded above inside
  rw [ByteArray.size_extract]
  omega

theorem growing_read_below (memory : ByteArray) (dest source size start length : Nat)
    (copyPositive : 0 < size) (sourceInside : source + size ≤ memory.size)
    (grows : memory.size ≤ dest + size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ memory.size) (below : start + length ≤ dest) :
    (memory.write source memory dest size).readWithPadding start length =
      memory.readWithPadding start length := by
  have growth := NativeSourceMcopyGrowth.write_growth memory dest source size copyPositive sourceInside grows padding
  have headSize : (memory.data.extract 0 dest).size = min dest memory.size := by
    simp only [Array.size_extract, ByteArray.size_data, Nat.sub_zero]
  have expanded : start + length ≤ (memory.write source memory dest size).size := by
    rw [growth]
    simp only [ByteArray.size, Array.size_append, Array.size_replicate]
    have : start + length ≤ min dest memory.size := by omega
    omega
  rw [ByteArray.readWithPadding_eq_extract _ _ _ positive bounded expanded,
    ByteArray.readWithPadding_eq_extract _ _ _ positive bounded inside, growth]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_le _ _ _ _ _ (by rw [headSize]; omega)]
  simp only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left below]

theorem preserving_read_below (memory : ByteArray) (dest source size start length : Nat)
    (copyPositive : 0 < size) (sourceInside : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ memory.size) (below : start + length ≤ dest) :
    (memory.write source memory dest size).readWithPadding start length =
      memory.readWithPadding start length := by
  by_cases fits : dest + size ≤ memory.size
  · exact read_below memory dest source size start length copyPositive sourceInside fits positive bounded below
  · exact growing_read_below memory dest source size start length copyPositive sourceInside (by omega)
      padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceCopyWindowFrame
