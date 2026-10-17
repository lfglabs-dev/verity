import Compiler.Proofs.IRGeneration.NativeSourceMemoryFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceGrowingFrame
open EvmYul

theorem read_below (machine : MachineState) (address value : UInt256) (start length : Nat)
    (grows : machine.memory.size ≤ address.toNat + 32)
    (padding : address.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ machine.memory.size) (below : start + length ≤ address.toNat) :
    (machine.mstore address value).memory.readWithPadding start length =
      machine.memory.readWithPadding start length := by
  have expanded := MachineState.le_size_memory_mstore machine address value padding
  rw [ByteArray.readWithPadding_eq_extract _ _ _ positive bounded (by omega),
    ByteArray.readWithPadding_eq_extract _ _ _ positive bounded inside]
  change (ByteArray.write value.toByteArray 0 machine.memory address.toNat 32).extract start (start + length) = _
  rw [ByteArray.write_eq_of_grows value.toByteArray machine.memory address.toNat 32
    (by decide) (UInt256.size_toByteArray value) grows padding]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  have headSize : (machine.memory.data.extract 0 address.toNat).size = min address.toNat machine.memory.size := by
    simp only [Array.size_extract, ByteArray.size_data, Nat.sub_zero]
  rw [Array.extract_append_of_le _ _ _ _ _ (by simp only [headSize]; omega)]
  simp only [Array.extract_extract, Nat.zero_add]
  congr 1
  omega

end Compiler.Proofs.IRGeneration.NativeSourceGrowingFrame
