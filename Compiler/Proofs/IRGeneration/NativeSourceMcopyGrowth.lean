import Compiler.Proofs.IRGeneration.NativeSourceMcopyWindow

namespace Compiler.Proofs.IRGeneration.NativeSourceMcopyGrowth
open EvmYul EVM.Proof

theorem write_growth (memory : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (input : source + size ≤ memory.size)
    (growth : memory.size ≤ dest + size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    memory.write source memory dest size =
      ⟨memory.data.extract 0 dest ++ Array.replicate (dest - memory.size) 0 ++
        memory.data.extract source (source + size)⟩ := by
  have zeros : (ffi.ByteArray.zeroes (⟨(dest - memory.size : Nat)⟩ : USize)).data =
      Array.replicate (dest - memory.size) 0 := by
    show Array.replicate (USize.toNat ⟨((dest - memory.size : Nat) : BitVec System.Platform.numBits)⟩) 0 = _
    rw [ffi.ByteArray.toNat_natCast_of_lt _ padding]
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show min size (memory.size - source) = size by omega,
    show min memory.size (dest + size) = memory.size by omega]
  dsimp only
  rw [show memory.size - (dest + size) = 0 by omega]
  rw [ByteArray.append_zeroes (by simp), Nat.add_zero]
  ext1
  simp only [ByteArray.copySlice, ByteArray.data_append, zeros]
  rw [show min size (memory.data.size - source) = size by simpa only [ByteArray.size_data] using (show min size (memory.size - source) = size by omega)]
  have gap : (Array.replicate (dest - memory.size) (0 : UInt8)).size = dest - memory.data.size := by simp
  have tail : (memory.data ++ Array.replicate (dest - memory.size) (0 : UInt8)).extract
      (dest + size) (memory.data ++ Array.replicate (dest - memory.size) (0 : UInt8)).size = #[] := by
    apply Array.extract_eq_empty_of_le
    simp only [Array.size_append, Array.size_replicate, ByteArray.size_data]
    omega
  rw [Array.extract_zero_append _ _ _ gap, tail, Array.append_empty]

theorem memory_growth (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.MCOPY, none)) pre = .ok post)
    (positive : 0 < size.toNat) (input : source.toNat + size.toNat ≤ pre.memory.size)
    (growth : pre.memory.size ≤ dest.toNat + size.toNat)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    post.memory = ⟨pre.memory.data.extract 0 dest.toNat ++
      Array.replicate (dest.toNat - pre.memory.size) 0 ++
      pre.memory.data.extract source.toNat (source.toNat + size.toNat)⟩ := by
  rw [NativeSourceMcopy.memory_step_MCOPY fuel gasCost pre post rest dest source size popped success]
  exact write_growth pre.memory _ _ _ positive input growth padding

theorem write_snapshot (memory : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (input : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    memory.write source memory dest size =
      (memory.extract source (source + size)).write 0 memory dest size := by
  have snapshot : (memory.extract source (source + size)).size = size := by
    rw [ByteArray.size_extract]
    omega
  by_cases fits : dest + size ≤ memory.size
  · rw [NativeSourceMcopyWindow.write_window memory dest source size positive input fits,
      ByteArray.write_eq_of_fits _ memory dest size positive snapshot fits]
    simp only [ByteArray.data_extract]
  · rw [write_growth memory dest source size positive input (by omega) padding,
      ByteArray.write_eq_of_grows _ memory dest size positive snapshot (by omega) padding]
    simp only [ByteArray.data_extract]

theorem readback (memory : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (bounded : size < 2^64) (input : source + size ≤ memory.size)
    (padding : dest - memory.size < 2 ^ System.Platform.numBits) :
    (memory.write source memory dest size).readWithPadding dest size =
      memory.extract source (source + size) := by
  rw [write_snapshot memory dest source size positive input padding]
  apply ByteArray.readWithPadding_write_self_of_pad _ memory dest size positive bounded _ padding
  rw [ByteArray.size_extract]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceMcopyGrowth
