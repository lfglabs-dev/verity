import Compiler.Proofs.IRGeneration.NativeCreate2GasDebit

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

private theorem padding_count (size count : Nat) (bounded : size ≤ 49152) (le : count ≤ size) :
    ({ toBitVec := (size : BitVec System.Platform.numBits) - (count : BitVec System.Platform.numBits) } : USize).toNat = size - count := by
  have small : size < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> omega
  have countSmall : count < 2 ^ System.Platform.numBits := by omega
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt countSmall]
  rw [show 2 ^ System.Platform.numBits - count + size = 2 ^ System.Platform.numBits + (size - count) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem unpadded_size (source : ByteArray) (offset size : Nat) :
    (source.readWithoutPadding offset size).size ≤ size := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · rw [ByteArray.size_extract]
    omega

/-- Native padding uses an exact natural count throughout the supported cap. -/
theorem native_padding_exact (source : ByteArray) (offset size : Nat) (bounded : size ≤ 49152) :
    (source.readWithPadding offset size).data =
      (source.readWithoutPadding offset size).data ++
        Array.replicate (size - (source.readWithoutPadding offset size).size) 0 := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  simp only [ByteArray.data_append, ffi.ByteArray.zeroes]
  rw [padding_count size _ bounded (unpadded_size source offset size)]

/-- Actual native padded reads equal the complete byte-indexed window. -/
theorem native_padded_slice (source : ByteArray) (offset size : Nat)
    (bounded : size ≤ 49152) :
    source.readWithPadding offset size =
      ⟨((List.range size).map fun index => source.data[offset + index]?.getD 0).toArray⟩ := by
  apply ByteArray.ext
  rw [native_padding_exact source offset size bounded]
  unfold ByteArray.readWithoutPadding
  by_cases outside : offset ≥ source.size
  · simp only [outside, if_true, ByteArray.data_empty, ByteArray.size_empty, Nat.sub_zero, Array.empty_append]
    apply Array.ext
    · simp
    · intro index left right
      simp only [Array.getElem_replicate, List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [Array.getElem?_eq_none (by change source.size ≤ offset + index; omega)]
      rfl
  · rw [if_neg outside]
    rw [ByteArray.data_extract]
    apply Array.ext
    · simp only [Array.size_append, Array.size_extract, Array.size_replicate,
        List.size_toArray, List.length_map, List.length_range, ByteArray.size_extract, ByteArray.size_data]
      omega
    · intro index left right
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      by_cases active : index < (source.data.extract offset (offset + min size source.size)).size
      · rw [Array.getElem_append_left active, Array.getElem_extract]
        rw [Array.getElem?_eq_getElem (by have := Array.getElem_extract_aux active; exact this)]
        rfl
      · rw [Array.getElem_append_right (by omega), Array.getElem_replicate]
        rw [Array.getElem?_eq_none (by simp only [Array.size_extract, ByteArray.size_data] at active; simp only [List.size_toArray, List.length_map, List.length_range] at right; change source.size ≤ offset + index; omega)]
        rfl

/-- Native allocated bytes fit inside the active word extent at an authentic
caller boundary; the rest of the physical carrier is an implicit zero tail. -/
theorem caller_memory_byte (pre : EVM.State)
    (allocated : pre.memory.size ≤ pre.activeWords.toNat * 32) (index : Nat) :
    UInt8.ofNat ((CreationBytecode.callerMemory pre).readByte index).val = pre.memory.data[index]?.getD 0 := by
  unfold Compiler.CompilationModel.DenoteMemory.Memory.readByte CreationBytecode.callerMemory
  dsimp only
  by_cases active : index < pre.activeWords.toNat * 32
  · rw [if_pos active]
    simp
  · rw [if_neg active]
    rw [Array.getElem?_eq_none (by change pre.memory.size ≤ index; omega)]
    rfl

/-- Full actual native initcode window agrees with canonical physical bytes.
No hash, selected word or predicted payload substitutes for the window. -/
theorem caller_physical_slice (world : Verity.ContractState) (pre : EVM.State)
    (allocated : pre.memory.size ≤ pre.activeWords.toNat * 32)
    (offset size : Nat) (bounded : size ≤ 49152) :
    Create2.physicalInitcodeBytes (world.installPhysicalMemory (CreationBytecode.callerMemory pre)) offset size =
      pre.memory.readWithPadding offset size := by
  rw [native_padded_slice pre.memory offset size bounded]
  unfold Create2.physicalInitcodeBytes Verity.ContractState.physicalByte Verity.ContractState.installPhysicalMemory
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index _
  exact caller_memory_byte pre allocated (offset + index)

/-- Expanding canonical memory exposes zeros without changing any byte read. -/
theorem expanded_memory_read (memory : Memory) (extent index : Nat) :
    (memory.expand extent).readByte index = memory.readByte index := by
  by_cases active : index < memory.size
  · exact Memory.expand_readByte_active memory extent index active
  · rw [Memory.expand_readByte_fresh memory extent index (by omega), Memory.readByte, if_neg active]

/-- Canonical caller preparation changes extent, never constructor bytes. -/
theorem prepared_memory_read (memory : Memory) (offset size index : Nat) :
    (MidnightInitcode.returnMemory memory offset size).readByte index = memory.readByte index := by
  unfold MidnightInitcode.returnMemory
  split
  · rfl
  · exact expanded_memory_read memory (offset + size) index

/-- After canonical memory preparation, the entire physical initcode remains
exactly the real native padded window, including unaligned/zero-tail reads. -/
theorem prepared_physical_slice (world : Verity.ContractState) (pre : EVM.State)
    (allocated : pre.memory.size ≤ pre.activeWords.toNat * 32)
    (offset size : Nat) (bounded : size ≤ 49152) :
    Create2.physicalInitcodeBytes (world.installPhysicalMemory
      (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset size)) offset size =
      pre.memory.readWithPadding offset size := by
  rw [← caller_physical_slice world pre allocated offset size bounded]
  unfold Create2.physicalInitcodeBytes Verity.ContractState.physicalByte Verity.ContractState.installPhysicalMemory
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index _
  rw [prepared_memory_read]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
