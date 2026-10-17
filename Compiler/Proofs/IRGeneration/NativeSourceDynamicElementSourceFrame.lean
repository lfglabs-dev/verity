import Compiler.Proofs.IRGeneration.NativeSourceDynamicElementBytes
import Compiler.Proofs.IRGeneration.NativeSourceStoreFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicElementSourceFrame
open EvmYul

theorem word_frame (memory : ByteArray) (value : UInt256) (address start length : Nat)
    (platform : 64 ≤ System.Platform.numBits) (addressBound : address < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ memory.size) (below : start + length ≤ address) :
    memory.size ≤ (value.toByteArray.write 0 memory address 32).size ∧
      (value.toByteArray.write 0 memory address 32).readWithPadding start length =
        memory.readWithPadding start length := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding : address - memory.size < 2 ^ System.Platform.numBits := by omega
  have size := ByteArray.size_write value.toByteArray memory address 32 (by decide)
    (UInt256.size_toByteArray value) padding
  constructor
  · omega
  · have natural : (UInt256.ofNat address).toNat = address := by
      change address % (2 ^ 256) = address
      exact Nat.mod_eq_of_lt (by omega)
    have frame := NativeSourceStoreFrame.read_below
      (show MachineState from ⟨0, 0, memory, ByteArray.empty, ByteArray.empty⟩) (UInt256.ofNat address) value start length
      (by simpa only [natural] using padding) positive bounded inside (by simpa only [natural] using below)
    simpa only [MachineState.mstore, MachineState.writeWord, writeBytes, natural] using frame

theorem read_below (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) (start length : Nat)
    (platform : 64 ≤ System.Platform.numBits) (destBound : dest.toNat + 96 < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ dest.toNat) :
    (NativeSourceDynamicElementExecution.four cost pre source mask dest spare tail).memory.readWithPadding start length = pre.memory.readWithPadding start length := by
  have p32 := NativeSourceFieldGeometry.offset_toNat dest 32 (by decide) (by omega)
  have p64 := NativeSourceFieldGeometry.offset_toNat dest 64 (by decide) (by omega)
  have p96 := NativeSourceFieldGeometry.offset_toNat dest 96 (by decide) (by omega)
  have h1 := word_frame (pre).memory (((NativeSourceDynamicFirstLoad.ready cost pre source (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32 :: tail)).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source)).land mask) dest.toNat start length
    platform (by omega) positive bounded inside (by omega)
  rw [← NativeSourceDynamicElementBytes.first cost pre source mask dest spare tail] at h1
  have inside1 := inside.trans h1.1
  have h2 := word_frame (NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).memory ((NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 32)) (dest + UInt256.ofNat 32).toNat start length
    platform (by rw [p32]; omega) positive bounded inside1 (by rw [p32]; omega)
  rw [← NativeSourceDynamicElementBytes.second cost pre source mask dest spare tail] at h2
  have inside2 := inside1.trans h2.1
  have h3 := word_frame (NativeSourceDynamicElementExecution.two cost pre source mask dest spare tail).memory ((NativeSourceDynamicElementExecution.two cost pre source mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 64)) (dest + UInt256.ofNat 64).toNat start length
    platform (by rw [p64]; omega) positive bounded inside2 (by rw [p64]; omega)
  rw [← NativeSourceDynamicElementBytes.third cost pre source mask dest spare tail] at h3
  have inside3 := inside2.trans h3.1
  have h4 := word_frame (NativeSourceDynamicElementExecution.three cost pre source mask dest spare tail).memory (((NativeSourceDynamicElementExecution.three cost pre source mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 96)).land mask) (dest + UInt256.ofNat 96).toNat start length
    platform (by rw [p96]; omega) positive bounded inside3 (by rw [p96]; omega)
  rw [← NativeSourceDynamicElementBytes.fourth cost pre source mask dest spare tail] at h4
  exact h4.2.trans (h3.2.trans (h2.2.trans h1.2))

end Compiler.Proofs.IRGeneration.NativeSourceDynamicElementSourceFrame
