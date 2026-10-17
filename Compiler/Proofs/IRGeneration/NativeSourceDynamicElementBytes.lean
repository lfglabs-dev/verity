import Compiler.Proofs.IRGeneration.NativeSourceDynamicElementExecution

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicElementBytes
open EvmYul

theorem first (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :
    (NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).memory =
      (((NativeSourceDynamicFirstLoad.ready cost pre source (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32 :: tail)).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source)).land mask).toByteArray.write 0 (pre).memory dest.toNat 32 := by
  rfl

theorem second (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :
    (NativeSourceDynamicElementExecution.two cost pre source mask dest spare tail).memory =
      ((NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 32)).toByteArray.write 0 (NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).memory (dest + UInt256.ofNat 32).toNat 32 := by
  rw [NativeSourceDynamicTwoStores.second_memory]
  rfl

theorem third (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :
    (NativeSourceDynamicElementExecution.three cost pre source mask dest spare tail).memory =
      ((NativeSourceDynamicElementExecution.two cost pre source mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 64)).toByteArray.write 0 (NativeSourceDynamicElementExecution.two cost pre source mask dest spare tail).memory (dest + UInt256.ofNat 64).toNat 32 := by
  rw [NativeSourceDynamicThirdStore.memory]
  rfl

theorem fourth (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :
    (NativeSourceDynamicElementExecution.four cost pre source mask dest spare tail).memory =
      (((NativeSourceDynamicElementExecution.three cost pre source mask dest spare tail).toMachineState.lookupMemory (pre.toMachineState.lookupMemory source + UInt256.ofNat 96)).land mask).toByteArray.write 0 (NativeSourceDynamicElementExecution.three cost pre source mask dest spare tail).memory (dest + UInt256.ofNat 96).toNat 32 := by
  rw [NativeSourceDynamicFourthStore.memory]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicElementBytes
