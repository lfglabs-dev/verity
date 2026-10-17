import Compiler.Proofs.IRGeneration.NativeSourceFieldWriteSnapshots

namespace Compiler.Proofs.IRGeneration.NativeSourceContextFieldWrites
open EvmYul

theorem first (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory =
      ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d).toByteArray.write 0 pre.memory (c + UInt256.ofNat 192).toNat 32 := by
  unfold NativeSourceFirstField.stored
  rw [NativeSourceFieldWriteSnapshots.first]
  change _ = _
  simpa only [MachineState.mstore, MachineState.writeWord, writeBytes] using congrArg (fun memory => ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d).toByteArray.write 0 memory (c + UInt256.ofNat 192).toNat 32) (NativeSourceContextFieldFrames.loaded_memory cost pre a b c d e f g h i j k tail)

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory =
      ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e).toByteArray.write 0 (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory (c + UInt256.ofNat 224).toNat 32 := by
  unfold NativeSourceSecondField.stored
  rw [NativeSourceFieldWriteSnapshots.second]
  rfl

theorem third (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory =
      (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a).toByteArray.write 0 (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory (c + UInt256.ofNat 256).toNat 32 := by
  unfold NativeSourceThirdField.stored
  rw [NativeSourceFieldWriteSnapshots.third]
  rfl

theorem fourth (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory =
      (((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a).toByteArray.write 0 (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory (c + UInt256.ofNat 288).toNat 32 := by
  unfold NativeSourceFourthField.stored
  rw [NativeSourceFieldWriteSnapshots.fourth]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceContextFieldWrites
