import Compiler.Proofs.IRGeneration.NativeSourceContextFieldFrames

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldWriteSnapshots
open EvmYul

theorem first (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldStore.s4 cost pre a b c d e f g h i tail).memory =
      (pre.toMachineState.mstore (h + UInt256.ofNat 192) a).memory := by
  rfl

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :
    (NativeSourceSecondFieldStore.s4 cost pre a b c d e f g h i tail).memory =
      (pre.toMachineState.mstore (g + UInt256.ofNat 224) a).memory := by
  rfl

theorem third (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :
    (NativeSourceMaskedFieldStore.s4 cost pre a b c d e f g h i tail).memory =
      (pre.toMachineState.mstore (e + UInt256.ofNat 256) a).memory := by
  rfl

theorem fourth (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :
    (NativeSourceFourthFieldStore.s4 cost pre a b c d e f g h i tail).memory =
      (pre.toMachineState.mstore (c + UInt256.ofNat 288) a).memory := by
  rfl

theorem length_word (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldRoundingStore.s4 cost pre mask size a b c d e f g tail).memory =
      (pre.toMachineState.mstore f (size + mask)).memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldWriteSnapshots
