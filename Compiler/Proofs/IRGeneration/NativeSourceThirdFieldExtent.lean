import Compiler.Proofs.IRGeneration.NativeSourceSecondFieldExtent
namespace Compiler.Proofs.IRGeneration.NativeSourceThirdFieldExtent
open EvmYul
theorem loaded_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.mload f).2.activeWords := by
  rfl

theorem loaded_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251) (source : f.toNat < 2 ^ 64) :
    (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [loaded_words]
  apply NativeSourceWordAccessExtent.load_bound
  · exact upper
  · exact source

theorem store_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceMaskedFieldStore.s4 cost pre a b c d e f g h i tail).activeWords =
      (pre.toMachineState.mstore (e + UInt256.ofNat 256) a).activeWords := by
  rfl

theorem stored_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail).toMachineState.mstore
        (c + UInt256.ofNat 256)
        (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a)).activeWords := by
  unfold NativeSourceThirdField.stored
  rw [store_words]

theorem stored_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (source : f.toNat < 2 ^ 64) (destination : (c + UInt256.ofNat 256).toNat < 2 ^ 64) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [stored_words]
  apply NativeSourceWordAccessExtent.store_bound
  · exact loaded_bound cost pre a b c d e f g h i j k tail upper source
  · exact destination

end Compiler.Proofs.IRGeneration.NativeSourceThirdFieldExtent

