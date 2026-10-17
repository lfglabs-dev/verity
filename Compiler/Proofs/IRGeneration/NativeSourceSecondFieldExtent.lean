import Compiler.Proofs.IRGeneration.NativeSourceFirstFieldExtent
namespace Compiler.Proofs.IRGeneration.NativeSourceSecondFieldExtent
open EvmYul
theorem loaded_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.mload e).2.activeWords := by
  rfl

theorem loaded_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251) (source : e.toNat < 2 ^ 64) :
    (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [loaded_words]
  apply NativeSourceWordAccessExtent.load_bound
  · exact upper
  · exact source

theorem store_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondFieldStore.s4 cost pre a b c d e f g h i tail).activeWords =
      (pre.toMachineState.mstore (g + UInt256.ofNat 224) a).activeWords := by
  rfl

theorem stored_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail).toMachineState.mstore
        (c + UInt256.ofNat 224)
        ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e)).activeWords := by
  unfold NativeSourceSecondField.stored
  rw [store_words]

theorem stored_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (source : e.toNat < 2 ^ 64) (destination : (c + UInt256.ofNat 224).toNat < 2 ^ 64) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [stored_words]
  apply NativeSourceWordAccessExtent.store_bound
  · exact loaded_bound cost pre a b c d e f g h i j k tail upper source
  · exact destination

end Compiler.Proofs.IRGeneration.NativeSourceSecondFieldExtent

