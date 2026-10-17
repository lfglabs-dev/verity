import Compiler.Proofs.IRGeneration.NativeSourceThirdFieldExtent
namespace Compiler.Proofs.IRGeneration.NativeSourceFourthFieldExtent
open EvmYul
theorem loaded_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.mload g).2.activeWords := by
  rfl

theorem loaded_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251) (source : g.toNat < 2 ^ 64) :
    (NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [loaded_words]
  apply NativeSourceWordAccessExtent.load_bound
  · exact upper
  · exact source

theorem store_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFourthFieldStore.s4 cost pre a b c d e f g h i tail).activeWords =
      (pre.toMachineState.mstore (c + UInt256.ofNat 288) a).activeWords := by
  rfl

theorem stored_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail).toMachineState.mstore
        (c + UInt256.ofNat 288)
        (((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a)).activeWords := by
  unfold NativeSourceFourthField.stored
  rw [store_words]

theorem stored_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (source : g.toNat < 2 ^ 64) (destination : (c + UInt256.ofNat 288).toNat < 2 ^ 64) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [stored_words]
  apply NativeSourceWordAccessExtent.store_bound
  · exact loaded_bound cost pre a b c d e f g h i j k tail upper source
  · exact destination

end Compiler.Proofs.IRGeneration.NativeSourceFourthFieldExtent

