import Compiler.Proofs.IRGeneration.NativeSourceWordAccessExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstFieldExtent
open EvmYul

theorem prepared_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).activeWords = pre.activeWords := by
  rfl

theorem loaded_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.mload d).2.activeWords := by
  rfl

theorem loaded_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : pre.activeWords.toNat < 2 ^ 251) (source : d.toNat < 2 ^ 64) :
    (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [loaded_words]
  apply NativeSourceWordAccessExtent.load_bound
  · rw [prepared_words]
    exact upper
  · exact source

theorem store_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldStore.s4 cost pre a b c d e f g h i tail).activeWords =
      (pre.toMachineState.mstore (h + UInt256.ofNat 192) a).activeWords := by
  rfl

theorem stored_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).activeWords =
      ((NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail).toMachineState.mstore
        (c + UInt256.ofNat 192)
        ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d)).activeWords := by
  unfold NativeSourceFirstField.stored
  rw [store_words]

theorem stored_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : pre.activeWords.toNat < 2 ^ 251)
    (source : d.toNat < 2 ^ 64) (destination : (c + UInt256.ofNat 192).toNat < 2 ^ 64) :
    (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  rw [stored_words]
  apply NativeSourceWordAccessExtent.store_bound
  · exact loaded_bound cost pre a b c d e f g h i j k tail upper source
  · exact destination

end Compiler.Proofs.IRGeneration.NativeSourceFirstFieldExtent

