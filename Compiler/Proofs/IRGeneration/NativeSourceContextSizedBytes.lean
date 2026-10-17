import Compiler.Proofs.IRGeneration.NativeSourceContextFieldWrites

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSizedBytes
open EvmYul

theorem sized_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).memory =
      ((a - b) + UInt256.lnot (UInt256.ofNat 31)).toByteArray.write 0 pre.memory h.toNat 32 := by
  unfold NativeSourceFieldSize.stored
  rw [NativeSourceFieldWriteSnapshots.length_word]
  rfl

theorem length_word (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory =
      ((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray.write 0
        (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory j.toNat 32 := by
  exact sized_memory cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: tail)

theorem encoded_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory =
      ((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray.write 0
        ((((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a).toByteArray.write 0
          ((((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a).toByteArray.write 0
            (((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e).toByteArray.write 0
              (((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d).toByteArray.write 0
                pre.memory (c + UInt256.ofNat 192).toNat 32)
              (c + UInt256.ofNat 224).toNat 32)
            (c + UInt256.ofNat 256).toNat 32)
          (c + UInt256.ofNat 288).toNat 32)
        j.toNat 32 := by
  rw [length_word, NativeSourceContextFieldWrites.fourth,
    NativeSourceContextFieldWrites.third, NativeSourceContextFieldWrites.second,
    NativeSourceContextFieldWrites.first]

end Compiler.Proofs.IRGeneration.NativeSourceContextSizedBytes
