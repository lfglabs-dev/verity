import Compiler.Proofs.IRGeneration.NativeSourceContextLength

namespace Compiler.Proofs.IRGeneration.NativeSourceContextCopy
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev entry (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :=
  NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (z :: tail)
abbrev length (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :=
  NativeSourceDecodedCopyProvenance.length cost (entry cost pre a b c d e f g h i j k z tail)
    h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail
abbrev copied (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :=
  NativeSourceDecodedPackingStart.copied cost (entry cost pre a b c d e f g h i j k z tail)
    h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail
abbrev free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :=
  NativeSourceDecodedPackingStart.free cost (entry cost pre a b c d e f g h i j k z tail)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256) :
    (entry cost pre a b c d e f g h i j k z tail).stack =
      h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: z :: tail := by
  exact NativeSourceFieldsAllocation.stack cost pre a b c d e f g h i j k (z :: tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) :
    run fuel cost 15 (entry cost pre a b c d e f g h i j k z tail) =
      .ok (copied cost pre a b c d e f g h i j k z tail) := by
  apply NativeSourceDecodedPackingStart.execute fuel cost _ h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail
  · exact code
  · exact NativeSourceFieldsAllocation.target cost pre a b c d e f g h i j k (z :: tail)
  · exact stack cost pre a b c d e f g h i j k z tail

theorem length_value (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (carrier : k.toNat < (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (active : ¬k ≥ (entry cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩) :
    length cost pre a b c d e f g h i j k z tail =
      (entry cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory k := by
  exact NativeSourceContextLength.lookup cost pre a b c d e f g h i j k (z :: tail)
    h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail carrier active

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (bounded : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (sourceInside : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤
      (entry cost pre a b c d e f g h i j k z tail).memory.size)
    (padding : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat
      (length cost pre a b c d e f g h i j k z tail).toNat =
      (entry cost pre a b c d e f g h i j k z tail).memory.extract i.toNat
        (i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat) := by
  exact NativeSourceDecodedCopyProvenance.readback cost _ h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail bounded sourceInside padding

end Compiler.Proofs.IRGeneration.NativeSourceContextCopy
