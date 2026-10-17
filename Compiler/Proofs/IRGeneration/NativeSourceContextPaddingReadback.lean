import Compiler.Proofs.IRGeneration.NativeSourceContextPacked
namespace Compiler.Proofs.IRGeneration.NativeSourceContextPaddingReadback
open EvmYul
theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) (count : Nat)
    (above : 96 ≤ i.toNat)
    (bounded : count < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits)
    (inside0 : i.toNat + count ≤ pre.memory.size)
    (fields : c.toNat + 288 < 2 ^ 64)
    (below0 : i.toNat + count ≤ (c + UInt256.ofNat 192).toNat)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (below4 : i.toNat + count ≤ j.toNat)
    (extent : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat = count)
    (endBound : (((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat +
      (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat) +
      (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) + 32 + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)
      (NativeSourceContextPacked.requested cost pre a b c d e f g h i j k z tail) = ⟨0⟩) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat count =
      pre.memory.extract i.toNat (i.toNat + count) := by
  have padding := NativeSourceContextPacked.copy_padding cost pre a b c d e f g h i j k z tail
    (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory platform endBound guard
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding0 := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  exact NativeSourceSizedPaddingCopy.readback cost pre a b c d e f g h i j k z tail count
    above bounded padding0 inside0 (by omega) below0 sizeBelow below4 extent padding

end Compiler.Proofs.IRGeneration.NativeSourceContextPaddingReadback
