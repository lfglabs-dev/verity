import Compiler.Proofs.IRGeneration.NativeSourceAcceptedFree
namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorPaddingCopy
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
    (requested : UInt256)
    (copyGuard : NativeSourceAllocatorDecision.flag
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) requested = ⟨0⟩)
    (sizeFits : requested.toNat + 31 < 2 ^ 256) (positive : 0 < requested.toNat) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat count =
      pre.memory.extract i.toNat (i.toNat + count) := by
  have fieldFits : c.toNat + 288 < 2 ^ 256 := by omega
  have fieldBound : c.toNat + 192 < 2 ^ System.Platform.numBits := by
    have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
    omega
  have padding0 := NativeSourceBoundedPadding.field_padding c pre.memory fieldBound (by omega)
  have copyPadding := NativeSourceRequestedMargin.copy_padding
    (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) requested
    (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory
    copyGuard sizeFits positive platform
  exact NativeSourceSizedPaddingCopy.readback cost pre a b c d e f g h i j k z tail count
    above bounded padding0 inside0 fieldFits below0 sizeBelow below4 extent copyPadding

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorPaddingCopy
