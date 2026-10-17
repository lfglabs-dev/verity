import Compiler.Proofs.IRGeneration.NativeSourceDynamicMappedEndpoint

namespace Compiler.Proofs.IRGeneration.NativeSourceLoopFirstPayload
open EvmYul NativeSourceContextCopy NativeSourceDynamicLoopInduction

abbrev before (n cost : Nat) (r : Registers) (initial : EVM.State) (tail : Stack UInt256) :=
  NativeSourceDynamicLoopReturn.returned n cost r initial tail
abbrev rest (n : Nat) (r : Registers) (tail : Stack UInt256) :=
  (advance n r).x12 :: (advance n r).x13 :: (advance n r).x14 :: (advance n r).x15 :: tail

theorem readback (cost : Nat)
    (n : Nat) (r : Registers) (initial : EVM.State) (tail : Stack UInt256)
    (inv : Invariant r initial tail)
    (countBound : r.x1.toNat < 2 ^ 64)
    (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64)
    (initialSource : r.x7.toNat = r.x9.toNat + 32)
    (initialOrder : r.x9.toNat + 32 ≤ r.x11.toNat)
    (bounded : (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat < 2 ^ 64)
    (above : 64 ≤ (NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat)
    (sourceAbove : 96 ≤ (advance n r).x8.toNat)
    (platform : 64 ≤ System.Platform.numBits)
    (inside0 : (advance n r).x8.toNat + (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat ≤ (before n cost r initial tail).memory.size)
    (fields : (advance n r).x9.toNat + 288 < 2 ^ 64)
    (below0 : (advance n r).x8.toNat + (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat ≤ ((advance n r).x9 + UInt256.ofNat 192).toNat)
    (sizeBelow : (advance n r).x9.toNat ≤ ((advance n r).x9 + UInt256.ofNat 288).toNat + 32)
    (below4 : (advance n r).x8.toNat + (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat ≤ (advance n r).x9.toNat)
    (endBound : (((NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat +
      (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat) +
      (NativeSourceContextPacked.second_amount cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat) + 32 + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail))
      (NativeSourceContextPacked.requested cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) = ⟨0⟩)
    (upper : (before n cost r initial tail).activeWords.toNat < 2 ^ 251)
    (sd : (advance n r).x3.toNat < 2 ^ 64)
    (se : (advance n r).x4.toNat < 2 ^ 64)
    (sf : (advance n r).x5.toNat < 2 ^ 64)
    (sg : (advance n r).x6.toNat < 2 ^ 64)
    (sizeAddress : (advance n r).x9.toNat < 2 ^ 64)
    (lengthAddress : (advance n r).x10.toNat < 2 ^ 64)
    (destBound : (free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail) + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : (advance n r).x8.toNat < 2 ^ 64)
    (firstGuard : NativeSourceAllocatorDecision.flag (advance n r).x9 ((advance n r).x11 - (advance n r).x9) = ⟨0⟩)
    (sizeAbove : 96 ≤ (advance n r).x9.toNat)
    :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) (advance n r).x9 (advance n r).x7 (UInt256.ofNat 32) (NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) ((NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) + UInt256.ofNat 32) (UInt256.ofNat 0) NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).memory.readWithPadding ((NativeSourceContextCopy.free cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat =
      (before n cost r initial tail).memory.extract (advance n r).x8.toNat ((advance n r).x8.toNat + (NativeSourceContextCopy.length cost (before n cost r initial tail) NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9 (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)).toNat) := by
  have contained := NativeSourceDynamicMappedEndpoint.endpoint_inside n cost r initial tail platform inv countBound remaining endpoint
  have order := NativeSourceDynamicMappedEndpoint.ordered n r (by omega) endpoint initialOrder
  have source := NativeSourceDynamicMappedEndpoint.source_value n r initialSource
  exact NativeSourcePrecontainedReturn.readback cost (before n cost r initial tail)
    NativeSourceDynamicMappedEndpoint.mask (advance n r).x11 (advance n r).x9
    (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7
    (advance n r).x8 (advance n r).x9 (advance n r).x10 NativeSourceDynamicMappedEndpoint.mask (rest n r tail)
    bounded above sourceAbove platform inside0 fields below0 sizeBelow below4 endBound guard
    upper sd se sf sg sizeAddress lengthAddress destBound sourceBound firstGuard sizeAbove order source contained

end Compiler.Proofs.IRGeneration.NativeSourceLoopFirstPayload
