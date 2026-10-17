import Compiler.Proofs.IRGeneration.NativeSourceAllocatorPointer

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorOverflowEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def amount (size : UInt256) := UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31))
def tested (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorPointer.s5 cost (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail)
    (amount size) base tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) :
    (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail).pc = UInt256.ofNat 919 := by
  change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910) :
    run fuel cost 5 (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail) =
      .ok (tested cost pre base size tail) := by
  exact NativeSourceAllocatorPointer.execute fuel cost
    (NativeSourceAllocatorRoundedEntry.rounded cost pre base size tail) (amount size) base tail
    code (entry_pc cost pre base size tail pc) (NativeSourceAllocatorRoundedEntry.stack cost pre base size tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: tail) :
    run fuel cost 13 pre = .ok (tested cost pre base size tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 8 5 pre _ _
    (NativeSourceAllocatorRoundedEntry.execute fuel cost pre base size tail code pc stack)
    (finish fuel cost pre base size tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (tested cost pre base size tail).stack =
      UInt256.lt (base + amount size) base :: (base + amount size) :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorOverflowEntry
