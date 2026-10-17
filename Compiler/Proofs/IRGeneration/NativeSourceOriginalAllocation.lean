import Compiler.Proofs.IRGeneration.NativeSourcePackedAllocation

namespace Compiler.Proofs.IRGeneration.NativeSourceOriginalAllocation
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def size (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) := NativeSourcePackedAllocation.size cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail
def returned (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) := NativeSourcePackedAllocation.returned cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceDecodedPackingStart.free cost pre) (size cost pre a b c d e f g h tail) = ⟨0⟩) :
    run fuel cost 52 (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) = .ok (returned cost pre a b c d e f g h tail) := by
  exact NativeSourcePackedAllocation.execute cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail fuel code
    (NativeSourcePackingCopies.entry_pc cost pre a b c d e f g h tail pc) (NativeSourcePackingCopies.entry_stack cost pre a b c d e f g h tail) guard

theorem execute (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceDecodedPackingStart.free cost pre) (size cost pre a b c d e f g h tail) = ⟨0⟩) :
    run fuel cost 67 pre = .ok (returned cost pre a b c d e f g h tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 15 52 pre _ _
    (NativeSourceDecodedPackingStart.execute fuel cost pre a b c d e f g h tail code pc stack)
    (second cost pre a b c d e f g h tail fuel code pc guard)

theorem target (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : (returned cost pre a b c d e f g h tail).pc = d := by
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (returned cost pre a b c d e f g h tail).stack = (NativeSourceDecodedPackingStart.free cost pre) :: ((NativeSourceDecodedPackingStart.free cost pre) + b) :: g :: h :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceOriginalAllocation
