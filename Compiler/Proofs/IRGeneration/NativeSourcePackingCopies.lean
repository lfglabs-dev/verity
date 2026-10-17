import Compiler.Proofs.IRGeneration.NativeSourceSecondPacking

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingCopies
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def packed (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourceSecondPacking.packed cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

theorem entry_stack (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).stack =
      (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) :: e :: a :: b :: (NativeSourceDecodedPackingStart.free cost pre) :: d :: (NativeSourceDecodedPackingStart.free cost pre) :: ((NativeSourceDecodedPackingStart.free cost pre) + b) :: g :: h :: tail := by
  rfl

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 632) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).pc = UInt256.ofNat 648 := by
  change (((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632) :
    run fuel cost 15 (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) = .ok (packed cost pre a b c d e f g h tail) := by
  exact NativeSourceSecondPacking.execute cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail fuel code
    (entry_pc cost pre a b c d e f g h tail pc) (entry_stack cost pre a b c d e f g h tail)

theorem execute (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 30 pre = .ok (packed cost pre a b c d e f g h tail) := by
  rw [show 30 = 15 + 15 by decide, run_add,
    NativeSourceDecodedPackingStart.execute fuel cost pre a b c d e f g h tail code pc stack]
  exact second cost pre a b c d e f g h tail fuel code pc

end Compiler.Proofs.IRGeneration.NativeSourcePackingCopies
