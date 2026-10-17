import Compiler.Proofs.IRGeneration.NativeSourcePackingSize

namespace Compiler.Proofs.IRGeneration.NativeSourceSizedSecondCopy
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def sized (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourcePackingSize.s6 cost (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail) (e + length) ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b) d e f g dest x (y :: tail)

theorem entry_stack (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).stack = (e + length) :: ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b) :: d :: e :: f :: g :: dest :: x :: y :: tail := by
  rfl

theorem entry_pc (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 648) :
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 663 := by
  change (((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem finish (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648) :
    run fuel cost 6 (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail) = .ok (sized cost pre length b c d e f g dest x y tail) := by
  exact NativeSourcePackingSize.execute fuel cost (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail) (e + length) ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b) d e f g dest x (y :: tail) code (entry_pc cost pre length b c d e f g dest x y tail pc) (entry_stack cost pre length b c d e f g dest x y tail)

theorem execute (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    run fuel cost 21 pre = .ok (sized cost pre length b c d e f g dest x y tail) := by
  rw [show 21 = 15 + 6 by decide, run_add,
    NativeSourceSecondPacking.execute cost pre length b c d e f g dest x y tail fuel code pc stack]
  exact finish cost pre length b c d e f g dest x y tail fuel code pc

end Compiler.Proofs.IRGeneration.NativeSourceSizedSecondCopy
