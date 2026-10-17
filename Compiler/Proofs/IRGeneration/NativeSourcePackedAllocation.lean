import Compiler.Proofs.IRGeneration.NativeSourceAllocatorCaller

namespace Compiler.Proofs.IRGeneration.NativeSourcePackedAllocation
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def size (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) := ((((e + length) + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)) + d) - e)
def returned (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorCaller.returned cost (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail) ((((e + length) + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)) + d) - e) f g (dest :: x :: y :: tail)

theorem entry_stack (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :
    (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).stack = size cost pre length b c d e f g dest x y tail :: f :: g :: dest :: x :: y :: tail := by
  rfl

theorem entry_pc (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 648) :
    (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 676 := by
  change (((((((((((((((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem finish (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (guard : NativeSourceAllocatorDecision.flag g (size cost pre length b c d e f g dest x y tail) = ⟨0⟩) :
    run fuel cost 25 (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail) = .ok (returned cost pre length b c d e f g dest x y tail) := by
  exact NativeSourceAllocatorCaller.execute fuel cost (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail) ((((e + length) + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)) + d) - e) f g (dest :: x :: y :: tail) code (entry_pc cost pre length b c d e f g dest x y tail pc) (entry_stack cost pre length b c d e f g dest x y tail) guard

theorem execute (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)
    (guard : NativeSourceAllocatorDecision.flag g (size cost pre length b c d e f g dest x y tail) = ⟨0⟩) :
    run fuel cost 52 pre = .ok (returned cost pre length b c d e f g dest x y tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 27 25 pre _ _
    (NativeSourceRoundedSecondCopy.execute cost pre length b c d e f g dest x y tail fuel code pc stack)
    (finish cost pre length b c d e f g dest x y tail fuel code pc guard)

end Compiler.Proofs.IRGeneration.NativeSourcePackedAllocation
