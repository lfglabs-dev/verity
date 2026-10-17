import Compiler.Proofs.IRGeneration.NativeSourceSecondCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondPacking
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def packed (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourceSecondCopy.copied cost (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail) ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b) ((e + length) + d) (e + length) c (d :: e :: f :: g :: dest :: x :: y :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 648) :
    (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 659 := by
  change (((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem copy (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648) :
    run fuel cost 4 (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail) = .ok (packed cost pre length b c d e f g dest x y tail) := by
  exact NativeSourceSecondCopy.execute fuel cost (NativeSourceSecondCopyStore.loaded cost pre length b c d e f g dest x y tail) ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b) ((e + length) + d) (e + length) c (d :: e :: f :: g :: dest :: x :: y :: tail) code
    (entry_pc cost pre length b c d e f g dest x y tail pc) (NativeSourceSecondCopyStore.loaded_stack cost pre length b c d e f g dest x y tail)

theorem execute (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    run fuel cost 15 pre = .ok (packed cost pre length b c d e f g dest x y tail) := by
  rw [show 15 = 11 + 4 by decide, run_add,
    NativeSourceSecondCopyStore.execute fuel cost pre length b c d e f g dest x y tail code pc stack]
  exact copy cost pre length b c d e f g dest x y tail fuel code pc

theorem bytes (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (positive : 0 < ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat)
    (bounded : ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat < 2^64)
    (input : c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat ≤
      (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.size)
    (padding : ((e + length) + d).toNat - (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits) :
    (packed cost pre length b c d e f g dest x y tail).memory.readWithPadding ((e + length) + d).toNat
      ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat =
      (NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).memory.extract c.toNat
        (c.toNat + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b).toNat) := by
  exact NativeSourceSecondCopy.bytes cost _ _ _ _ _ _ positive bounded input padding

end Compiler.Proofs.IRGeneration.NativeSourceSecondPacking
