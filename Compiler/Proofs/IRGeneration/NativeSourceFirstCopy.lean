import Compiler.Proofs.IRGeneration.NativeSourcePackingFragment

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstCopy
open EvmYul EVM.Proof NativeSourcePackingStack

def copied (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) : EVM.State :=
  let ready := prepared pre cost1 cost2 cost3 length a b c d e f g dest tail
  EVM.State.replaceStackAndIncrPC
    { stepPre cost4 ready with
      toMachineState := (stepPre cost4 ready).toMachineState.mcopy dest a length }
    (length :: b :: c :: d :: e :: f :: g :: dest :: tail)

theorem decode (pre : EVM.State) (cost1 cost2 cost3 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 644) :
    decodeAt (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail) = (.MCOPY, none) := by
  have readyPC : (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail).pc = UInt256.ofNat 647 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  exact NativeSourcePackingCopy.decode_at _ code (Or.inl readyPC)

theorem copy_step (fuel cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 644) :
    EVM.step (fuel + 1) cost4
      (some (decodeAt (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail)))
      (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail) =
      .ok (copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail) := by
  rw [decode pre cost1 cost2 cost3 length a b c d e f g dest tail code pc]
  exact NativeSourceMcopy.step_MCOPY fuel cost4 _ _ dest a length (operands _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem execute (fuel cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 644)
    (stack : pre.stack = length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail) :
    ((do
      let one ← EVM.step (fuel + 1) cost1 (some (decodeAt pre)) pre
      let two ← EVM.step (fuel + 1) cost2 (some (decodeAt one)) one
      EVM.step (fuel + 1) cost3 (some (decodeAt two)) two) >>= fun ready =>
      EVM.step (fuel + 1) cost4 (some (decodeAt ready)) ready) =
      .ok (copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail) := by
  rw [NativeSourcePackingFragment.execute fuel cost1 cost2 cost3 pre length a b c d e f g dest tail code pc stack]
  exact copy_step fuel cost1 cost2 cost3 cost4 pre length a b c d e f g dest tail code pc

theorem bytes (pre : EVM.State) (cost1 cost2 cost3 cost4 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (positive : 0 < length.toNat) (bounded : length.toNat < 2^64)
    (input : a.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (copied pre cost1 cost2 cost3 cost4 length a b c d e f g dest tail).memory.readWithPadding
      dest.toNat length.toNat = pre.memory.extract a.toNat (a.toNat + length.toNat) := by
  change (pre.memory.write a.toNat pre.memory dest.toNat length.toNat).readWithPadding _ _ = _
  exact NativeSourceMcopyGrowth.readback pre.memory _ _ _ positive bounded input padding

end Compiler.Proofs.IRGeneration.NativeSourceFirstCopy
