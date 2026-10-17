import Compiler.Proofs.IRGeneration.NativeSourceSecondCopyShuffles

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondCopy
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceSecondCopyShuffles

def copied (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) : EVM.State :=
  let ready := s3 cost pre length dest finish source tail
  EVM.State.replaceStackAndIncrPC
    { stepPre cost ready with
      toMachineState := (stepPre cost ready).toMachineState.mcopy dest source length }
    (finish :: length :: tail)

theorem decode (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 659) :
    decodeAt (s3 cost pre length dest finish source tail) = (.MCOPY, none) := by
  have readyPC : (s3 cost pre length dest finish source tail).pc = UInt256.ofNat 662 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  exact NativeSourcePackingCopy.decode_at _ code (Or.inr readyPC)

theorem copy_step (fuel cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 659) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre length dest finish source tail)))
      (s3 cost pre length dest finish source tail) =
      .ok (copied cost pre length dest finish source tail) := by
  rw [decode cost pre length dest finish source tail code pc]
  exact NativeSourceMcopy.step_MCOPY fuel cost _ _ dest source length
    (operands cost pre length dest finish source tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 659)
    (stack : pre.stack = length :: dest :: finish :: source :: tail) :
    run fuel cost 4 pre = .ok (copied cost pre length dest finish source tail) := by
  rw [show 4 = 3 + 1 by decide, run_add,
    NativeSourceSecondCopyShuffles.execute fuel cost pre length dest finish source tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, copy_step fuel cost pre length dest finish source tail code pc]
  rfl

theorem bytes (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256)
    (tail : Stack UInt256) (positive : 0 < length.toNat) (bounded : length.toNat < 2^64)
    (input : source.toNat + length.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (copied cost pre length dest finish source tail).memory.readWithPadding dest.toNat length.toNat =
      pre.memory.extract source.toNat (source.toNat + length.toNat) := by
  change (pre.memory.write source.toNat pre.memory dest.toNat length.toNat).readWithPadding _ _ = _
  exact NativeSourceMcopyGrowth.readback pre.memory _ _ _ positive bounded input padding

end Compiler.Proofs.IRGeneration.NativeSourceSecondCopy
