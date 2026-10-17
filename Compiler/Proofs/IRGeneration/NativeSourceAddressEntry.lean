import Compiler.Proofs.IRGeneration.NativeSourceCanonicalFrames

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressEntry
open EvmYul EVM EVM.Proof

def entered (pre : EVM.State) := (stepPre 1 pre).incrPC

theorem decode944 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 944) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 944 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 944).toNat = 944 by decide, byte]
  decide

theorem continue_entry (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (entered pre) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, decode944]; rfl
  have check := Z_JUMPDEST jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word, GasConstants.Gjumpdest] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (step_JUMPDEST fuel 1 pre) (H_JUMPDEST _)

theorem entry_frame (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 944) :
    (entered pre).pc = UInt256.ofNat 945 ∧ (entered pre).stack = pre.stack ∧
      (entered pre).toState = pre.toState ∧ (entered pre).memory = pre.memory ∧
      (entered pre).executionEnv.code = pre.executionEnv.code := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  change pre.pc + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem entry_gas (pre : EVM.State) (gas : 1 ≤ pre.gasAvailable.toNat) :
    (entered pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 := by
  exact NativeSourceCheckedRejection.gas_sub _ 1 (by decide) gas

theorem reject_exact (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = address :: ret :: tail) (invalid : ¬(pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 53 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 19) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 53)) ByteArray.empty) := by
  have frame := entry_frame pre pc
  have charged := entry_gas pre (by omega)
  rw [continue_entry (fuel + 17) _ pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  rw [NativeSourceCheckedInputRejection.reject_exact fuel (entered pre) address ret tail
    (frame.2.2.2.2.trans code) frame.1 (frame.2.1.trans stack)
    (by rw [frame.2.2.1]; exact invalid) (by omega) depth, charged]
  congr 3

theorem canonical_return (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = address :: ret :: tail) (valid : (pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 55 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (destination : ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) :
    EVM.X (fuel + 16) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result (entered pre) address ret tail) := by
  have frame := entry_frame pre pc
  have charged := entry_gas pre (by omega)
  rw [continue_entry (fuel + 14) _ pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  exact NativeSourceCheckedCanonical.input_return fuel (entered pre) address ret tail
    (frame.2.2.2.2.trans code) frame.1 (frame.2.1.trans stack)
    (by rw [frame.2.2.1]; exact valid) (by omega) depth destination

theorem canonical_gas (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (gas : 55 ≤ pre.gasAvailable.toNat) :
    (NativeSourceCheckedCanonical.result (entered pre) address ret tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - 55 := by
  have charged := entry_gas pre (by omega)
  have returned := NativeSourceCheckedCanonical.input_gas (entered pre) address ret tail (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceAddressEntry
