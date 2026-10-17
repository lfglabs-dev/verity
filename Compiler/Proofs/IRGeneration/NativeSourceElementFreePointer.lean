import Compiler.Proofs.IRGeneration.NativeSourceElementAllocationDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceElementFreePointer
open EvmYul EVM EVM.Proof

def pushed (pre : EVM.State) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 64 :: pre.stack) 2

def read (pre : EVM.State) :=
  NativeSourceLoadStep.loaded 3 (NativeSourceArrayLoadCheck.expanded (pushed pre)) (UInt256.ofNat 64) pre.stack

theorem push_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 817)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (pushed pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceElementAllocationDecodes.decode817]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) ⟨by omega, depth⟩
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH1, some (UInt256.ofNat 64, 1))) pre = .ok (pushed pre) := by rfl
  exact X_succ_of_continue decoded check step rfl

theorem load_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 819)
    (stack : pre.stack = UInt256.ofNat 64 :: tail)
    (gas : memoryExpansionCost pre .MLOAD + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (NativeSourceLoadStep.loaded 3 (NativeSourceArrayLoadCheck.expanded pre) (UInt256.ofNat 64) tail) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceElementAllocationDecodes.decode819]; rfl
  have check := NativeSourceArrayLoadCheck.mload jumps pre gas (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (NativeSourceLoadStep.step fuel 3 (NativeSourceArrayLoadCheck.expanded pre) _ tail stack) rfl

theorem pushed_pc (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 817) :
    (pushed pre).pc = UInt256.ofNat 819 := by
  change pre.pc + UInt256.ofNat 2 = _
  rw [pc]; decide

theorem read_execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 817)
    (gas : 3 ≤ pre.gasAvailable.toNat)
    (loadGas : memoryExpansionCost (pushed pre) .MLOAD + 3 ≤
      (pushed pre).gasAvailable.toNat)
    (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 3) jumps pre = EVM.X (fuel + 1) jumps (read pre) := by
  rw [push_continue (fuel + 1) jumps pre code pc gas depth]
  exact load_continue fuel jumps _ pre.stack code (pushed_pc pre pc) rfl loadGas depth

theorem read_gas (pre : EVM.State) (gas : 3 ≤ pre.gasAvailable.toNat)
    (loadGas : memoryExpansionCost (pushed pre) .MLOAD + 3 ≤
      (pushed pre).gasAvailable.toNat) :
    (read pre).gasAvailable.toNat = pre.gasAvailable.toNat - 6 -
      memoryExpansionCost (pushed pre) .MLOAD := by
  have pushGas : (pushed pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) gas
  have expanded := NativeSourceArrayLoadCheck.expansion_gas (pushed pre) (by omega)
  have last : (read pre).gasAvailable.toNat =
      (NativeSourceArrayLoadCheck.expanded (pushed pre)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem read_frame (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 817) :
    (read pre).pc = UInt256.ofNat 820 ∧
    (read pre).stack = pre.toMachineState.lookupMemory (UInt256.ofNat 64) :: pre.stack ∧
    (read pre).memory = pre.memory ∧ (read pre).toState = pre.toState := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (pushed pre).pc + UInt256.ofNat 1 = _
  rw [pushed_pc pre pc]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceElementFreePointer
