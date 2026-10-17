import Compiler.Proofs.IRGeneration.NativeSourceArrayOperandChecks
import Compiler.Proofs.IRGeneration.NativeSourceArrayLoadCheck
import Compiler.Proofs.IRGeneration.NativeSourceArrayFreePointer

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCheckedPointer
open EvmYul EVM EVM.Proof

theorem push_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (NativeSourceArrayFreePointer.pushed pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode273]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) ⟨by omega, depth⟩
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayFreePointer.push_step fuel pre code pc
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem swap_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (pointer n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 276)
    (stack : pre.stack = pointer :: n :: x :: array :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1020) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps
      ((stepPre 3 pre).replaceStackAndIncrPC (array :: n :: x :: pointer :: tail)) := by
  have decoded : decodeAt pre = (.SWAP3, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode276]; rfl
  have check := NativeSourceArrayOperandChecks.swap3 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := NativeSourceArrayFreePointer.swap_step fuel pre pointer n x array tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

def read (pre : EVM.State) :=
  NativeSourceLoadStep.loaded 3 (NativeSourceArrayLoadCheck.expanded (NativeSourceArrayFreePointer.pushed pre))
    (UInt256.ofNat 64) pre.stack

theorem pushed_pc (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 273) :
    (NativeSourceArrayFreePointer.pushed pre).pc = UInt256.ofNat 275 := by
  change pre.pc + UInt256.ofNat 2 = _
  rw [pc]; decide

theorem read_execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (gas : 3 ≤ pre.gasAvailable.toNat)
    (loadGas : memoryExpansionCost (NativeSourceArrayFreePointer.pushed pre) .MLOAD + 3 ≤
      (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat)
    (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 3) jumps pre = EVM.X (fuel + 1) jumps (read pre) := by
  rw [push_continue (fuel + 1) jumps pre code pc gas depth]
  exact NativeSourceArrayLoadCheck.load_continue fuel jumps _ pre.stack code (pushed_pc pre pc) rfl loadGas depth

theorem read_gas (pre : EVM.State) (gas : 3 ≤ pre.gasAvailable.toNat)
    (loadGas : memoryExpansionCost (NativeSourceArrayFreePointer.pushed pre) .MLOAD + 3 ≤
      (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat) :
    (read pre).gasAvailable.toNat = pre.gasAvailable.toNat - 6 -
      memoryExpansionCost (NativeSourceArrayFreePointer.pushed pre) .MLOAD := by
  have pushed : (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) gas
  have expanded := NativeSourceArrayLoadCheck.expansion_gas (NativeSourceArrayFreePointer.pushed pre) (by omega)
  have last : (read pre).gasAvailable.toNat =
      (NativeSourceArrayLoadCheck.expanded (NativeSourceArrayFreePointer.pushed pre)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayCheckedPointer
