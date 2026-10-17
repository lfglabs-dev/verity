import Compiler.Proofs.IRGeneration.NativeSourceArrayElementSteps

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementBranch
open EvmYul EVM EVM.Proof

def branched (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre 10 pre with
    pc := if condition != ⟨0⟩ then UInt256.ofNat 91 else pre.pc + UInt256.ofNat 1,
    stack := tail }

theorem rejection_destination : UInt256.ofNat 91 ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  rw [NativeSourceReturnMembership.scanned]
  apply NativeJumpScannerFrame.preserves
  simp [NativeSourceReturnMembership.found]

theorem jump_continue (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 816)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (branched pre condition tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayElementDecodes.decode816]; rfl
  have lookup : EVM.X.notIn pre.stack[0]? (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) = false := by
    rw [stack]
    change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 91)) = false
    rw [NativeSourceJumpChecks.contains_of_mem _ _ rejection_destination]; rfl
  have check := NativeSourceJumpChecks.jumpi (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega) lookup
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 10 (some (.JUMPI, none)) pre = .ok (branched pre condition tail) := by
    change EvmYul.step (τ := .EVM) .JUMPI none (stepPre 10 pre) = _
    unfold EvmYul.step
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem gas_exact (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (gas : 10 ≤ pre.gasAvailable.toNat) :
    (branched pre condition tail).gasAvailable.toNat = pre.gasAvailable.toNat - 10 := by
  exact NativeSourceCheckedRejection.gas_sub _ 10 (by decide) gas

theorem destinations (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 816) :
    (branched pre condition tail).pc = if condition != ⟨0⟩ then UInt256.ofNat 91 else UInt256.ofNat 817 := by
  change (if condition != ⟨0⟩ then UInt256.ofNat 91 else pre.pc + UInt256.ofNat 1) = _
  rw [pc]; rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementBranch
