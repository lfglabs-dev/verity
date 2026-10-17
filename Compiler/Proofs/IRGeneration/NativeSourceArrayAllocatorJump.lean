import Compiler.Proofs.IRGeneration.NativeSourceArrayCheckedPointer

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatorJump
open EvmYul EVM EVM.Proof

theorem allocator_destination : UInt256.ofNat 910 ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  rw [NativeSourceReturnMembership.scanned]
  change UInt256.ofNat 910 ∈ EVM.D_J_aux NativeSourceAbiWrite.code (333 + 13) 895 NativeSourceReturnMembership.found
  rw [NativeSourceHelperScanner.scan0, NativeSourceHelperScanner.scan1, NativeSourceHelperScanner.scan2,
    NativeSourceHelperScanner.scan3, NativeSourceHelperScanner.scan4, NativeSourceHelperScanner.scan5,
    NativeSourceHelperScanner.scan6, NativeSourceHelperScanner.scan7, NativeSourceHelperScanner.scan8,
    NativeSourceHelperScanner.scan9, NativeSourceHelperScanner.scan10, NativeSourceHelperScanner.scan11,
    NativeSourceHelperScanner.scan12]
  apply NativeJumpScannerFrame.preserves
  simp

def jumped (pre : EVM.State) (tail : Stack UInt256) : EVM.State :=
  { stepPre 8 pre with pc := UInt256.ofNat 910, stack := tail }

theorem jump_step (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 910 :: tail) :
    EVM.step (fuel + 1) 8 (some (.JUMP, none)) pre = .ok (jumped pre tail) := by
  change EvmYul.step (τ := .EVM) .JUMP none (stepPre 8 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem jump_continue (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 291)
    (stack : pre.stack = UInt256.ofNat 910 :: tail)
    (gas : 8 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (jumped pre tail) := by
  have decoded : decodeAt pre = (.JUMP, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode291]; rfl
  have lookup : EVM.X.notIn pre.stack[0]? (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) = false := by
    rw [stack]
    change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 910)) = false
    rw [NativeSourceJumpChecks.contains_of_mem _ _ allocator_destination]; rfl
  have check := NativeSourceCheckedReturn.jump_check _ pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega) lookup
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (jump_step fuel pre tail stack) rfl

theorem jump_gas (pre : EVM.State) (tail : Stack UInt256) (gas : 8 ≤ pre.gasAvailable.toNat) :
    (jumped pre tail).gasAvailable.toNat = pre.gasAvailable.toNat - 8 := by
  exact NativeSourceCheckedRejection.gas_sub _ 8 (by decide) gas

theorem jump_frame (pre : EVM.State) (tail : Stack UInt256) :
    (jumped pre tail).pc = UInt256.ofNat 910 ∧ (jumped pre tail).stack = tail ∧
    (jumped pre tail).memory = pre.memory ∧ (jumped pre tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatorJump
