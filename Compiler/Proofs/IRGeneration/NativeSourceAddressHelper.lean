import Compiler.Proofs.IRGeneration.NativeSourceAddressBranch
import Compiler.Proofs.IRGeneration.NativeSourceSizedPacking

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressHelper
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev guard (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressGuardExecution.s10 cost pre word ret tail
abbrev branch (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressBranch.branched cost (guard cost pre word ret tail)
    (word - word.land NativeSourceAddressCanonicality.mask) (ret :: word :: tail)
abbrev result (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressBranch.returned cost (branch cost pre word ret tail) ret word tail

theorem guard_pc (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 946) :
    (guard cost pre word ret tail).pc = UInt256.ofNat 959 := by
  change (((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem update_code (cost : Nat) (pre : EVM.State) (stack : Stack UInt256) (width : Nat) :
    ((stepPre cost pre).replaceStackAndIncrPC stack width).executionEnv.code = pre.executionEnv.code := by rfl

theorem guard_code (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (guard cost pre word ret tail).executionEnv.code = pre.executionEnv.code := by
  unfold guard
  rw [NativeSourceAddressGuardExecution.s10, update_code]
  rw [NativeSourceAddressGuardExecution.s9, update_code]
  rw [NativeSourceAddressGuardExecution.s8, update_code]
  rw [NativeSourceAddressGuardExecution.s7, update_code]
  rw [NativeSourceAddressGuardExecution.s6, update_code]
  rw [NativeSourceAddressGuardExecution.s5, update_code]
  rw [NativeSourceAddressGuardExecution.s4, update_code]
  rw [NativeSourceAddressGuardExecution.s3, update_code]
  rw [NativeSourceAddressGuardExecution.s2, update_code]
  rw [NativeSourceAddressGuardExecution.s1, update_code]

theorem branch_code_frame (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) :
    (NativeSourceAddressBranch.branched cost pre condition rest).executionEnv.code = pre.executionEnv.code := by rfl

theorem branch_code (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (branch cost pre word ret tail).executionEnv.code = pre.executionEnv.code := by
  exact (branch_code_frame cost (guard cost pre word ret tail) _ _).trans (guard_code cost pre word ret tail)

theorem execute_branch (fuel cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    run fuel cost 12 pre = .ok (branch cost pre word ret tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 10 2 pre _ _
    (NativeSourceAddressGuardExecution.execute fuel cost pre word ret tail code pc stack)
    (NativeSourceAddressBranch.execute fuel cost (guard cost pre word ret tail) _ _ ((guard_code cost pre word ret tail).trans code) (guard_pc cost pre word ret tail pc)
      (NativeSourceAddressGuardExecution.output_stack cost pre word ret tail))

theorem branch_pc (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 946) :
    (branch cost pre word ret tail).pc =
      if word.toNat < 2 ^ 160 then UInt256.ofNat 963 else UInt256.ofNat 91 := by
  exact NativeSourceAddressBranch.address_destinations cost _ word ret tail (guard_pc cost pre word ret tail pc)

theorem execute_return (fuel cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) (canonical : word.toNat < 2 ^ 160) :
    run fuel cost 13 pre = .ok (result cost pre word ret tail) := by
  have atPC : (branch cost pre word ret tail).pc = UInt256.ofNat 963 := by
    rw [branch_pc cost pre word ret tail pc, if_pos canonical]
  have last : run fuel cost 1 (branch cost pre word ret tail) = .ok (result cost pre word ret tail) := by
    have step := NativeSourceAddressBranch.return_step fuel cost (branch cost pre word ret tail)
      ret word tail ((branch_code cost pre word ret tail).trans code) atPC (by rfl)
    change Except.bind (EVM.step (fuel + 1) cost (some (decodeAt (branch cost pre word ret tail)))
      (branch cost pre word ret tail)) (run fuel cost 0) = _
    rw [step]
    rfl
  exact NativeSourceSizedPacking.compose fuel cost 12 1 pre _ _
    (execute_branch fuel cost pre word ret tail code pc stack) last

theorem update_world (cost : Nat) (pre : EVM.State) (stack : Stack UInt256) (width : Nat) :
    ((stepPre cost pre).replaceStackAndIncrPC stack width).toState = pre.toState := by rfl

theorem guard_world (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (guard cost pre word ret tail).toState = pre.toState := by
  unfold guard
  rw [NativeSourceAddressGuardExecution.s10, update_world]
  rw [NativeSourceAddressGuardExecution.s9, update_world]
  rw [NativeSourceAddressGuardExecution.s8, update_world]
  rw [NativeSourceAddressGuardExecution.s7, update_world]
  rw [NativeSourceAddressGuardExecution.s6, update_world]
  rw [NativeSourceAddressGuardExecution.s5, update_world]
  rw [NativeSourceAddressGuardExecution.s4, update_world]
  rw [NativeSourceAddressGuardExecution.s3, update_world]
  rw [NativeSourceAddressGuardExecution.s2, update_world]
  rw [NativeSourceAddressGuardExecution.s1, update_world]

theorem branch_world (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) :
    (NativeSourceAddressBranch.branched cost pre condition rest).toState = pre.toState := by rfl

theorem return_world (cost : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressBranch.returned cost pre ret word tail).toState = pre.toState := by rfl

theorem return_frame (cost : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressBranch.returned cost pre ret word tail).stack = word :: tail ∧
      (NativeSourceAddressBranch.returned cost pre ret word tail).pc = ret ∧
      (NativeSourceAddressBranch.returned cost pre ret word tail).memory = pre.memory := by
  exact ⟨rfl, rfl, rfl⟩

theorem result_frame (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (result cost pre word ret tail).stack = word :: tail ∧
      (result cost pre word ret tail).pc = ret ∧
      (result cost pre word ret tail).memory = pre.memory ∧
      (result cost pre word ret tail).toState = pre.toState := by
  have frame := return_frame cost (branch cost pre word ret tail) ret word tail
  refine ⟨frame.1, frame.2.1, ?_, ?_⟩
  · exact frame.2.2.trans ((NativeSourceAddressBranch.memory cost _ _ _).trans
      (NativeSourceAddressGuardExecution.memory cost pre word ret tail))
  · exact (return_world cost _ ret word tail).trans
      ((branch_world cost _ _ _).trans (guard_world cost pre word ret tail))

theorem invalid_branch (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 946) (invalid : ¬word.toNat < 2 ^ 160) :
    (branch cost pre word ret tail).pc = UInt256.ofNat 91 ∧
      (branch cost pre word ret tail).stack = ret :: word :: tail ∧
      (branch cost pre word ret tail).memory = pre.memory := by
  refine ⟨?_, rfl, ?_⟩
  · rw [branch_pc cost pre word ret tail pc, if_neg invalid]
  · rw [NativeSourceAddressBranch.memory, NativeSourceAddressGuardExecution.memory]

end Compiler.Proofs.IRGeneration.NativeSourceAddressHelper
