import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorStore
open EvmYul EVM EVM.Proof NativeSourceAllocatorReturn

theorem push_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (pushed 3 pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt; rw [code, pc, decode940]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) ⟨by omega, depth⟩
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := push fuel 3 pre code pc
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem store_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 942)
    (stack : pre.stack = UInt256.ofNat 64 :: pointer :: tail)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (mstorePost 3 (NativeSourceFieldStoreChecks.expanded pre) tail (UInt256.ofNat 64) pointer) := by
  have decoded : decodeAt pre = (.MSTORE, none) := by
    unfold decodeAt; rw [code, pc, decode942]; rfl
  have check := NativeSourceFieldStoreChecks.mstore jumps pre gas
    (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (step_MSTORE fuel 3 (NativeSourceFieldStoreChecks.expanded pre)
    tail (UInt256.ofNat 64) pointer (by change pre.stack.pop2 = _; rw [stack]; rfl)) rfl

theorem store_gas (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat) :
    (mstorePost 3 (NativeSourceFieldStoreChecks.expanded pre) tail (UInt256.ofNat 64) pointer).gasAvailable.toNat =
      pre.gasAvailable.toNat - memoryExpansionCost pre .MSTORE - 3 := by
  have charged := NativeSourceFieldStoreChecks.expansion_gas pre (by omega)
  exact (NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)).trans (by rw [charged])

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorStore
