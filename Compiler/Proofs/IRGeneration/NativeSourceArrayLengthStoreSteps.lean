import Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreSteps
open EvmYul EVM EVM.Proof

theorem dup5_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 5 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP5 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP5 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 5 by omega, show ¬pre.stack.length - 5 + 6 > 1024 by omega]

def entered (pre : EVM.State) := (stepPre 1 pre).incrPC

theorem enter_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 292)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (entered pre) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLengthStoreDecodes.decode292]; rfl
  have check := NativeSourceCheckedAllocatorStart.jumpdest_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (show EVM.step (fuel + 1) 1 (some (.JUMPDEST, none)) pre = .ok (entered pre) by rfl) rfl

def lengthPost (pre : EVM.State) (a n : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (n :: a :: n :: tail)

theorem length_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a n : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 293)
    (stack : pre.stack = a :: n :: tail) (gas : 3 ≤ pre.gasAvailable.toNat)
    (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (lengthPost pre a n tail) := by
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLengthStoreDecodes.decode293]; rfl
  have check := NativeSourceFieldStoreChecks.dup2 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons] at depth ⊢; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.DUP2, none)) pre = .ok (lengthPost pre a n tail) := by
    change EvmYul.dup 2 (stepPre 3 pre) = _
    unfold EvmYul.dup
    rw [show (stepPre 3 pre).stack = pre.stack from rfl, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

def pointerPost (pre : EVM.State) (n a x pointer : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (pointer :: n :: a :: n :: x :: pointer :: tail)

theorem pointer_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (n a x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 294)
    (stack : pre.stack = n :: a :: n :: x :: pointer :: tail) (gas : 3 ≤ pre.gasAvailable.toNat)
    (depth : pre.stack.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (pointerPost pre n a x pointer tail) := by
  have decoded : decodeAt pre = (.DUP5, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLengthStoreDecodes.decode294]; rfl
  have check := dup5_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons] at depth ⊢; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.DUP5, none)) pre = .ok (pointerPost pre n a x pointer tail) := by
    change EvmYul.dup 5 (stepPre 3 pre) = _
    unfold EvmYul.dup
    rw [show (stepPre 3 pre).stack = pre.stack from rfl, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem store_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (pointer n : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 295)
    (stack : pre.stack = pointer :: n :: tail)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (mstorePost 3 (NativeSourceFieldStoreChecks.expanded pre) tail pointer n) := by
  have decoded : decodeAt pre = (.MSTORE, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLengthStoreDecodes.decode295]; rfl
  have check := NativeSourceFieldStoreChecks.mstore jumps pre gas (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (step_MSTORE fuel 3 (NativeSourceFieldStoreChecks.expanded pre)
    tail pointer n (by change pre.stack.pop2 = _; rw [stack]; rfl)) rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreSteps
