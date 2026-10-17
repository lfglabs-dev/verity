import Compiler.Proofs.IRGeneration.NativeCreate2CanonicalEntry

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Actual child bookkeeping fixes its address and empty return buffer.
Neither observation is an independently supplied result certificate. -/
theorem native_create2_child_bookkeeping (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result) :
    result.1 = nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload) ∧
      result.2.2.2.2.2.2 = ByteArray.empty := by
  have formula := completed
  unfold nativeCreate2Child at formula
  dsimp only at formula
  rw [code] at formula
  rw [lambda_constructor payload bounded] at formula
  · have bookkeeping := lambda_result_bookkeeping payload _ _ _ _ _ _ _ result formula
    exact ⟨bookkeeping.1, bookkeeping.2.2.2⟩
  · exact vacant
  · exact enough

/-- Native successful entry removes all non-status branches of the stack guard. -/
theorem native_create2_stack_outcome (pre next : EVM.State) (cost : Nat)
    (rest : Stack UInt256) (offset size : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (observed : Create2CallerObservations pre next cost rest offset size result)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (target : AccountAddress) (address : result.1 = target)
    (before reserved : Create2Accounts.Accounts) (payload : ByteArray) :
    next.stack = rest.push (UInt256.ofNat
      (Create2Operation.outcomeValue (constructorOutcome before reserved pre.executionEnv.codeOwner
        target payload result.2.2.2.2.2.1)).val) := by
  have depth : pre.executionEnv.depth ≠ 1024 := by omega
  have balance : ¬ UInt256.ofNat 0 > (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) := by
    change ¬ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)).toNat < 0
    exact Nat.not_lt_zero _
  have cap : ¬ (pre.memory.readWithPadding offset.toNat size.toNat).size > 49152 := by omega
  rw [observed.1]
  have targetBound : target.val < Verity.Core.Uint256.modulus :=
    lt_of_lt_of_le target.isLt (by decide)
  cases flag : result.2.2.2.2.2.1
  · simp only [Bool.false_eq_true, true_or, if_true, if_false, constructorOutcome, Create2Operation.outcomeValue,
      Verity.Core.Uint256.val_zero]
  · simp only [Bool.true_eq_false, depth, balance, cap, or_self, if_false, constructorOutcome,
      if_true, Create2Operation.outcomeValue, address, Verity.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt targetBound]

/-- Native continuation observations tied to the computed canonical value. -/
structure CallerResultObservations (pre next : EVM.State) (rest : Stack UInt256)
    (offset size : UInt256) (value : Verity.Core.Uint256) : Prop where
  stack : next.stack = rest.push (UInt256.ofNat value.val)
  returndata : next.returnData = ByteArray.empty
  pc : next.pc = pre.pc + UInt256.ofNat 1
  execLength : next.execLength = pre.execLength + 1
  activeWords : next.activeWords = UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat size.toNat)
  original : next.σ₀ = pre.σ₀
  memory : next.memory = pre.memory
  environment : next.executionEnv = pre.executionEnv

/-- Memory metering changes only gas, outside these continuation observations. -/
theorem caller_observations_debited (pre next : EVM.State) (rest : Stack UInt256)
    (offset size : UInt256) (value : Verity.Core.Uint256)
    (observed : CallerResultObservations (create2MemoryDebited pre) next rest offset size value) :
    CallerResultObservations pre next rest offset size value := by
  exact { observed with }

/-- Every native caller observation follows from the same actual completed
child and parent step, including the computed canonical stack result. -/
theorem native_create2_result_observations (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre next : EVM.State) (cost fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (enough : 10 ≤ fuel) (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (child : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next)
    (before reserved : Create2Accounts.Accounts) :
    CallerResultObservations pre next rest offset size (Create2Operation.outcomeValue
      (constructorOutcome before reserved pre.executionEnv.codeOwner
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload))
        payload result.2.2.2.2.2.1)) := by
  have observed := native_create2_caller_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry child stepped
  have bookkeeping := native_create2_child_bookkeeping payload bounded pre cost offset size salt code vacant fuel enough result child
  have frame := native_create2_child_frame (fuel + 2) cost pre next rest offset size salt result popped nonce entry child stepped
  refine ⟨native_create2_stack_outcome pre next cost rest offset size result observed entry _ bookkeeping.1 before reserved payload,
    ?_, observed.2.2.2.1, observed.2.2.2.2.1, observed.2.2.2.2.2,
    frame.2.2.2.2.1, frame.2.2.2.2.2, frame.2.2.2.1⟩
  rw [observed.2.2.1, bookkeeping.2]
  cases result.2.2.2.2.2.1 <;> rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
