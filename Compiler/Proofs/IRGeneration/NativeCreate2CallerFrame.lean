import Compiler.Proofs.IRGeneration.NativeCreate2WorldCompletion

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Native caller observations; the status expression is the pinned instruction's guard. -/
def Create2CallerObservations (pre next : EVM.State) (cost : Nat)
    (rest : Stack UInt256) (offset size : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray) : Prop :=
    next.stack = rest.push (if result.2.2.2.2.2.1 = false ∨ pre.executionEnv.depth = 1024 ∨
        UInt256.ofNat 0 > (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∨
        (pre.memory.readWithPadding offset.toNat size.toNat).size > 49152 then UInt256.ofNat 0 else UInt256.ofNat result.1) ∧
      next.gasAvailable = UInt256.ofNat ((pre.gasAvailable - UInt256.ofNat cost).toNat -
        EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat + result.2.2.2.1.toNat) ∧
      next.returnData = (if result.2.2.2.2.2.1 then ByteArray.empty else result.2.2.2.2.2.2) ∧
      next.pc = pre.pc + UInt256.ofNat 1 ∧ next.execLength = pre.execLength + 1 ∧
      next.activeWords = UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat size.toNat)

/-- Exact native caller observations, retaining the native status guard. -/
theorem native_create2_caller_frame (fuel cost : Nat) (pre next : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (child : nativeCreate2Child fuel cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 1) cost (some (.CREATE2, none)) pre = .ok next) :
    Create2CallerObservations pre next cost rest offset size result := by
  rcases result with ⟨address, created, accounts, gas, substate, success, data⟩
  simp only [EVM.step] at stepped
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind] at stepped
  simp only [popped, nonce, if_false, entry] at stepped
  unfold nativeCreate2Child creatorBumpedMachine at child
  simp only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] at child entry stepped
  simp only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) by rfl] at child entry stepped
  simp only [entry.1, and_self, if_true] at stepped
  rw [child] at stepped
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at stepped
  by_cases out : (pre.gasAvailable - UInt256.ofNat cost + gas).toNat <
      EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat
  · simp only [out, if_true] at stepped
    cases stepped
  · simp only [out, if_false] at stepped
    cases stepped
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


open NativeCreationWorld Verity.Core.Model

/-- Derived completion, raw world commit and every caller observation together. -/
theorem native_create2_complete_observations (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (fuel cost : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256) (enough : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (gasBound : (pre.gasAvailable - UInt256.ofNat cost).toNat < 2^255) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ next result reserved committed,
      EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next ∧
      nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      CreationStorage.commit world (constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner
        target payload result.2.2.2.2.2.1) = .ok committed ∧
      Agreement committed next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory ∧
      Create2CallerObservations pre next cost rest offset size result := by
  obtain ⟨next, result, reserved, committed, stepped, child, commit, agreement, original, memory⟩ :=
    native_create2_world_completed world pre warm agrees payload bounded fuel cost rest offset size salt
      enough code popped nonce entry vacant gasBound
  have observations := native_create2_caller_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry child stepped
  exact ⟨next, result, reserved, committed, stepped, child, commit, agreement, original, memory, observations⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
