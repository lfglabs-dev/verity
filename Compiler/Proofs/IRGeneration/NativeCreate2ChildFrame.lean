import Compiler.Proofs.IRGeneration.NativeConstructorBumpAgreement

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Exact child invocation in the pinned native CREATE2 instruction, after
opcode cost debit and creator nonce insertion. No child evaluator is supplied. -/
def nativeCreate2Child (fuel cost : Nat) (pre : EVM.State) (offset size salt : UInt256) :=
  let debited := { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
  let bumped := creatorBumpedMachine debited pre.executionEnv.codeOwner
  EVM.Lambda fuel debited.executionEnv.blobVersionedHashes debited.createdAccounts
    debited.genesisBlockHeader debited.blocks bumped.accountMap debited.σ₀ debited.substate
    debited.executionEnv.codeOwner debited.executionEnv.sender
    (UInt256.ofNat (EVM.L debited.gasAvailable.toNat)) (UInt256.ofNat debited.executionEnv.gasPrice)
    (UInt256.ofNat 0) (debited.memory.readWithPadding offset.toNat size.toNat)
    (UInt256.ofNat (debited.executionEnv.depth + 1)) (some salt.toByteArray)
    debited.executionEnv.header debited.executionEnv.perm

/-- The native entry size guard applies to header plus runtime payload. -/
theorem native_create2_payload_bound (payload : ByteArray)
    (bounded : (Verity.Core.Model.MidnightInitcode.initcode payload).size ≤ 49152) :
    payload.size ≤ 49141 := by
  have length : (Verity.Core.Model.MidnightInitcode.initcode payload).size = 11 + payload.size := by
    exact Verity.Core.Model.MidnightInitcode.initcode_size payload
  omega


/-- A real completed child result is carried into the actual CREATE2 parent
step, retaining parent environment, original storage and physical memory. -/
theorem native_create2_child_frame (fuel cost : Nat) (pre next : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (child : nativeCreate2Child fuel cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 1) cost (some (.CREATE2, none)) pre = .ok next) :
    next.accountMap = result.2.2.1 ∧ next.substate = result.2.2.2.2.1 ∧ next.createdAccounts = result.2.1 ∧
      next.executionEnv = pre.executionEnv ∧ next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
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

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
