import Contracts.Common

/-!
# Hashed nested / struct mapping execution (Pareto G2, #2416)

Executable-plane smoke for `getMappingN` / `setMappingN`, `structMembers`
destructuring and transient mapping chains. The storage shape mirrors
`IdleCreditVault`: a `mapping(address => mapping(uint256 => uint256))`
receipt map and a struct-valued APR-0 bucket. Before this file the
executable plane read `0` from every such field and dropped every write.
-/

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract HashedMappingExecSmoke where
  storage
    withdrawsRequestsByEpoch : Address → Uint256 → Uint256 := slot 226
    apr0Users : MappingStruct(Address,[
      principal @word 0,
      principalEpoch @word 1,
      settledPrincipal @word 2,
      settledInterest @word 3
    ]) := slot 219
    transient locks : Bytes32 → Uint256 := slot 1

  function setRequest (user : Address, epoch : Uint256, amount : Uint256) : Unit := do
    setMappingN withdrawsRequestsByEpoch [user, epoch] amount

  function requestOf (user : Address, epoch : Uint256) : Uint256 := do
    let amount ← getMappingN withdrawsRequestsByEpoch [user, epoch]
    return amount

  function acquire (lockId : Bytes32) : Unit := do
    setMappingN locks [lockId] 1

  function locked (lockId : Bytes32) : Uint256 := do
    let current ← getMappingN locks [lockId]
    return current

  function setReceipt (user : Address, principal : Uint256, epoch : Uint256) : Unit := do
    setStructMember "apr0Users" user "principal" principal
    setStructMember "apr0Users" user "principalEpoch" epoch

  function receiptOf (user : Address) : Tuple [Uint256, Uint256] := do
    let (principal, epoch) := structMembers "apr0Users" user ["principal", "principalEpoch"]
    return (principal, epoch)

/-! ## Slot layout agrees with Solidity

`withdrawsRequestsByEpoch[user][epoch]` at slot 226 lives at
`keccak256(epoch ‖ keccak256(user ‖ 226))`; `apr0Users[user].principalEpoch`
at slot 219 lives at `keccak256(user ‖ 219) + 1`. Both are definitional
against the compiler's `solidityMappingSlot`. -/

theorem request_slot_is_solidity (user : Address) (epoch : Uint256) :
    mappingChainSlot HashedMappingExecSmoke.withdrawsRequestsByEpoch.slot [↑user, ↑epoch] =
      Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.solidityMappingSlot 226 user.toNat) epoch.val := rfl

theorem receipt_epoch_slot_is_solidity (user : Address) :
    structSlot HashedMappingExecSmoke.apr0Users.slot user.toNat 1 =
      (Compiler.Proofs.solidityMappingSlot 219 user.toNat + 1) % Compiler.Constants.evmModulus := rfl

/-! ## The executable plane is no longer opaque -/

/-- A write through `setRequest` is visible to `requestOf` at the same keys. -/
theorem requestOf_after_setRequest (s : ContractState) (user : Address) (epoch amount : Uint256) :
    (Verity.bind (HashedMappingExecSmoke.setRequest user epoch amount)
      fun _ => HashedMappingExecSmoke.requestOf user epoch).run s =
    ContractResult.success amount
      (s.writeSlot (mappingChainSlot 226 [↑user, ↑epoch]) amount) := by
  simp [HashedMappingExecSmoke.setRequest, HashedMappingExecSmoke.requestOf,
    HashedMappingExecSmoke.withdrawsRequestsByEpoch, Contract.run, Bind.bind, Pure.pure,
    Verity.bind, Verity.pure, setMappingN, getMappingN]

/-- `acquire` writes the transient channel only: persistent storage is untouched. -/
theorem acquire_leaves_storage (s : ContractState) (lockId : Bytes32) (n : Nat) :
    ∀ s', (HashedMappingExecSmoke.acquire lockId).run s = ContractResult.success () s' →
      s'.storage n = s.storage n := by
  intro s' h
  simp [HashedMappingExecSmoke.acquire, HashedMappingExecSmoke.locks, Contract.run,
    setTransientMappingN] at h
  subst h
  simp [ContractState.storage, ContractState.writeTransient]

/-- `locked` reads back what `acquire` wrote. -/
theorem locked_after_acquire (s : ContractState) (lockId : Bytes32) :
    (Verity.bind (HashedMappingExecSmoke.acquire lockId)
      fun _ => HashedMappingExecSmoke.locked lockId).run s =
    ContractResult.success 1 (s.writeTransient (mappingChainSlot 1 [↑lockId]) 1) := by
  simp [HashedMappingExecSmoke.acquire, HashedMappingExecSmoke.locked,
    HashedMappingExecSmoke.locks, Contract.run, Bind.bind, Pure.pure, Verity.bind, Verity.pure,
    setTransientMappingN, getTransientMappingN]

/-- `structMembers` destructuring reads the hashed struct slots written by `setReceipt`. -/
theorem receiptOf_after_setReceipt (s : ContractState) (user : Address) (principal epoch : Uint256) :
    (Verity.bind (HashedMappingExecSmoke.setReceipt user principal epoch)
      fun _ => HashedMappingExecSmoke.receiptOf user).run s =
    ContractResult.success (principal, epoch)
      ((s.writeSlot (structSlot 219 user.toNat 0) principal).writeSlot
        (structSlot 219 user.toNat 1) epoch) := by
  have hne : structSlot 219 user.toNat 0 ≠ structSlot 219 user.toNat 1 :=
    structSlot_ne_succ 219 user.toNat 0
  simp [HashedMappingExecSmoke.setReceipt, HashedMappingExecSmoke.receiptOf,
    HashedMappingExecSmoke.structMember, HashedMappingExecSmoke.setStructMember,
    Contract.run, Bind.bind, Pure.pure, Verity.bind, Verity.pure, structMemberAt,
    setStructMemberAt, hne]

end Contracts.Smoke
