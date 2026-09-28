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
    withdrawn : Uint256 := slot 206

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

  function setWithdrawn (amount : Uint256) : Unit := do
    setStorage withdrawn amount

  function setReceipt (user : Address, principal : Uint256, epoch : Uint256) : Unit := do
    setStructMember "apr0Users" user "principal" principal
    setStructMember "apr0Users" user "principalEpoch" epoch

  function receiptOf (user : Address) : Tuple [Uint256, Uint256] := do
    let (principal, epoch) := structMembers "apr0Users" user ["principal", "principalEpoch"]
    return (principal, epoch)

/-! ## Slot layout agrees with Solidity (interpretation only)

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

/-- The same slot is the interpretation of the symbolic entry
`mapChain 226 [user, epoch] 0` (`Compiler.Proofs.mappingChainSlotLocation`). -/
theorem request_location_is_solidity (user : Address) (epoch : Uint256) :
    Compiler.Proofs.mappingChainSlotLocation 226 [user.toNat, epoch.val] 0 =
      Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.solidityMappingSlot 226 user.toNat) epoch.val :=
  Compiler.Proofs.mappingChainSlotLocation_zero _ _ _

/-! ## The executable plane: symbolic, separated by construction

Every lemma below uses only `propext`, `Classical.choice` and `Quot.sound`
(see `PrintAxioms.lean`): no `solidityMappingSlot_injective`. -/

/-- A write through `setRequest` is visible to `requestOf` at the same keys. -/
theorem requestOf_after_setRequest (s : ContractState) (user : Address) (epoch amount : Uint256) :
    (Verity.bind (HashedMappingExecSmoke.setRequest user epoch amount)
      fun _ => HashedMappingExecSmoke.requestOf user epoch).run s =
    ContractResult.success amount
      (s.writeMapChain 226 [user.toNat, epoch.val] 0 amount) := by
  simp [HashedMappingExecSmoke.setRequest, HashedMappingExecSmoke.requestOf,
    HashedMappingExecSmoke.withdrawsRequestsByEpoch, Contract.run, Bind.bind, Pure.pure,
    Verity.bind, Verity.pure, setMappingN, getMappingN]

/-- Different keys never alias: key inequality, no keccak injectivity. -/
theorem requestOf_other_after_setRequest (s : ContractState) (user user' : Address)
    (epoch epoch' amount : Uint256) (h : user' ≠ user ∨ epoch' ≠ epoch) :
    (Verity.bind (HashedMappingExecSmoke.setRequest user epoch amount)
      fun _ => HashedMappingExecSmoke.requestOf user' epoch').run s =
    ContractResult.success (s.readMapChain 226 [user'.toNat, epoch'.val] 0)
      (s.writeMapChain 226 [user.toNat, epoch.val] 0 amount) := by
  have hne : ¬ (user' = user ∧ epoch' = epoch) := by
    rintro ⟨rfl, rfl⟩; rcases h with h | h <;> exact h rfl
  simp [HashedMappingExecSmoke.setRequest, HashedMappingExecSmoke.requestOf,
    HashedMappingExecSmoke.withdrawsRequestsByEpoch, Contract.run, Bind.bind, Pure.pure,
    Verity.bind, Verity.pure, setMappingN, getMappingN, hne]

/-- Mapping-vs-scalar separation: a nested-mapping write leaves the plain scalar
slot 206 (and every other scalar slot) untouched. Unprovable when the entry
lived in `.slot` at its keccak slot. -/
theorem setRequest_leaves_scalar (s : ContractState) (user : Address) (epoch amount : Uint256)
    (n : Nat) :
    ((HashedMappingExecSmoke.setRequest user epoch amount).run s).getState.storage n =
      s.storage n := by
  simp [HashedMappingExecSmoke.setRequest, HashedMappingExecSmoke.withdrawsRequestsByEpoch,
    Contract.run, setMappingN, ContractResult.getState]

/-- ... and a scalar write at slot 206 leaves every hashed entry untouched. -/
theorem requestOf_after_setWithdrawn (s : ContractState) (user : Address)
    (epoch amount : Uint256) :
    (Verity.bind (HashedMappingExecSmoke.setWithdrawn amount)
      fun _ => HashedMappingExecSmoke.requestOf user epoch).run s =
    ContractResult.success (s.readMapChain 226 [user.toNat, epoch.val] 0)
      (s.writeSlot 206 amount) := by
  simp [HashedMappingExecSmoke.setWithdrawn, HashedMappingExecSmoke.requestOf,
    HashedMappingExecSmoke.withdrawsRequestsByEpoch, HashedMappingExecSmoke.withdrawn,
    Contract.run, Bind.bind, Pure.pure, Verity.bind, Verity.pure, getMappingN,
    Verity.setStorage]

/-- `acquire` writes the transient channel only: persistent storage and persistent
hashed entries are untouched. -/
theorem acquire_leaves_storage (s : ContractState) (lockId : Bytes32) (n : Nat)
    (base : Nat) (keys : List Nat) (offset : Nat) :
    ∀ s', (HashedMappingExecSmoke.acquire lockId).run s = ContractResult.success () s' →
      s'.storage n = s.storage n ∧
        s'.readMapChain base keys offset = s.readMapChain base keys offset := by
  intro s' h
  simp [HashedMappingExecSmoke.acquire, HashedMappingExecSmoke.locks, Contract.run,
    setTransientMappingN] at h
  subst h
  simp

/-- `locked` reads back what `acquire` wrote. -/
theorem locked_after_acquire (s : ContractState) (lockId : Bytes32) :
    (Verity.bind (HashedMappingExecSmoke.acquire lockId)
      fun _ => HashedMappingExecSmoke.locked lockId).run s =
    ContractResult.success 1 (s.writeTransientMapChain 1 [lockId.val] 1) := by
  simp [HashedMappingExecSmoke.acquire, HashedMappingExecSmoke.locked,
    HashedMappingExecSmoke.locks, Contract.run, Bind.bind, Pure.pure, Verity.bind, Verity.pure,
    setTransientMappingN, getTransientMappingN]

/-- `structMembers` destructuring reads the struct words written by `setReceipt`;
adjacent members are distinct entries by word offset. -/
theorem receiptOf_after_setReceipt (s : ContractState) (user : Address) (principal epoch : Uint256) :
    (Verity.bind (HashedMappingExecSmoke.setReceipt user principal epoch)
      fun _ => HashedMappingExecSmoke.receiptOf user).run s =
    ContractResult.success (principal, epoch)
      ((s.writeMapChain 219 [user.toNat] 0 principal).writeMapChain 219 [user.toNat] 1 epoch) := by
  simp [HashedMappingExecSmoke.setReceipt, HashedMappingExecSmoke.receiptOf,
    HashedMappingExecSmoke.structMember, HashedMappingExecSmoke.setStructMember,
    Contract.run, Bind.bind, Pure.pure, Verity.bind, Verity.pure, structMemberAt,
    setStructMemberAt]

/-- Struct writes leave the nested mapping and the scalar slot untouched. -/
theorem setReceipt_leaves_request_and_scalar (s : ContractState) (user user' : Address)
    (principal epoch epoch' : Uint256) (n : Nat) :
    let s' := ((HashedMappingExecSmoke.setReceipt user principal epoch).run s).getState
    s'.readMapChain 226 [user'.toNat, epoch'.val] 0 = s.readMapChain 226 [user'.toNat, epoch'.val] 0 ∧
      s'.storage n = s.storage n := by
  simp [HashedMappingExecSmoke.setReceipt, HashedMappingExecSmoke.setStructMember,
    Contract.run, Bind.bind, Verity.bind, setStructMemberAt, ContractResult.getState]

/-- Hop frame: a distinct-address callee running `setRequest` writes its own
namespaced entry; the caller's entries are unchanged after the hop. -/
theorem hop_setRequest_frame (s : ContractState) (callee user : Address)
    (epoch amount : Uint256) (h : s.thisAddress ≠ callee) (keys : List Nat) (offset : Nat) :
    (Contract.hopCall callee (HashedMappingExecSmoke.setRequest user epoch amount) s).getState.readMapChain
        226 keys offset = s.readMapChain 226 keys offset := by
  rw [Contract.hopCall_of_ne _ _ _ h]
  simp only [HashedMappingExecSmoke.setRequest, HashedMappingExecSmoke.withdrawsRequestsByEpoch,
    setMappingN, ContractResult.getState]
  exact ContractState.readMapChain_exitHop_enterHop_of_frame _ _ _ _ _ _ _
    (ContractState.storageWords_scoped_writeMapChain _ _ _ _ _ _ _)

end Contracts.Smoke
