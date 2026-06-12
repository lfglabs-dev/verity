import Contracts.Smoke.Effects

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Every contract emits a storageNamespace : Nat definition (#1730, Axis 4 Step 4a).
-- Verify a few representative contracts have it and it is a Nat.
example : Contracts.Counter.storageNamespace = Contracts.Counter.storageNamespace := rfl
example : NewtypeSmoke.storageNamespace = NewtypeSmoke.storageNamespace := rfl

-- Namespaced storage smoke test (#1730, Axis 4 Step 4b).
-- When `storage_namespace` is present, user-declared slot numbers are offset
-- by keccak256("{ContractName}.storage.v0") so different contracts never collide.
verity_contract NamespacedStorageSmoke where
  storage_namespace
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function deposit (amount : Uint256) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function getOwner () : Address := do
    let addr ← getStorageAddr owner
    return addr

#check_contract NamespacedStorageSmoke

-- Verify that NamespacedStorageSmoke's storage slots differ from
-- non-namespaced contracts: slot 0 is offset by the namespace base.
-- The slot values embed the keccak-based namespace offset.
example : NamespacedStorageSmoke.balance.slot ≠ 0 := by decide
example : NamespacedStorageSmoke.owner.slot ≠ 1 := by decide

-- Verify storageNamespace flows into the CompilationModel spec (#1730, Axis 4 Step 4d).
-- Namespaced contracts carry `some ns`; non-namespaced carry `none`.
example : NamespacedStorageSmoke.spec.storageNamespace.isSome = true := rfl
example : Contracts.Counter.spec.storageNamespace.isNone = true := rfl

-- Custom namespace override (#1730, Axis 4 Step 4c)
-- Uses `storage_namespace "custom.v0"` instead of the default contract-name-based key.
-- The keccak256 is computed on the literal string "custom.v0".
verity_contract CustomNamespacedSmoke where
  storage_namespace "custom.v0"
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  function deposit (amount : Uint256) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function getOwner () : Address := do
    let addr ← getStorageAddr owner
    return addr

#check_contract CustomNamespacedSmoke

-- Verify custom namespace: slots are offset (nonzero) and differ from the
-- default-namespaced contract (which uses keccak256("NamespacedStorageSmoke.storage.v0")).
example : CustomNamespacedSmoke.balance.slot ≠ 0 := by decide
example : CustomNamespacedSmoke.owner.slot ≠ 1 := by decide
example : CustomNamespacedSmoke.balance.slot ≠ NamespacedStorageSmoke.balance.slot := by decide
example : CustomNamespacedSmoke.spec.storageNamespace.isSome = true := rfl
-- Verify the exported storageNamespace constant matches the spec value (not the default contract name hash).
example : CustomNamespacedSmoke.storageNamespace = CustomNamespacedSmoke.spec.storageNamespace.get! := rfl
example : CustomNamespacedSmoke.storageNamespace = 105542539407630759878214364786123406227647255732885741380220581264062975076298 := rfl
example : CustomNamespacedSmoke.storageNamespace ≠ 67387409610395734986217237394999073412260967828994783805404864304835768435504 := by decide

-- Automatic default namespace policy (#1896). Existing modules keep legacy
-- slot layout unless they opt in with this option; once enabled, omitting an
-- explicit `storage_namespace` derives the stable contract-name namespace.
set_option verity.storageNamespace.default true in
verity_contract DefaultNamespacedStorageSmoke where
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  function write (amount : Uint256, newOwner : Address) : Unit := do
    setStorage balance amount
    setStorageAddr owner newOwner

#check_contract DefaultNamespacedStorageSmoke

example : DefaultNamespacedStorageSmoke.balance.slot ≠ 0 := by decide
example : DefaultNamespacedStorageSmoke.owner.slot ≠ 1 := by decide
example : DefaultNamespacedStorageSmoke.spec.storageNamespace.isSome = true := rfl
example : DefaultNamespacedStorageSmoke.balance.slot =
    DefaultNamespacedStorageSmoke.storageNamespace := rfl
example : DefaultNamespacedStorageSmoke.owner.slot =
    DefaultNamespacedStorageSmoke.storageNamespace + 1 := rfl

-- Explicit keys override the automatic default namespace policy.
set_option verity.storageNamespace.default true in
verity_contract DefaultNamespaceOverrideSmoke where
  storage_namespace "override.namespace.v0"
  storage
    balance : Uint256 := slot 0

  function write (amount : Uint256) : Unit := do
    setStorage balance amount

#check_contract DefaultNamespaceOverrideSmoke

example :
    DefaultNamespaceOverrideSmoke.storageNamespace =
      DefaultNamespaceOverrideSmoke.spec.storageNamespace.get! := rfl
example : DefaultNamespaceOverrideSmoke.balance.slot =
    DefaultNamespaceOverrideSmoke.storageNamespace := rfl
example :
    DefaultNamespaceOverrideSmoke.storageNamespace ≠
      DefaultNamespacedStorageSmoke.storageNamespace := by
  decide

-- `storage_namespace legacy` is the compatibility escape hatch when the
-- automatic policy is enabled for a file but a specific contract must retain
-- historical raw slots.
set_option verity.storageNamespace.default true in
verity_contract DefaultNamespaceLegacyOptOutSmoke where
  storage_namespace legacy
  storage
    balance : Uint256 := slot 0
    owner : Address := slot 1

  function write (amount : Uint256, newOwner : Address) : Unit := do
    setStorage balance amount
    setStorageAddr owner newOwner

#check_contract DefaultNamespaceLegacyOptOutSmoke

example : DefaultNamespaceLegacyOptOutSmoke.balance.slot = 0 := rfl
example : DefaultNamespaceLegacyOptOutSmoke.owner.slot = 1 := rfl
example : DefaultNamespaceLegacyOptOutSmoke.spec.storageNamespace.isNone = true := rfl

-- Multiple namespace roots in one contract. Each `storage_namespace` item
-- inside the storage block applies to subsequent fields until the next item.
verity_contract MultiNamespaceStorageSmoke where
  storage
    storage_namespace erc7201 "unlink.storage.State"
    stateMerkleRoot : Uint256 := slot 0
    stateVerifierRouter : Address := slot 4
    storage_namespace erc7201 "unlink.storage.UnlinkPoolRelayers"
    relayersSlot : Address → Uint256 := slot 0

  function writeState (root : Uint256, router : Address) : Unit := do
    setStorage stateMerkleRoot root
    setStorageAddr stateVerifierRouter router

  function readStateRoot () : Uint256 := do
    let value ← getStorage stateMerkleRoot
    return value

  function readRelayer (account : Address) : Uint256 := do
    let enabled ← getMapping relayersSlot account
    return enabled

#check_contract MultiNamespaceStorageSmoke

example : MultiNamespaceStorageSmoke.stateMerkleRoot.slot =
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000 := by decide
example : MultiNamespaceStorageSmoke.stateVerifierRouter.slot =
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb004 := by decide
example : MultiNamespaceStorageSmoke.relayersSlot.slot =
    0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00 := by decide
example : MultiNamespaceStorageSmoke.stateMerkleRoot.slot ≠ MultiNamespaceStorageSmoke.relayersSlot.slot := by decide
example : MultiNamespaceStorageSmoke.spec.storageNamespace.isSome = true := rfl

-- Regression for the Bugbot review on PR #1971: when
-- `verity.storageNamespace.default` is enabled and the storage block opens
-- with an explicit `storage_namespace` directive (no contract-level
-- `storage_namespace`), the reported `spec.storageNamespace` must be the
-- in-storage root (the one the first field actually lives under), not the
-- provisional auto-default contract-name root.
set_option verity.storageNamespace.default true in
verity_contract DefaultNamespaceInStorageOverrideSmoke where
  storage
    storage_namespace erc7201 "unlink.storage.State"
    stateMerkleRoot : Uint256 := slot 0

  function writeRoot (root : Uint256) : Unit := do
    setStorage stateMerkleRoot root

#check_contract DefaultNamespaceInStorageOverrideSmoke

example :
    DefaultNamespaceInStorageOverrideSmoke.stateMerkleRoot.slot =
      0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000 := by decide
example :
    DefaultNamespaceInStorageOverrideSmoke.spec.storageNamespace =
      some 0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000 := by decide
-- The auto-default would have used the keccak of "DefaultNamespaceInStorageOverrideSmoke.storage.v0";
-- check the in-storage root replaced it instead of co-existing.
example :
    DefaultNamespaceInStorageOverrideSmoke.spec.storageNamespace ≠
      some (Verity.keccak256_nat "DefaultNamespaceInStorageOverrideSmoke.storage.v0") := by
  native_decide

end Contracts.Smoke
