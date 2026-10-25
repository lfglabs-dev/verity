/-
  Shared helpers for specs.

  Keep specs human-friendly by naming the common "unchanged" clauses
  instead of repeating field-by-field equality.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Specs

open Verity
open Verity.EVM.Uint256

/-- Contract context (sender, address, msg value, self balance, timestamp, block number, chain id, blob base fee, calldata size) is unchanged. -/
def sameContext (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.selfBalance = s.selfBalance ∧
  s'.blockTimestamp = s.blockTimestamp ∧
  s'.blockNumber = s.blockNumber ∧
  s'.chainId = s.chainId ∧
  s'.blobBaseFee = s.blobBaseFee ∧
  s'.calldataSize = s.calldataSize

@[simp] theorem sameContext_rfl (s : ContractState) : sameContext s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Uint256 storage is unchanged. -/
def sameStorage (s s' : ContractState) : Prop :=
  s'.storage = s.storage

@[simp] theorem sameStorage_rfl (s : ContractState) : sameStorage s s := rfl

/-- One Uint256 storage slot is unchanged. -/
def sameStorageSlot (slot : Nat) (s s' : ContractState) : Prop :=
  s'.storage slot = s.storage slot

@[simp] theorem sameStorageSlot_rfl (slot : Nat) (s : ContractState) :
    sameStorageSlot slot s s := rfl

/-- Address storage is unchanged. -/
def sameStorageAddr (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

@[simp] theorem sameStorageAddr_rfl (s : ContractState) : sameStorageAddr s s := rfl

/-- One address storage slot is unchanged. -/
def sameStorageAddrSlot (slot : Nat) (s s' : ContractState) : Prop :=
  s'.storageAddr slot = s.storageAddr slot

@[simp] theorem sameStorageAddrSlot_rfl (slot : Nat) (s : ContractState) :
    sameStorageAddrSlot slot s s := rfl

/-- Mapping storage is unchanged. -/
def sameStorageMap (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

@[simp] theorem sameStorageMap_rfl (s : ContractState) : sameStorageMap s s := rfl

/-- Uint256-keyed mapping storage is unchanged. -/
def sameStorageMapUint (s s' : ContractState) : Prop :=
  s'.storageMapUint = s.storageMapUint

@[simp] theorem sameStorageMapUint_rfl (s : ContractState) : sameStorageMapUint s s := rfl

/-- Double mapping storage is unchanged. -/
def sameStorageMap2 (s s' : ContractState) : Prop :=
  s'.storageMap2 = s.storageMap2

@[simp] theorem sameStorageMap2_rfl (s : ContractState) : sameStorageMap2 s s := rfl

/-- Dynamic-array storage is unchanged. -/
def sameStorageArray (s s' : ContractState) : Prop :=
  s'.storageArray = s.storageArray

@[simp] theorem sameStorageArray_rfl (s : ContractState) : sameStorageArray s s := rfl

/-- Event log is unchanged. -/
def sameEvents (s s' : ContractState) : Prop :=
  s'.events = s.events

@[simp] theorem sameEvents_rfl (s : ContractState) : sameEvents s s := rfl

/-- Known addresses tracking is unchanged. -/
def sameKnownAddresses (s s' : ContractState) : Prop :=
  s'.knownAddresses = s.knownAddresses

@[simp] theorem sameKnownAddresses_rfl (s : ContractState) : sameKnownAddresses s s := rfl

/-- Address storage, mapping storage, and context are unchanged. -/
def sameAddrMapContext (s s' : ContractState) : Prop :=
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameAddrMapContext_rfl (s : ContractState) : sameAddrMapContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, mapping storage, and context are unchanged. -/
def sameStorageMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMapContext_rfl (s : ContractState) : sameStorageMapContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, address storage, and context are unchanged. -/
def sameStorageAddrContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrContext_rfl (s : ContractState) : sameStorageAddrContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage, double-mapping storage, and context are unchanged. -/
def sameStorageMap2Context (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMap2Context_rfl (s : ContractState) : sameStorageMap2Context s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage and context are unchanged. -/
def sameMapContext (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameMapContext_rfl (s : ContractState) : sameMapContext s s :=
  ⟨rfl, rfl, sameContext_rfl s⟩

/-- One address slot and context are unchanged. -/
def sameStorageAddrSlotContext (addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageAddrSlot addrSlot s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrSlotContext_rfl (addrSlot : Nat) (s : ContractState) :
    sameStorageAddrSlotContext addrSlot s s :=
  ⟨rfl, sameContext_rfl s⟩

/-- One address slot, double-mapping storage, and context are unchanged. -/
def sameStorageAddrSlotMap2Context (addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageAddrSlot addrSlot s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrSlotMap2Context_rfl (addrSlot : Nat) (s : ContractState) :
    sameStorageAddrSlotMap2Context addrSlot s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- One Uint256 slot, one address slot, double-mapping storage, and context are unchanged. -/
def sameStorageSlotAddrSlotMap2Context
    (storageSlot addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageSlot storageSlot s s' ∧
  sameStorageAddrSlot addrSlot s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageSlotAddrSlotMap2Context_rfl
    (storageSlot addrSlot : Nat) (s : ContractState) :
    sameStorageSlotAddrSlotMap2Context storageSlot addrSlot s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, address storage, mapping storage, and context are unchanged. -/
def sameStorageAddrMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrMapContext_rfl (s : ContractState) : sameStorageAddrMapContext s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256/address storage, mapping storage (word+uint-keyed), and context are unchanged. -/
def sameStorageAddrMapUintContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrMapUintContext_rfl (s : ContractState) : sameStorageAddrMapUintContext s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage (word + uint-keyed + double), and context are unchanged. -/
def sameStorageMapsContext (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMapsContext_rfl (s : ContractState) : sameStorageMapsContext s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- All storage slots except `slot` are unchanged. -/
def storageUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storage other = s.storage other

/-- All address storage slots except `slot` are unchanged. -/
def storageAddrUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storageAddr other = s.storageAddr other

/-- Canonical two-state spec shape for updating one `storage` slot. -/
def storageUpdateSpec
    (slot : Nat)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storage slot = value s ∧
  storageUnchangedExcept slot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot. -/
def storageAddrUpdateSpec
    (slot : Nat)
    (value : ContractState → Address)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr slot = value s ∧
  storageAddrUnchangedExcept slot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot and one `storage` slot. -/
def storageAddrStorageUpdateSpec
    (addrSlot storageSlot : Nat)
    (addrValue : ContractState → Address)
    (storageValue : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr addrSlot = addrValue s ∧
  s'.storage storageSlot = storageValue s ∧
  storageAddrUnchangedExcept addrSlot s s' ∧
  storageUnchangedExcept storageSlot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot and two `storage` slots. -/
def storageAddrStorage2UpdateSpec
    (addrSlot storageSlot1 storageSlot2 : Nat)
    (addrValue : ContractState → Address)
    (storageValue1 storageValue2 : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr addrSlot = addrValue s ∧
  s'.storage storageSlot1 = storageValue1 s ∧
  s'.storage storageSlot2 = storageValue2 s ∧
  storageAddrUnchangedExcept addrSlot s s' ∧
  (∀ other : Nat, other ≠ storageSlot1 → other ≠ storageSlot2 → s'.storage other = s.storage other) ∧
  frame s s'

/-- Canonical two-state spec shape for updating two `storage` slots. -/
def storage2UpdateSpec
    (slot1 slot2 : Nat)
    (value1 value2 : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storage slot1 = value1 s ∧
  s'.storage slot2 = value2 s ∧
  (∀ other : Nat, other ≠ slot1 → other ≠ slot2 → s'.storage other = s.storage other) ∧
  frame s s'

/-- All mapping storage slots except `slot` are unchanged. -/
def storageMapUnchangedExceptSlot (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → ∀ addr : Address, s'.storageMap other addr = s.storageMap other addr

/-- All mapping entries at `slot` except `addr` are unchanged. -/
def storageMapUnchangedExceptKey (slot : Nat) (addr : Address) (s s' : ContractState) : Prop :=
  ∀ other : Address, other ≠ addr → s'.storageMap slot other = s.storageMap slot other

/-- All mapping entries at `slot` except `addr1` and `addr2` are unchanged. -/
def storageMapUnchangedExceptKeys (slot : Nat) (addr1 addr2 : Address) (s s' : ContractState) : Prop :=
  ∀ other : Address, other ≠ addr1 → other ≠ addr2 → s'.storageMap slot other = s.storageMap slot other

/-- Mapping storage is unchanged except at `slot` for key `addr`. -/
def storageMapUnchangedExceptKeyAtSlot (slot : Nat) (addr : Address) (s s' : ContractState) : Prop :=
  storageMapUnchangedExceptKey slot addr s s' ∧
  storageMapUnchangedExceptSlot slot s s'

/-- Mapping storage is unchanged except at `slot` for keys `addr1` and `addr2`. -/
def storageMapUnchangedExceptKeysAtSlot (slot : Nat) (addr1 addr2 : Address) (s s' : ContractState) : Prop :=
  storageMapUnchangedExceptKeys slot addr1 addr2 s s' ∧
  storageMapUnchangedExceptSlot slot s s'

/-- All double-mapping entries at `slot` are unchanged except possibly `(key1, key2)`. -/
def storageMap2UnchangedExceptKeyPair
    (slot : Nat) (key1 key2 : Address) (s s' : ContractState) : Prop :=
  (∀ k1' : Address, ∀ k2' : Address,
    k1' ≠ key1 → s'.storageMap2 slot k1' k2' = s.storageMap2 slot k1' k2') ∧
  (∀ k2' : Address,
    k2' ≠ key2 → s'.storageMap2 slot key1 k2' = s.storageMap2 slot key1 k2')

/-- Canonical two-state spec shape for updating one `storageMap` slot/key entry. -/
def storageMapUpdateSpec
    (slot : Nat)
    (key : Address)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap slot key = value s ∧
  storageMapUnchangedExceptKeyAtSlot slot key s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageMap` entry and one `storage` slot. -/
def storageMapAndStorageUpdateSpec
    (mapSlot : Nat)
    (key : Address)
    (mapValue : ContractState → Uint256)
    (storageSlot : Nat)
    (storageValue : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap mapSlot key = mapValue s ∧
  s'.storage storageSlot = storageValue s ∧
  storageMapUnchangedExceptKeyAtSlot mapSlot key s s' ∧
  storageUnchangedExcept storageSlot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageMap2` slot/key pair. -/
def storageMap2UpdateSpec
    (slot : Nat)
    (key1 key2 : Address)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap2 slot key1 key2 = value s ∧
  storageMap2UnchangedExceptKeyPair slot key1 key2 s s' ∧
  frame s s'

/-- Canonical two-state spec shape for transfer-style updates on one mapping slot.
When `from == to`, balances are unchanged; otherwise `from` is debited and `to` is credited. -/
@[simp]
def storageMapTransferSpec
    (slot : Nat)
    (fromAddr to : Address)
    (amount : Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  (if fromAddr == to
    then s'.storageMap slot fromAddr = s.storageMap slot fromAddr
    else s'.storageMap slot fromAddr = sub (s.storageMap slot fromAddr) amount) ∧
  (if fromAddr == to
    then s'.storageMap slot to = s.storageMap slot to
    else s'.storageMap slot to = add (s.storageMap slot to) amount) ∧
  (if fromAddr == to
    then storageMapUnchangedExceptKeyAtSlot slot fromAddr s s'
    else storageMapUnchangedExceptKeysAtSlot slot fromAddr to s s') ∧
  frame s s'

/-- Canonical two-state spec shape for ERC20-style `transferFrom` updates.
When `from == to`, balances are unchanged; otherwise `from` is debited and `to` is credited.
Allowance stays at `MAX_UINT256` or decreases by `amount` and all other allowance pairs are unchanged. -/
@[simp]
def storageMapTransferFromSpec
    (balanceSlot allowanceSlot : Nat)
    (fromAddr to spender : Address)
    (amount : Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  (if fromAddr == to
    then s'.storageMap balanceSlot fromAddr = s.storageMap balanceSlot fromAddr
    else s'.storageMap balanceSlot fromAddr = sub (s.storageMap balanceSlot fromAddr) amount) ∧
  (if fromAddr == to
    then s'.storageMap balanceSlot to = s.storageMap balanceSlot to
    else s'.storageMap balanceSlot to = add (s.storageMap balanceSlot to) amount) ∧
  (if fromAddr == to
    then storageMapUnchangedExceptKeyAtSlot balanceSlot fromAddr s s'
    else storageMapUnchangedExceptKeysAtSlot balanceSlot fromAddr to s s') ∧
  (if s.storageMap2 allowanceSlot fromAddr spender == Verity.EVM.MAX_UINT256
    then s'.storageMap2 allowanceSlot fromAddr spender = Verity.EVM.MAX_UINT256
    else s'.storageMap2 allowanceSlot fromAddr spender =
      sub (s.storageMap2 allowanceSlot fromAddr spender) amount) ∧
  storageMap2UnchangedExceptKeyPair allowanceSlot fromAddr spender s s' ∧
  frame s s'

/-- All storage (uint256, addr, map, mapUint, map2, array) is unchanged. -/
def sameAllStorage (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s'

@[simp] theorem sameAllStorage_rfl (s : ContractState) : sameAllStorage s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Everything except the event log is unchanged. -/
def sameExceptEvents (s s' : ContractState) : Prop :=
  sameAllStorage s s' ∧
  sameContext s s' ∧
  sameKnownAddresses s s'

@[simp] theorem sameExceptEvents_rfl (s : ContractState) : sameExceptEvents s s :=
  ⟨sameAllStorage_rfl s, sameContext_rfl s, rfl⟩

/-- Full state is unchanged — the frame condition for `view` functions.
    Covers all storage, context, events, and known-address tracking. -/
def viewPreservesState (s s' : ContractState) : Prop :=
  sameAllStorage s s' ∧
  sameContext s s' ∧
  sameEvents s s' ∧
  sameKnownAddresses s s'

@[simp] theorem viewPreservesState_rfl (s : ContractState) : viewPreservesState s s :=
  ⟨sameAllStorage_rfl s, sameContext_rfl s, rfl, rfl⟩

/-! ## Parametric Storage Keys (`SpecStorageKey`), `unchangedExcept`, and WP `FnSpec` -/

/-- Storage channel and slot identifier for parametric frame specifications (`unchangedExcept`). -/
inductive SpecStorageKey where
  | slot (idx : Nat)
  | addr (idx : Nat)
  | map (idx : Nat)
  | mapUint (idx : Nat)
  | map2 (idx : Nat)
  | array (idx : Nat)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a single `SpecStorageKey` is unchanged between `s` and `s'`. -/
@[simp] def SpecStorageKey.Preserved (k : SpecStorageKey) (s s' : ContractState) : Prop :=
  match k with
  | .slot idx => s'.storage idx = s.storage idx
  | .addr idx => s'.storageAddr idx = s.storageAddr idx
  | .map idx => s'.storageMap idx = s.storageMap idx
  | .mapUint idx => s'.storageMapUint idx = s.storageMapUint idx
  | .map2 idx => s'.storageMap2 idx = s.storageMap2 idx
  | .array idx => s'.storageArray idx = s.storageArray idx

@[simp] theorem SpecStorageKey.preserved_rfl (k : SpecStorageKey) (s : ContractState) :
    k.Preserved s s := by
  cases k <;> rfl

/-- Uniform conversion from slot descriptors (`SpecStorageKey`, raw `Nat`, or typed `StorageSlot`)
into `SpecStorageKey`. -/
class ToSpecStorageKey (α : Type) where
  toSpecStorageKey : α → SpecStorageKey

@[simp] instance : ToSpecStorageKey SpecStorageKey where
  toSpecStorageKey k := k

@[simp] instance : ToSpecStorageKey Nat where
  toSpecStorageKey idx := .slot idx

@[simp] instance : ToSpecStorageKey (StorageSlot Uint256) where
  toSpecStorageKey | ⟨idx⟩ => .slot idx

@[simp] instance : ToSpecStorageKey (StorageSlot Address) where
  toSpecStorageKey | ⟨idx⟩ => .addr idx

@[simp] instance : ToSpecStorageKey (StorageSlot (Address → Uint256)) where
  toSpecStorageKey | ⟨idx⟩ => .map idx

@[simp] instance : ToSpecStorageKey (StorageSlot (Uint256 → Uint256)) where
  toSpecStorageKey | ⟨idx⟩ => .mapUint idx

@[simp] instance : ToSpecStorageKey (StorageSlot (Address → Address → Uint256)) where
  toSpecStorageKey | ⟨idx⟩ => .map2 idx

@[simp] instance {α : Type} : ToSpecStorageKey (StorageSlot (List α)) where
  toSpecStorageKey | ⟨idx⟩ => .array idx

/-- Parametric frame condition: every storage channel/slot not listed in `writes`
(across `.slot`, `.addr`, `.map`, `.mapUint`, `.map2`, `.array`) and the contract
execution context (`sameContext`) are unchanged between `s` and `s'`. -/
def unchangedExcept (writes : List SpecStorageKey) (s s' : ContractState) : Prop :=
  (∀ idx, SpecStorageKey.slot idx ∉ writes → s'.storage idx = s.storage idx) ∧
  (∀ idx, SpecStorageKey.addr idx ∉ writes → s'.storageAddr idx = s.storageAddr idx) ∧
  (∀ idx, SpecStorageKey.map idx ∉ writes → s'.storageMap idx = s.storageMap idx) ∧
  (∀ idx, SpecStorageKey.mapUint idx ∉ writes → s'.storageMapUint idx = s.storageMapUint idx) ∧
  (∀ idx, SpecStorageKey.map2 idx ∉ writes → s'.storageMap2 idx = s.storageMap2 idx) ∧
  (∀ idx, SpecStorageKey.array idx ∉ writes → s'.storageArray idx = s.storageArray idx) ∧
  sameContext s s'

@[simp] theorem unchangedExcept_rfl (writes : List SpecStorageKey) (s : ContractState) :
    unchangedExcept writes s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl, sameContext_rfl s⟩

/-- Monotonicity of `unchangedExcept` under write-list inclusion (`writes₁ ⊆ writes₂`). -/
theorem unchangedExcept_subset {writes₁ writes₂ : List SpecStorageKey}
    {s s' : ContractState}
    (hsub : ∀ k, k ∈ writes₁ → k ∈ writes₂)
    (h : unchangedExcept writes₁ s s') :
    unchangedExcept writes₂ s s' := by
  rcases h with ⟨hslot, haddr, hmap, hmapu, hmap2, harr, hctx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hctx⟩
  · intro idx hnot; exact hslot idx (fun hm => hnot (hsub _ hm))
  · intro idx hnot; exact haddr idx (fun hm => hnot (hsub _ hm))
  · intro idx hnot; exact hmap idx (fun hm => hnot (hsub _ hm))
  · intro idx hnot; exact hmapu idx (fun hm => hnot (hsub _ hm))
  · intro idx hnot; exact hmap2 idx (fun hm => hnot (hsub _ hm))
  · intro idx hnot; exact harr idx (fun hm => hnot (hsub _ hm))

@[simp] theorem unchangedExcept_cons_of_unchangedExcept
    (k : SpecStorageKey) (writes : List SpecStorageKey) {s s' : ContractState}
    (h : unchangedExcept writes s s') :
    unchangedExcept (k :: writes) s s' :=
  unchangedExcept_subset (fun _ hm => List.mem_cons_of_mem k hm) h

theorem sameContext_trans {s₁ s₂ s₃ : ContractState}
    (h₁₂ : sameContext s₁ s₂) (h₂₃ : sameContext s₂ s₃) :
    sameContext s₁ s₃ := by
  rcases h₁₂ with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases h₂₃ with ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
  exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4, g5.trans h5,
         g6.trans h6, g7.trans h7, g8.trans h8, g9.trans h9⟩

/-- Transitivity of `unchangedExcept` for a fixed write set `writes`. -/
theorem unchangedExcept_trans {writes : List SpecStorageKey}
    {s₁ s₂ s₃ : ContractState}
    (h₁₂ : unchangedExcept writes s₁ s₂)
    (h₂₃ : unchangedExcept writes s₂ s₃) :
    unchangedExcept writes s₁ s₃ := by
  rcases h₁₂ with ⟨hslot₁, haddr₁, hmap₁, hmapu₁, hmap2₁, harr₁, hctx₁⟩
  rcases h₂₃ with ⟨hslot₂, haddr₂, hmap₂, hmapu₂, hmap2₂, harr₂, hctx₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_trans hctx₁ hctx₂⟩
  · intro idx hnot; exact (hslot₂ idx hnot).trans (hslot₁ idx hnot)
  · intro idx hnot; exact (haddr₂ idx hnot).trans (haddr₁ idx hnot)
  · intro idx hnot; exact (hmap₂ idx hnot).trans (hmap₁ idx hnot)
  · intro idx hnot; exact (hmapu₂ idx hnot).trans (hmapu₁ idx hnot)
  · intro idx hnot; exact (hmap2₂ idx hnot).trans (hmap2₁ idx hnot)
  · intro idx hnot; exact (harr₂ idx hnot).trans (harr₁ idx hnot)

/-- Characterization of `unchangedExcept` via `SpecStorageKey.Preserved`. -/
theorem unchangedExcept_iff_forall_key
    (writes : List SpecStorageKey) (s s' : ContractState) :
    unchangedExcept writes s s' ↔
      ((∀ k : SpecStorageKey, k ∉ writes → k.Preserved s s') ∧ sameContext s s') := by
  constructor
  · rintro ⟨hslot, haddr, hmap, hmapu, hmap2, harr, hctx⟩
    refine ⟨?_, hctx⟩
    intro k hnot
    cases k with
    | slot idx => exact hslot idx hnot
    | addr idx => exact haddr idx hnot
    | map idx => exact hmap idx hnot
    | mapUint idx => exact hmapu idx hnot
    | map2 idx => exact hmap2 idx hnot
    | array idx => exact harr idx hnot
  · rintro ⟨hall, hctx⟩
    exact ⟨fun idx hnot => hall (.slot idx) hnot,
           fun idx hnot => hall (.addr idx) hnot,
           fun idx hnot => hall (.map idx) hnot,
           fun idx hnot => hall (.mapUint idx) hnot,
           fun idx hnot => hall (.map2 idx) hnot,
           fun idx hnot => hall (.array idx) hnot,
           hctx⟩

theorem unchangedExcept.sameContext {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') : sameContext s s' :=
  h.2.2.2.2.2.2

theorem unchangedExcept.sameStorageSlot {writes : List SpecStorageKey} {s s' : ContractState}
    {idx : Nat} (h : unchangedExcept writes s s') (hnot : SpecStorageKey.slot idx ∉ writes) :
    sameStorageSlot idx s s' :=
  h.1 idx hnot

theorem unchangedExcept.sameStorageAddrSlot {writes : List SpecStorageKey} {s s' : ContractState}
    {idx : Nat} (h : unchangedExcept writes s s') (hnot : SpecStorageKey.addr idx ∉ writes) :
    sameStorageAddrSlot idx s s' :=
  h.2.1 idx hnot

theorem unchangedExcept.sameStorage_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.slot idx ∉ writes) :
    sameStorage s s' := by
  funext idx
  exact h.1 idx (hnot idx)

theorem unchangedExcept.sameStorageAddr_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.addr idx ∉ writes) :
    sameStorageAddr s s' := by
  funext idx
  exact h.2.1 idx (hnot idx)

theorem unchangedExcept.sameStorageMap_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.map idx ∉ writes) :
    sameStorageMap s s' := by
  funext idx
  exact h.2.2.1 idx (hnot idx)

theorem unchangedExcept.sameStorageMapUint_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.mapUint idx ∉ writes) :
    sameStorageMapUint s s' := by
  funext idx
  exact h.2.2.2.1 idx (hnot idx)

theorem unchangedExcept.sameStorageMap2_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.map2 idx ∉ writes) :
    sameStorageMap2 s s' := by
  funext idx
  exact h.2.2.2.2.1 idx (hnot idx)

theorem unchangedExcept.sameStorageArray_of_not_mem {writes : List SpecStorageKey} {s s' : ContractState}
    (h : unchangedExcept writes s s') (hnot : ∀ idx, SpecStorageKey.array idx ∉ writes) :
    sameStorageArray s s' := by
  funext idx
  exact h.2.2.2.2.2.1 idx (hnot idx)

@[simp] theorem unchangedExcept_nil (s s' : ContractState) :
    unchangedExcept [] s s' ↔ (sameAllStorage s s' ∧ sameContext s s') := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h.sameContext⟩
    · exact h.sameStorage_of_not_mem (by simp)
    · exact h.sameStorageAddr_of_not_mem (by simp)
    · exact h.sameStorageMap_of_not_mem (by simp)
    · exact h.sameStorageMapUint_of_not_mem (by simp)
    · exact h.sameStorageMap2_of_not_mem (by simp)
    · exact h.sameStorageArray_of_not_mem (by simp)
  · rintro ⟨⟨hst, haddr, hmap, hmapu, hmap2, harr⟩, hctx⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hctx⟩
    · intro idx _; exact congrFun hst idx
    · intro idx _; exact congrFun haddr idx
    · intro idx _; exact congrFun hmap idx
    · intro idx _; exact congrFun hmapu idx
    · intro idx _; exact congrFun hmap2 idx
    · intro idx _; exact congrFun harr idx

/-! ### Bridge Lemmas to `same*Context` and `*UnchangedExcept*` -/

theorem unchangedExcept_singleton_slot_iff (slot : Nat) (s s' : ContractState) :
    unchangedExcept [.slot slot] s s' ↔
      (storageUnchangedExcept slot s s' ∧
       sameAddrMapContext s s' ∧
       sameStorageMapUint s s' ∧
       sameStorageMap2 s s') := by
  constructor
  · intro h
    refine ⟨?_, ⟨?_, ?_, ?_, h.sameContext⟩, ?_, ?_⟩
    · intro other hne
      exact h.1 other (by simp [hne])
    · exact h.sameStorageAddr_of_not_mem (by simp)
    · exact h.sameStorageMap_of_not_mem (by simp)
    · exact h.sameStorageArray_of_not_mem (by simp)
    · exact h.sameStorageMapUint_of_not_mem (by simp)
    · exact h.sameStorageMap2_of_not_mem (by simp)
  · rintro ⟨hslot, ⟨haddr, hmap, harr, hctx⟩, hmapu, hmap2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hctx⟩
    · intro idx hnot
      exact hslot idx (by simpa using hnot)
    · intro idx _; exact congrFun haddr idx
    · intro idx _; exact congrFun hmap idx
    · intro idx _; exact congrFun hmapu idx
    · intro idx _; exact congrFun hmap2 idx
    · intro idx _; exact congrFun harr idx

theorem unchangedExcept.to_storageUnchangedExcept {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.slot slot] s s') :
    storageUnchangedExcept slot s s' :=
  (unchangedExcept_singleton_slot_iff slot s s').mp h |>.1

theorem unchangedExcept.to_sameAddrMapContext {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.slot slot] s s') :
    sameAddrMapContext s s' :=
  (unchangedExcept_singleton_slot_iff slot s s').mp h |>.2.1

theorem unchangedExcept_singleton_addr_iff (slot : Nat) (s s' : ContractState) :
    unchangedExcept [.addr slot] s s' ↔
      (storageAddrUnchangedExcept slot s s' ∧
       sameStorageMapContext s s' ∧
       sameStorageMapUint s s' ∧
       sameStorageMap2 s s') := by
  constructor
  · intro h
    refine ⟨?_, ⟨?_, ?_, ?_, h.sameContext⟩, ?_, ?_⟩
    · intro other hne
      exact h.2.1 other (by simp [hne])
    · exact h.sameStorage_of_not_mem (by simp)
    · exact h.sameStorageMap_of_not_mem (by simp)
    · exact h.sameStorageArray_of_not_mem (by simp)
    · exact h.sameStorageMapUint_of_not_mem (by simp)
    · exact h.sameStorageMap2_of_not_mem (by simp)
  · rintro ⟨haddr, ⟨hst, hmap, harr, hctx⟩, hmapu, hmap2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hctx⟩
    · intro idx _; exact congrFun hst idx
    · intro idx hnot
      exact haddr idx (by simpa using hnot)
    · intro idx _; exact congrFun hmap idx
    · intro idx _; exact congrFun hmapu idx
    · intro idx _; exact congrFun hmap2 idx
    · intro idx _; exact congrFun harr idx

theorem unchangedExcept.to_storageAddrUnchangedExcept {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.addr slot] s s') :
    storageAddrUnchangedExcept slot s s' :=
  (unchangedExcept_singleton_addr_iff slot s s').mp h |>.1

theorem unchangedExcept.to_sameStorageMapContext {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.addr slot] s s') :
    sameStorageMapContext s s' :=
  (unchangedExcept_singleton_addr_iff slot s s').mp h |>.2.1

theorem unchangedExcept_singleton_map_iff (slot : Nat) (s s' : ContractState) :
    unchangedExcept [.map slot] s s' ↔
      (storageMapUnchangedExceptSlot slot s s' ∧
       sameStorageAddrContext s s' ∧
       sameStorageMapUint s s' ∧
       sameStorageMap2 s s') := by
  constructor
  · intro h
    refine ⟨?_, ⟨?_, ?_, ?_, h.sameContext⟩, ?_, ?_⟩
    · intro other hne addr
      exact congrFun (h.2.2.1 other (by simp [hne])) addr
    · exact h.sameStorage_of_not_mem (by simp)
    · exact h.sameStorageAddr_of_not_mem (by simp)
    · exact h.sameStorageArray_of_not_mem (by simp)
    · exact h.sameStorageMapUint_of_not_mem (by simp)
    · exact h.sameStorageMap2_of_not_mem (by simp)
  · rintro ⟨hmap, ⟨hst, haddr, harr, hctx⟩, hmapu, hmap2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hctx⟩
    · intro idx _; exact congrFun hst idx
    · intro idx _; exact congrFun haddr idx
    · intro idx hnot
      funext addr
      exact hmap idx (by simpa using hnot) addr
    · intro idx _; exact congrFun hmapu idx
    · intro idx _; exact congrFun hmap2 idx
    · intro idx _; exact congrFun harr idx

theorem unchangedExcept.to_storageMapUnchangedExceptSlot {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.map slot] s s') :
    storageMapUnchangedExceptSlot slot s s' :=
  (unchangedExcept_singleton_map_iff slot s s').mp h |>.1

theorem unchangedExcept.to_sameStorageAddrContext {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.map slot] s s') :
    sameStorageAddrContext s s' :=
  (unchangedExcept_singleton_map_iff slot s s').mp h |>.2.1

theorem unchangedExcept.to_sameStorageAddrMapContext {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.map2 slot] s s') :
    sameStorageAddrMapContext s s' :=
  ⟨h.sameStorage_of_not_mem (by simp),
   h.sameStorageAddr_of_not_mem (by simp),
   h.sameStorageMap_of_not_mem (by simp),
   h.sameStorageArray_of_not_mem (by simp),
   h.sameContext⟩

theorem unchangedExcept.to_sameStorageAddrMapUintContext {slot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.map2 slot] s s') :
    sameStorageAddrMapUintContext s s' :=
  ⟨h.sameStorage_of_not_mem (by simp),
   h.sameStorageAddr_of_not_mem (by simp),
   h.sameStorageMap_of_not_mem (by simp),
   h.sameStorageMapUint_of_not_mem (by simp),
   h.sameStorageArray_of_not_mem (by simp),
   h.sameContext⟩

theorem unchangedExcept.to_sameStorageMap2Context {addrSlot storageSlot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.addr addrSlot, .slot storageSlot] s s') :
    sameStorageMap2Context s s' :=
  ⟨h.sameStorageMap_of_not_mem (by simp),
   h.sameStorageMap2_of_not_mem (by simp),
   h.sameStorageArray_of_not_mem (by simp),
   h.sameContext⟩

theorem unchangedExcept.to_sameStorageMapsContext {addrSlot storageSlot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.addr addrSlot, .slot storageSlot] s s') :
    sameStorageMapsContext s s' :=
  ⟨h.sameStorageMap_of_not_mem (by simp),
   h.sameStorageMapUint_of_not_mem (by simp),
   h.sameStorageMap2_of_not_mem (by simp),
   h.sameStorageArray_of_not_mem (by simp),
   h.sameContext⟩

theorem unchangedExcept.to_sameMapContext {addrSlot storageSlot : Nat} {s s' : ContractState}
    (h : unchangedExcept [.addr addrSlot, .slot storageSlot] s s') :
    sameMapContext s s' :=
  ⟨h.sameStorageMap_of_not_mem (by simp),
   h.sameStorageArray_of_not_mem (by simp),
   h.sameContext⟩

/-! ### Compositional `[simp]` Lemmas for `ContractState` Writes under `unchangedExcept` -/

@[simp] theorem unchangedExcept_with_events
    (writes : List SpecStorageKey) (s₀ s : ContractState) (ev : List Event) :
    unchangedExcept writes s₀ { s with events := ev } ↔ unchangedExcept writes s₀ s :=
  Iff.rfl

@[simp] theorem unchangedExcept_with_knownAddresses
    (writes : List SpecStorageKey) (s₀ s : ContractState)
    (ka : Nat → Verity.Core.FiniteAddressSet) :
    unchangedExcept writes s₀ { s with knownAddresses := ka } ↔ unchangedExcept writes s₀ s :=
  Iff.rfl

theorem unchangedExcept_writeSlot_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (val : Uint256)
    (hmem : SpecStorageKey.slot slot ∈ writes) :
    unchangedExcept writes s (s.writeSlot slot val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    simp [ContractState.storage, ContractState.writeSlot, hne]
  · intro idx _; simp
  · intro idx _; simp
  · intro idx _; simp
  · intro idx _; simp
  · intro idx _; simp

@[simp] theorem unchangedExcept_writeSlot_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (val : Uint256)
    (hmem : SpecStorageKey.slot slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeSlot slot val) :=
  unchangedExcept_trans h (unchangedExcept_writeSlot_self writes s slot val hmem)

theorem unchangedExcept_writeAddrSlot_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (val : Address)
    (hmem : SpecStorageKey.addr slot ∈ writes) :
    unchangedExcept writes s (s.writeAddrSlot slot val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx _; simp [ContractState.storage, ContractState.writeAddrSlot]
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    simp [ContractState.storageAddr, ContractState.writeAddrSlot, hne]
  · intro idx _; funext k; simp [ContractState.storageMap, ContractState.writeAddrSlot]
  · intro idx _; funext k; simp [ContractState.storageMapUint, ContractState.writeAddrSlot]
  · intro idx _; funext k1 k2; simp [ContractState.storageMap2, ContractState.writeAddrSlot]
  · intro idx _; rfl

@[simp] theorem unchangedExcept_writeAddrSlot_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (val : Address)
    (hmem : SpecStorageKey.addr slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeAddrSlot slot val) :=
  unchangedExcept_trans h (unchangedExcept_writeAddrSlot_self writes s slot val hmem)

theorem unchangedExcept_writeMap_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (key : Address) (val : Uint256)
    (hmem : SpecStorageKey.map slot ∈ writes) :
    unchangedExcept writes s (s.writeMap slot key val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx _; simp [ContractState.storage, ContractState.writeMap]
  · intro idx _; simp [ContractState.storageAddr, ContractState.writeMap]
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    funext k
    simp [ContractState.storageMap, ContractState.writeMap, hne]
  · intro idx _; funext k; simp [ContractState.storageMapUint, ContractState.writeMap]
  · intro idx _; funext k1 k2; simp [ContractState.storageMap2, ContractState.writeMap]
  · intro idx _; rfl

@[simp] theorem unchangedExcept_writeMap_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (key : Address) (val : Uint256)
    (hmem : SpecStorageKey.map slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeMap slot key val) :=
  unchangedExcept_trans h (unchangedExcept_writeMap_self writes s slot key val hmem)

theorem unchangedExcept_writeMapUint_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (key : Uint256) (val : Uint256)
    (hmem : SpecStorageKey.mapUint slot ∈ writes) :
    unchangedExcept writes s (s.writeMapUint slot key val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx _; simp [ContractState.storage, ContractState.writeMapUint]
  · intro idx _; simp [ContractState.storageAddr, ContractState.writeMapUint]
  · intro idx _; funext k; simp [ContractState.storageMap, ContractState.writeMapUint]
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    funext k
    simp [ContractState.storageMapUint, ContractState.writeMapUint, hne]
  · intro idx _; funext k1 k2; simp [ContractState.storageMap2, ContractState.writeMapUint]
  · intro idx _; rfl

@[simp] theorem unchangedExcept_writeMapUint_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (key : Uint256) (val : Uint256)
    (hmem : SpecStorageKey.mapUint slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeMapUint slot key val) :=
  unchangedExcept_trans h (unchangedExcept_writeMapUint_self writes s slot key val hmem)

theorem unchangedExcept_writeMap2_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (key1 key2 : Address) (val : Uint256)
    (hmem : SpecStorageKey.map2 slot ∈ writes) :
    unchangedExcept writes s (s.writeMap2 slot key1 key2 val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx _; simp
  · intro idx _; simp
  · intro idx _; simp
  · intro idx _; simp
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    funext k1 k2
    simp [ContractState.storageMap2, ContractState.writeMap2, hne]
  · intro idx _; rfl

@[simp] theorem unchangedExcept_writeMap2_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (key1 key2 : Address) (val : Uint256)
    (hmem : SpecStorageKey.map2 slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeMap2 slot key1 key2 val) :=
  unchangedExcept_trans h (unchangedExcept_writeMap2_self writes s slot key1 key2 val hmem)

theorem unchangedExcept_writeArray_self
    (writes : List SpecStorageKey) (s : ContractState) (slot : Nat) (vals : List Uint256)
    (hmem : SpecStorageKey.array slot ∈ writes) :
    unchangedExcept writes s (s.writeArray slot vals) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sameContext_rfl s⟩
  · intro idx _; rfl
  · intro idx _; rfl
  · intro idx _; rfl
  · intro idx _; rfl
  · intro idx _; rfl
  · intro idx hnot
    have hne : idx ≠ slot := fun heq => hnot (heq ▸ hmem)
    exact ContractState.storageArray_writeArray_other s hne vals

@[simp] theorem unchangedExcept_writeArray_of_mem
    (writes : List SpecStorageKey) (s₀ s : ContractState) (slot : Nat) (vals : List Uint256)
    (hmem : SpecStorageKey.array slot ∈ writes)
    (h : unchangedExcept writes s₀ s) :
    unchangedExcept writes s₀ (s.writeArray slot vals) :=
  unchangedExcept_trans h (unchangedExcept_writeArray_self writes s slot vals hmem)

/-- Unified parametric two-state specification combining a postcondition `post s s'`
with the parametric frame `unchangedExcept writes s s'`. -/
def fnUpdateSpec
    (writes : List SpecStorageKey)
    (post : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  post s s' ∧ unchangedExcept writes s s'

@[simp] theorem fnUpdateSpec_rfl
    (writes : List SpecStorageKey)
    (post : ContractState → ContractState → Prop)
    (s : ContractState) (hpost : post s s) :
    fnUpdateSpec writes post s s :=
  ⟨hpost, unchangedExcept_rfl writes s⟩

theorem fnUpdateSpec_implies_storageUpdateSpec
    (slot : Nat) (value : ContractState → Uint256) ( s s' : ContractState)
    (h : fnUpdateSpec [.slot slot] (fun st st' => st'.storage slot = value st) s s') :
    storageUpdateSpec slot value sameAddrMapContext s s' :=
  ⟨h.1, h.2.to_storageUnchangedExcept, h.2.to_sameAddrMapContext⟩

theorem fnUpdateSpec_implies_storageAddrUpdateSpec
    (slot : Nat) (value : ContractState → Address) (s s' : ContractState)
    (h : fnUpdateSpec [.addr slot] (fun st st' => st'.storageAddr slot = value st) s s') :
    storageAddrUpdateSpec slot value sameStorageMapContext s s' :=
  ⟨h.1, h.2.to_storageAddrUnchangedExcept, h.2.to_sameStorageMapContext⟩

/-! ### Weakest-Precondition `FnSpec` and `FnSpec.Satisfies` -/

/-- Unified weakest-precondition function specification over `Contract α`. -/
structure FnSpec (α : Type) where
  pre : Prop := True
  post : α → ContractState → Prop := fun _ _ => True
  events : α → List Event → Prop := fun _ _ => True
  writes : List SpecStorageKey := []

/-- Weakest-precondition satisfaction of `spec : FnSpec α` by `m : Contract α` from pre-state `s`:
on `.success v s'`, the precondition, postcondition, event specification, and `unchangedExcept`
frame all hold; on `.revert`, the precondition is false (`¬ spec.pre`). -/
def FnSpec.Satisfies {α : Type} (m : Contract α) (s : ContractState) (spec : FnSpec α) : Prop :=
  match m.run s with
  | .success v s' =>
      spec.pre ∧ spec.post v s' ∧ spec.events v s'.events ∧ unchangedExcept spec.writes s s'
  | .revert _ _ => ¬ spec.pre

@[simp] theorem FnSpec.satisfies_of_run_success {α : Type}
    {m : Contract α} {s s' : ContractState} {v : α} {spec : FnSpec α}
    (hrun : m.run s = .success v s') :
    FnSpec.Satisfies m s spec ↔
      (spec.pre ∧ spec.post v s' ∧ spec.events v s'.events ∧ unchangedExcept spec.writes s s') := by
  simp [FnSpec.Satisfies, hrun]

@[simp] theorem FnSpec.satisfies_of_run_revert {α : Type}
    {m : Contract α} {s s' : ContractState} {msg : String} {spec : FnSpec α}
    (hrun : m.run s = .revert msg s') :
    FnSpec.Satisfies m s spec ↔ ¬ spec.pre := by
  simp [FnSpec.Satisfies, hrun]

/-- **Total Equivalence Theorem (`FnSpec.Satisfies_iff_total`)**:
The single `match` characterization `FnSpec.Satisfies m s spec` is logically equivalent
to the conjunction of:
1. Precondition exactness (`(m.run s).isSuccess = true ↔ spec.pre`),
2. Postcondition, event specification, and `unchangedExcept` frame on `.success`, and
3. Revert completeness (`m.run s = .revert msg s' → ¬ spec.pre`). -/
theorem FnSpec.Satisfies_iff_total {α : Type}
    (m : Contract α) (s : ContractState) (spec : FnSpec α) :
    FnSpec.Satisfies m s spec ↔
      (((m.run s).isSuccess = true ↔ spec.pre) ∧
       (∀ v s', m.run s = .success v s' →
         spec.post v s' ∧ spec.events v s'.events ∧ unchangedExcept spec.writes s s') ∧
       (∀ msg s', m.run s = .revert msg s' → ¬ spec.pre)) := by
  unfold FnSpec.Satisfies
  cases hrun : m.run s with
  | success v s' =>
    constructor
    · rintro ⟨hpre, hpost, hev, hfr⟩
      refine ⟨⟨fun _ => hpre, fun _ => rfl⟩, ?_, ?_⟩
      · intro v' s'' heq
        cases heq
        exact ⟨hpost, hev, hfr⟩
      · intro _ _ heq
        cases heq
    · rintro ⟨hiff, hsucc, _⟩
      have hpre : spec.pre := hiff.mp rfl
      obtain ⟨hpost, hev, hfr⟩ := hsucc v s' rfl
      exact ⟨hpre, hpost, hev, hfr⟩
  | revert msg s' =>
    constructor
    · intro hnpre
      refine ⟨⟨fun h => (by cases h), fun hpre => False.elim (hnpre hpre)⟩, ?_, ?_⟩
      · intro _ _ heq
        cases heq
      · intro _ _ _
        exact hnpre
    · rintro ⟨_, _, hrev⟩
      exact hrev msg s' rfl

/-- Compact two-clause equivalence for `FnSpec.Satisfies`. -/
theorem FnSpec.Satisfies_iff {α : Type}
    (m : Contract α) (s : ContractState) (spec : FnSpec α) :
    FnSpec.Satisfies m s spec ↔
      (((m.run s).isSuccess = true ↔ spec.pre) ∧
       (∀ v s', m.run s = .success v s' →
         spec.post v s' ∧ spec.events v s'.events ∧ unchangedExcept spec.writes s s')) := by
  rw [FnSpec.Satisfies_iff_total]
  constructor
  · rintro ⟨h1, h2, _⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    intro msg s' hrev hpre
    have hsucc : (m.run s).isSuccess = true := h1.mpr hpre
    rw [hrev] at hsucc
    cases hsucc

theorem FnSpec.Satisfies.isSuccess_iff {α : Type}
    {m : Contract α} {s : ContractState} {spec : FnSpec α}
    (h : FnSpec.Satisfies m s spec) :
    (m.run s).isSuccess = true ↔ spec.pre :=
  ((FnSpec.Satisfies_iff_total m s spec).mp h).1

theorem FnSpec.Satisfies.post_of_success {α : Type}
    {m : Contract α} {s s' : ContractState} {v : α} {spec : FnSpec α}
    (h : FnSpec.Satisfies m s spec) (hrun : m.run s = .success v s') :
    spec.post v s' :=
  (((FnSpec.Satisfies_iff_total m s spec).mp h).2.1 v s' hrun).1

theorem FnSpec.Satisfies.events_of_success {α : Type}
    {m : Contract α} {s s' : ContractState} {v : α} {spec : FnSpec α}
    (h : FnSpec.Satisfies m s spec) (hrun : m.run s = .success v s') :
    spec.events v s'.events :=
  (((FnSpec.Satisfies_iff_total m s spec).mp h).2.1 v s' hrun).2.1

theorem FnSpec.Satisfies.frame_of_success {α : Type}
    {m : Contract α} {s s' : ContractState} {v : α} {spec : FnSpec α}
    (h : FnSpec.Satisfies m s spec) (hrun : m.run s = .success v s') :
    unchangedExcept spec.writes s s' :=
  (((FnSpec.Satisfies_iff_total m s spec).mp h).2.1 v s' hrun).2.2

theorem FnSpec.Satisfies.not_pre_of_revert {α : Type}
    {m : Contract α} {s s' : ContractState} {msg : String} {spec : FnSpec α}
    (h : FnSpec.Satisfies m s spec) (hrun : m.run s = .revert msg s') :
    ¬ spec.pre :=
  ((FnSpec.Satisfies_iff_total m s spec).mp h).2.2 msg s' hrun

/-- Monotonicity / weakening for `FnSpec.Satisfies`. -/
theorem FnSpec.Satisfies.weaken {α : Type}
    {m : Contract α} {s : ContractState} {spec₁ spec₂ : FnSpec α}
    (h : FnSpec.Satisfies m s spec₁)
    (hpre : spec₁.pre ↔ spec₂.pre)
    (hpost : ∀ v s', spec₁.post v s' → spec₂.post v s')
    (hev : ∀ v ev, spec₁.events v ev → spec₂.events v ev)
    (hwrites : ∀ k, k ∈ spec₁.writes → k ∈ spec₂.writes) :
    FnSpec.Satisfies m s spec₂ := by
  unfold FnSpec.Satisfies at h ⊢
  cases hrun : m.run s with
  | success v s' =>
    rw [hrun] at h
    rcases h with ⟨hp, hpo, he, hfr⟩
    exact ⟨hpre.mp hp, hpost v s' hpo, hev v s'.events he, unchangedExcept_subset hwrites hfr⟩
  | revert msg s' =>
    rw [hrun] at h
    exact fun hp2 => h (hpre.mpr hp2)

end Verity.Specs
