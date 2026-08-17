/-
  Verity: Minimal EDSL Core

  This module defines the essential types and primitives for smart contracts.
  Philosophy: Keep it minimal - only add what examples actually need.
-/

import Verity.Core.Address
import Verity.Core.Int256
import Verity.Core.NarrowTypes
import Verity.Core.Uint16
import Verity.Core.Uint256
import Verity.Core.FiniteSet
import Verity.Core.Intrinsics
import Verity.Core.StorageAttr

namespace Verity

open Verity.Core (FiniteAddressSet)

-- Basic Ethereum types
abbrev Address := Verity.Core.Address
abbrev Bytes32 := Verity.Core.Uint256
abbrev Int256 := Verity.Core.Int256
abbrev Uint16 := Verity.Core.Uint16
abbrev Uint256 := Verity.Core.Uint256
abbrev UIntN := Verity.Core.UIntN
abbrev IntN := Verity.Core.IntN
abbrev BytesN := Verity.Core.BytesN

abbrev Uint24 := UIntN 24
abbrev Uint32 := UIntN 32
abbrev Uint40 := UIntN 40
abbrev Uint48 := UIntN 48
abbrev Uint56 := UIntN 56
abbrev Uint64 := UIntN 64
abbrev Uint72 := UIntN 72
abbrev Uint80 := UIntN 80
abbrev Uint88 := UIntN 88
abbrev Uint96 := UIntN 96
abbrev Uint104 := UIntN 104
abbrev Uint112 := UIntN 112
abbrev Uint120 := UIntN 120
abbrev Uint128 := UIntN 128
abbrev Uint136 := UIntN 136
abbrev Uint144 := UIntN 144
abbrev Uint152 := UIntN 152
abbrev Uint160 := UIntN 160
abbrev Uint168 := UIntN 168
abbrev Uint176 := UIntN 176
abbrev Uint184 := UIntN 184
abbrev Uint192 := UIntN 192
abbrev Uint200 := UIntN 200
abbrev Uint208 := UIntN 208
abbrev Uint216 := UIntN 216
abbrev Uint224 := UIntN 224
abbrev Uint232 := UIntN 232
abbrev Uint240 := UIntN 240
abbrev Uint248 := UIntN 248

abbrev Int8 := IntN 8
abbrev Int16 := IntN 16
abbrev Int24 := IntN 24
abbrev Int32 := IntN 32
abbrev Int40 := IntN 40
abbrev Int48 := IntN 48
abbrev Int56 := IntN 56
abbrev Int64 := IntN 64
abbrev Int72 := IntN 72
abbrev Int80 := IntN 80
abbrev Int88 := IntN 88
abbrev Int96 := IntN 96
abbrev Int104 := IntN 104
abbrev Int112 := IntN 112
abbrev Int120 := IntN 120
abbrev Int128 := IntN 128
abbrev Int136 := IntN 136
abbrev Int144 := IntN 144
abbrev Int152 := IntN 152
abbrev Int160 := IntN 160
abbrev Int168 := IntN 168
abbrev Int176 := IntN 176
abbrev Int184 := IntN 184
abbrev Int192 := IntN 192
abbrev Int200 := IntN 200
abbrev Int208 := IntN 208
abbrev Int216 := IntN 216
abbrev Int224 := IntN 224
abbrev Int232 := IntN 232
abbrev Int240 := IntN 240
abbrev Int248 := IntN 248

abbrev Bytes1 := BytesN 1
abbrev Bytes2 := BytesN 2
abbrev Bytes3 := BytesN 3
abbrev Bytes4 := BytesN 4
abbrev Bytes5 := BytesN 5
abbrev Bytes6 := BytesN 6
abbrev Bytes7 := BytesN 7
abbrev Bytes8 := BytesN 8
abbrev Bytes9 := BytesN 9
abbrev Bytes10 := BytesN 10
abbrev Bytes11 := BytesN 11
abbrev Bytes12 := BytesN 12
abbrev Bytes13 := BytesN 13
abbrev Bytes14 := BytesN 14
abbrev Bytes15 := BytesN 15
abbrev Bytes16 := BytesN 16
abbrev Bytes17 := BytesN 17
abbrev Bytes18 := BytesN 18
abbrev Bytes19 := BytesN 19
abbrev Bytes20 := BytesN 20
abbrev Bytes21 := BytesN 21
abbrev Bytes22 := BytesN 22
abbrev Bytes23 := BytesN 23
abbrev Bytes24 := BytesN 24
abbrev Bytes25 := BytesN 25
abbrev Bytes26 := BytesN 26
abbrev Bytes27 := BytesN 27
abbrev Bytes28 := BytesN 28
abbrev Bytes29 := BytesN 29
abbrev Bytes30 := BytesN 30
abbrev Bytes31 := BytesN 31

@[simp] def toInt256 (value : Uint256) : Int256 :=
  Verity.Core.Int256.ofUint256 value

@[simp] def toUint256 (value : Int256) : Uint256 :=
  Verity.Core.Int256.toUint256 value

@[simp] def zeroAddress : Address := 0

@[simp] def addressToWord (a : Address) : Uint256 :=
  (a.toNat : Uint256)

@[simp] def wordToAddress (w : Uint256) : Address :=
  Verity.Core.Address.ofNat (w : Nat)

/-- Replace only the address-sized low bits of a storage word.  Address
views are lenses into word storage, so reserved upper bits survive writes. -/
def writeAddressWord (word : Uint256) (value : Address) : Uint256 :=
  word - addressToWord (wordToAddress word) + addressToWord value

@[simp] theorem writeAddressWord_wordToAddress (word : Uint256) :
    writeAddressWord word (wordToAddress word) = word := by
  simpa only [writeAddressWord, Verity.Core.Uint256.add_comm] using
    Verity.Core.Uint256.sub_add_cancel_left word (addressToWord (wordToAddress word))

@[simp] theorem wordToAddress_writeAddressWord (word : Uint256) (value : Address) :
    wordToAddress (writeAddressWord word value) = value := by
  apply Verity.Core.Address.ext
  change (writeAddressWord word value).val % Verity.Core.Address.modulus = value.val
  have hvalue : (addressToWord value).val = value.val := by
    simp [addressToWord, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt (by
      calc
        value.val < Verity.Core.Address.modulus := value.isLt
        _ < Verity.Core.Uint256.modulus := by
          change 2 ^ 160 < 2 ^ 256
          exact Nat.pow_lt_pow_right (by decide) (by decide))
  have hlow : (addressToWord (wordToAddress word)).val =
      word.val % Verity.Core.Address.modulus := by
    simp [addressToWord, wordToAddress, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans
      (Nat.mod_lt _ Verity.Core.Address.modulus_pos)
      (by
        change 2 ^ 160 < 2 ^ 256
        exact Nat.pow_lt_pow_right (by decide) (by decide)))
  have hsub : (word - addressToWord (wordToAddress word)).val =
      word.val - word.val % Verity.Core.Address.modulus := by
    change (Verity.Core.Uint256.sub word (addressToWord (wordToAddress word))).val =
      word.val - word.val % Verity.Core.Address.modulus
    rw [Verity.Core.Uint256.subNoWrap]
    · rw [hlow]
    · rw [hlow]
      exact Nat.mod_le _ _
  have hdiv : Verity.Core.Address.modulus ∣ Verity.Core.Uint256.modulus := by
    refine ⟨2 ^ 96, ?_⟩
    change 2 ^ 256 = 2 ^ 160 * 2 ^ 96
    rw [← Nat.pow_add]
  change (word - addressToWord (wordToAddress word) + addressToWord value).val %
      Verity.Core.Address.modulus = value.val
  rw [show (word - addressToWord (wordToAddress word) + addressToWord value).val =
      ((word - addressToWord (wordToAddress word)).val + (addressToWord value).val) %
        Verity.Core.Uint256.modulus by rfl]
  rw [Nat.mod_mod_of_dvd _ hdiv, hsub, hvalue]
  have hdecomp : word.val % Verity.Core.Address.modulus +
      Verity.Core.Address.modulus * (word.val / Verity.Core.Address.modulus) = word.val := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div word.val Verity.Core.Address.modulus)
  have hsub' : word.val - word.val % Verity.Core.Address.modulus =
      Verity.Core.Address.modulus * (word.val / Verity.Core.Address.modulus) := by
    omega
  rw [hsub']
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt value.isLt

@[simp] def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

@[simp] def uint16ToWord (value : Uint16) : Uint256 :=
  value.toUint256

@[simp] def wordToUint16 (value : Uint256) : Uint16 :=
  Verity.Core.Uint16.ofUint256 value

@[simp] def bytes32ToWord (value : Bytes32) : Uint256 :=
  value

@[simp] def wordToBytes32 (value : Uint256) : Bytes32 :=
  value

@[simp] def isZeroAddress (a : Address) : Bool :=
  a == zeroAddress

-- Storage key-value abstraction
structure StorageSlot (α : Type) where
  slot : Nat
  deriving Repr

-- Event type for ERC20/ERC721 compliance (#153)
structure Event where
  name : String
  args : List Uint256           -- Unindexed data arguments
  indexedArgs : List Uint256    -- Indexed topic arguments
  deriving Repr

-- External-call journal: core-level observables for calls that cross the
-- contract boundary. Mirrors the denotational call model
-- (`Verity.Core.Model.DenoteExternalCalls`) without importing it, the same
-- way `Event` mirrors log emission (#153).

/-- The EVM external-call opcode family, as recorded in the journal. -/
inductive ExternalCallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr

/-- The control component of an external call's outcome. `failure` is a zero
success bit without a revert payload; `revert` carries its payload through
`returndata`. -/
inductive ExternalCallControl where
  | success
  | failure
  | revert
  deriving DecidableEq, Repr

/-- One entry of the external-call journal: everything a caller can observe
at a call boundary — who was called, how, with what, and what came back. -/
structure ExternalCall where
  siteId : Nat
  kind : ExternalCallKind
  target : Nat
  value : Nat := 0
  calldata : List Nat := []
  control : ExternalCallControl
  returndata : List Nat := []
  /-- Linked-external name for entries journaled by the EDSL executable
  plane, where callees are keyed by name rather than address (the address
  is bound at link time). Address-keyed model-plane entries
  (`DenoteExternalCalls.journalEntry`) leave it empty. -/
  name : String := ""
  deriving DecidableEq, Repr

/-! Canonical, injective names for every word-valued storage location.

The source model deliberately keeps these names separate from compiler-level
keccak slot derivation.  Thus the lens laws below use constructor injectivity,
rather than assuming that a hash is injective. -/
inductive StorageKey where
  | slot (slot : Nat)
  | contractSlot (contract slot : Nat)
  | transient (slot : Nat)
  | addr (slot : Nat)
  | map (slot : Nat) (key : Address)
  | mapUint (slot : Nat) (key : Uint256)
  | map2 (slot : Nat) (key1 key2 : Address)
  deriving DecidableEq, Repr

-- State monad for contract execution
structure ContractState where
  /-- The sole word-valued storage backing map. `StorageKey` retains the
      source-level channel/layout distinction injectively. -/
  storageWords : StorageKey → Uint256
  storageArray : Nat → List Uint256  -- Dynamic-array storage grouped by base slot (#1571)
  sender : Address
  thisAddress : Address
  -- `tx.origin` — the externally owned account that initiated the
  -- top-level transaction.  Equal to `sender` when the contract is
  -- called directly from an EOA; differs when a contract intermediary
  -- forwards the call.  Defaults to `0` for backwards compatibility
  -- with state literals that pre-date this field.
  txOrigin : Address := 0
  msgValue : Uint256
  selfBalance : Uint256 := 0
  blockTimestamp : Uint256
  blockNumber : Uint256 := 0
  chainId : Uint256 := 0
  blobBaseFee : Uint256 := 0
  calldataSize : Uint256 := 0
  calldata : List Nat := []                 -- Immutable calldata words used by ABI expression semantics
  memory : Nat → Uint256 := fun _ => 0     -- EVM memory (word-addressed, zero-initialized)
  knownAddresses : Nat → FiniteAddressSet  -- Tracked addresses per storage slot (for sum properties)
  events : List Event := []  -- Emitted events, append-only log (#153)
  /-- Observed external calls, append-only journal. Journaled call
      denotations (`DenoteExternalCalls.denoteCallJournaled`) append here and
      preserve the journal across caller-side rollback of a failed or
      reverted call: the world is restored *except* this field, otherwise
      reverted calls would be unobservable. A full monadic revert through
      `Contract.run` still restores the pre-call snapshot including the
      journal, which is why the source primitive `externalCall` reports the
      callee's outcome in-band (`ExternalCallResult.control`) instead of
      raising a monadic revert. -/
  calls : List ExternalCall := []

namespace ContractState

/-!
## Canonical storage lens API (P5-A)

The one sanctioned read/write surface over `ContractState`'s storage
channels. Interpreters, denotations and proofs should use these lenses
instead of raw field access/record updates, so the planned word-addressed
storage representation flip (one `Nat → Uint256` map with Solidity-layout
slot derivation) is a swap of lens implementations under stable names and
the `storage_simps` simp set — not another ~1400-site rewrite.
-/

def storage (s : ContractState) : Nat → Uint256 :=
  fun slot => s.storageWords (.slot slot)

/-- Compatibility view for explicitly identified contract worlds. Contract
    `0` remains the unqualified storage world. -/
def contractStorage (s : ContractState) : Nat → Nat → Uint256 :=
  fun contract slot => if contract == 0 then s.storage slot else s.storageWords (.contractSlot contract slot)

def transientStorage (s : ContractState) : Nat → Uint256 :=
  fun slot => s.storageWords (.transient slot)

def storageAddr (s : ContractState) : Nat → Address :=
  fun slot => wordToAddress (s.storageWords (.addr slot))

def storageMap (s : ContractState) : Nat → Address → Uint256 :=
  fun slot key => s.storageWords (.map slot key)

def storageMapUint (s : ContractState) : Nat → Uint256 → Uint256 :=
  fun slot key => s.storageWords (.mapUint slot key)

def storageMap2 (s : ContractState) : Nat → Address → Address → Uint256 :=
  fun slot key1 key2 => s.storageWords (.map2 slot key1 key2)

def readSlot (s : ContractState) (slot : Nat) : Uint256 := s.storage slot

def writeSlot (s : ContractState) (slot : Nat) (value : Uint256) : ContractState :=
  { s with storageWords := fun key => if key == .slot slot then value else s.storageWords key }

/-- Read a word from a contract-separated storage world. Contract id `0`
    deliberately denotes the legacy, unqualified `storage` world. -/
def readContractSlot (s : ContractState) (contract : Nat) (slot : Nat) : Uint256 :=
  if contract == 0 then s.readSlot slot else s.contractStorage contract slot

/-- Write a word in a contract-separated storage world. Contract id `0`
    deliberately updates the legacy, unqualified `storage` world. -/
def writeContractSlot (s : ContractState) (contract : Nat) (slot : Nat)
    (value : Uint256) : ContractState :=
  if contract == 0 then s.writeSlot slot value
  else
    { s with storageWords := fun key =>
        if key == .contractSlot contract slot then value else s.storageWords key }

def readAddrSlot (s : ContractState) (slot : Nat) : Address :=
  s.storageAddr slot

def writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) : ContractState :=
  { s with storageWords := fun key =>
      if key == .addr slot then writeAddressWord (s.storageWords key) value else s.storageWords key }

def readTransient (s : ContractState) (slot : Nat) : Uint256 :=
  s.transientStorage slot

def writeTransient (s : ContractState) (slot : Nat) (value : Uint256) : ContractState :=
  { s with storageWords := fun key => if key == .transient slot then value else s.storageWords key }

def readMap (s : ContractState) (slot : Nat) (key : Address) : Uint256 :=
  s.storageMap slot key

def writeMap (s : ContractState) (slot : Nat) (key : Address) (value : Uint256) : ContractState :=
  { s with storageWords := fun storageKey =>
      if storageKey == .map slot key then value else s.storageWords storageKey }

/-- Word-slot writes leave the address and mapping compatibility views intact. -/
@[simp] theorem storageAddr_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).storageAddr = s.storageAddr := by
  funext addrSlot
  simp [storageAddr, writeSlot]

@[simp] theorem storageMap_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).storageMap = s.storageMap := by
  funext mapSlot mapKey
  simp [storageMap, writeSlot]

@[simp] theorem storageMapUint_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey
  simp [storageMapUint, writeSlot]

@[simp] theorem storageMap2_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).storageMap2 = s.storageMap2 := by
  funext mapSlot mapKey1 mapKey2
  simp [storageMap2, writeSlot]

@[simp] theorem sender_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).thisAddress = s.thisAddress := rfl
@[simp] theorem txOrigin_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).txOrigin = s.txOrigin := rfl
@[simp] theorem msgValue_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).msgValue = s.msgValue := rfl
@[simp] theorem selfBalance_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).selfBalance = s.selfBalance := rfl
@[simp] theorem blockTimestamp_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).blockTimestamp = s.blockTimestamp := rfl
@[simp] theorem blockNumber_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).blockNumber = s.blockNumber := rfl
@[simp] theorem chainId_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).chainId = s.chainId := rfl
@[simp] theorem blobBaseFee_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).blobBaseFee = s.blobBaseFee := rfl
@[simp] theorem calldataSize_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).calldataSize = s.calldataSize := rfl
@[simp] theorem calldata_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).calldata = s.calldata := rfl
@[simp] theorem memory_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).memory = s.memory := rfl
@[simp] theorem knownAddresses_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).knownAddresses = s.knownAddresses := rfl
@[simp] theorem events_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).events = s.events := rfl
@[simp] theorem calls_writeSlot (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).calls = s.calls := rfl

@[simp] theorem storageWords_writeSlot (s : ContractState) (slot : Nat) (value : Uint256)
    (key : StorageKey) :
    (s.writeSlot slot value).storageWords key =
      if key == .slot slot then value else s.storageWords key := rfl

/-- Compatibility views reduce through a `storageWords` record update. Contract
    proofs that unfold `writeSlot`/`writeAddrSlot`/`writeMap` land on this form. -/
@[simp] theorem storage_set_storageWords (s : ContractState) (f : StorageKey → Uint256)
    (n : Nat) :
    { s with storageWords := f }.storage n = f (.slot n) := rfl

@[simp] theorem storageAddr_set_storageWords (s : ContractState) (f : StorageKey → Uint256)
    (n : Nat) :
    { s with storageWords := f }.storageAddr n = wordToAddress (f (.addr n)) := rfl

@[simp] theorem storageMap_set_storageWords (s : ContractState) (f : StorageKey → Uint256)
    (n : Nat) (key : Address) :
    { s with storageWords := f }.storageMap n key = f (.map n key) := rfl

@[simp] theorem storageMapUint_set_storageWords (s : ContractState)
    (f : StorageKey → Uint256) (n : Nat) (key : Uint256) :
    { s with storageWords := f }.storageMapUint n key = f (.mapUint n key) := rfl

@[simp] theorem storageMap2_set_storageWords (s : ContractState)
    (f : StorageKey → Uint256) (n : Nat) (key1 key2 : Address) :
    { s with storageWords := f }.storageMap2 n key1 key2 = f (.map2 n key1 key2) := rfl

@[simp] theorem transientStorage_set_storageWords (s : ContractState)
    (f : StorageKey → Uint256) (n : Nat) :
    { s with storageWords := f }.transientStorage n = f (.transient n) := rfl

/-- Address-slot writes leave word-slot and mapping compatibility views intact. -/
@[simp] theorem storage_writeSlot_same (s : ContractState) (slot : Nat) (value : Uint256) :
    (s.writeSlot slot value).storage slot = value := by
  simp [storage, writeSlot]

@[simp] theorem storage_writeSlot_other (s : ContractState) {slot slot' : Nat}
    (h : slot' ≠ slot) (value : Uint256) :
    (s.writeSlot slot value).storage slot' = s.storage slot' := by
  simp [storage, writeSlot, h]

@[simp] theorem transientStorage_writeTransient_same (s : ContractState) (slot : Nat)
    (value : Uint256) :
    (s.writeTransient slot value).transientStorage slot = value := by
  simp [transientStorage, writeTransient]

@[simp] theorem transientStorage_writeTransient_other (s : ContractState)
    {slot slot' : Nat} (h : slot' ≠ slot) (value : Uint256) :
    (s.writeTransient slot value).transientStorage slot' = s.transientStorage slot' := by
  simp [transientStorage, writeTransient, h]

@[simp] theorem storage_writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) :
    (s.writeAddrSlot slot value).storage = s.storage := by
  funext wordSlot
  simp [storage, writeAddrSlot]

@[simp] theorem storageMap_writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) :
    (s.writeAddrSlot slot value).storageMap = s.storageMap := by
  funext mapSlot mapKey
  simp [storageMap, writeAddrSlot]

@[simp] theorem storageMapUint_writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) :
    (s.writeAddrSlot slot value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey
  simp [storageMapUint, writeAddrSlot]

@[simp] theorem storageMap2_writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) :
    (s.writeAddrSlot slot value).storageMap2 = s.storageMap2 := by
  funext mapSlot mapKey1 mapKey2
  simp [storageMap2, writeAddrSlot]

/-- Same-slot address view after a write. High bits of the backing word
    are not part of the address payload. -/
@[simp] theorem storageAddr_writeAddrSlot_same (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).storageAddr slot = value := by
  simpa [storageAddr, writeAddrSlot] using
    wordToAddress_writeAddressWord (s.storageWords (.addr slot)) value

@[simp] theorem storageAddr_writeAddrSlot_other (s : ContractState)
    {slot slot' : Nat} (h : slot' ≠ slot) (value : Address) :
    (s.writeAddrSlot slot value).storageAddr slot' = s.storageAddr slot' := by
  simp [storageAddr, writeAddrSlot, h]

@[simp] theorem sender_writeAddrSlot (s : ContractState) (slot : Nat) (value : Address) :
    (s.writeAddrSlot slot value).sender = s.sender := rfl

@[simp] theorem thisAddress_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).thisAddress = s.thisAddress := rfl

@[simp] theorem storageArray_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).storageArray = s.storageArray := rfl

@[simp] theorem msgValue_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).msgValue = s.msgValue := rfl

@[simp] theorem selfBalance_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).selfBalance = s.selfBalance := rfl

@[simp] theorem blockTimestamp_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).blockTimestamp = s.blockTimestamp := rfl

@[simp] theorem blockNumber_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).blockNumber = s.blockNumber := rfl

@[simp] theorem chainId_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).chainId = s.chainId := rfl

@[simp] theorem blobBaseFee_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).blobBaseFee = s.blobBaseFee := rfl

@[simp] theorem calldataSize_writeAddrSlot (s : ContractState) (slot : Nat)
    (value : Address) :
    (s.writeAddrSlot slot value).calldataSize = s.calldataSize := rfl

/-- Mapping writes leave word-slot and address compatibility views intact. -/
@[simp] theorem storage_writeMap (s : ContractState) (slot : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slot key value).storage = s.storage := by
  funext wordSlot
  simp [storage, writeMap]

@[simp] theorem storageAddr_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) : (s.writeMap slot key value).storageAddr = s.storageAddr := by
  funext addrSlot
  simp [storageAddr, writeMap]

@[simp] theorem storageMapUint_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) : (s.writeMap slot key value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey
  simp [storageMapUint, writeMap]

@[simp] theorem storageMap2_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) : (s.writeMap slot key value).storageMap2 = s.storageMap2 := by
  funext mapSlot mapKey1 mapKey2
  simp [storageMap2, writeMap]

@[simp] theorem storageMap_writeMap_same (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).storageMap slot key = value := by
  simp [storageMap, writeMap]

@[simp] theorem storageMap_writeMap_other_key (s : ContractState) (slot : Nat)
    {key key' : Address} (h : key' ≠ key) (value : Uint256) :
    (s.writeMap slot key value).storageMap slot key' = s.storageMap slot key' := by
  simp [storageMap, writeMap, h]

@[simp] theorem sender_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).thisAddress = s.thisAddress := rfl
@[simp] theorem txOrigin_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).txOrigin = s.txOrigin := rfl
@[simp] theorem msgValue_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).msgValue = s.msgValue := rfl
@[simp] theorem selfBalance_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).selfBalance = s.selfBalance := rfl
@[simp] theorem blockTimestamp_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).blockTimestamp = s.blockTimestamp := rfl
@[simp] theorem blockNumber_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).blockNumber = s.blockNumber := rfl
@[simp] theorem chainId_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).chainId = s.chainId := rfl
@[simp] theorem blobBaseFee_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).blobBaseFee = s.blobBaseFee := rfl
@[simp] theorem calldataSize_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).calldataSize = s.calldataSize := rfl
@[simp] theorem calldata_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).calldata = s.calldata := rfl
@[simp] theorem knownAddresses_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).knownAddresses = s.knownAddresses := rfl
@[simp] theorem events_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).events = s.events := rfl
@[simp] theorem calls_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).calls = s.calls := rfl

@[simp] theorem storageWords_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) (storageKey : StorageKey) :
    (s.writeMap slot key value).storageWords storageKey =
      if storageKey == .map slot key then value else s.storageWords storageKey := rfl

def readMapUint (s : ContractState) (slot : Nat) (key : Uint256) : Uint256 :=
  s.storageMapUint slot key

def writeMapUint (s : ContractState) (slot : Nat) (key : Uint256) (value : Uint256) : ContractState :=
  { s with storageWords := fun storageKey =>
      if storageKey == .mapUint slot key then value else s.storageWords storageKey }

@[simp] theorem storage_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).storage = s.storage := by
  funext wordSlot
  simp [storage, writeMapUint]

@[simp] theorem storageAddr_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).storageAddr = s.storageAddr := by
  funext addrSlot
  simp [storageAddr, writeMapUint]

@[simp] theorem storageMap_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).storageMap = s.storageMap := by
  funext mapSlot mapKey
  simp [storageMap, writeMapUint]

@[simp] theorem storageMap2_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).storageMap2 = s.storageMap2 := by
  funext mapSlot mapKey1 mapKey2
  simp [storageMap2, writeMapUint]

@[simp] theorem sender_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).thisAddress = s.thisAddress := rfl
@[simp] theorem knownAddresses_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).knownAddresses = s.knownAddresses := rfl
@[simp] theorem msgValue_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).msgValue = s.msgValue := rfl
@[simp] theorem blockTimestamp_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).blockTimestamp = s.blockTimestamp := rfl
@[simp] theorem blockNumber_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).blockNumber = s.blockNumber := rfl
@[simp] theorem events_writeMapUint (s : ContractState) (slot : Nat) (key value : Uint256) :
    (s.writeMapUint slot key value).events = s.events := rfl

def readMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) : Uint256 :=
  s.storageMap2 slot key1 key2

def writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    ContractState :=
  { s with storageWords := fun storageKey =>
      if storageKey == .map2 slot key1 key2 then value else s.storageWords storageKey }

@[simp] theorem storage_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address)
    (value : Uint256) : (s.writeMap2 slot key1 key2 value).storage = s.storage := by
  funext wordSlot
  simp [storage, writeMap2]

@[simp] theorem storageAddr_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address)
    (value : Uint256) : (s.writeMap2 slot key1 key2 value).storageAddr = s.storageAddr := by
  funext addrSlot
  simp [storageAddr, writeMap2]

@[simp] theorem storageMap_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address)
    (value : Uint256) : (s.writeMap2 slot key1 key2 value).storageMap = s.storageMap := by
  funext mapSlot mapKey
  simp [storageMap, writeMap2]

@[simp] theorem storageMapUint_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address)
    (value : Uint256) : (s.writeMap2 slot key1 key2 value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey
  simp [storageMapUint, writeMap2]

@[simp] theorem storageMap2_writeMap2_same (s : ContractState) (slot : Nat)
    (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).storageMap2 slot key1 key2 = value := by
  simp [storageMap2, writeMap2]

@[simp] theorem storageMap2_writeMap2_other (s : ContractState) (slot : Nat)
    {key1 key1' key2 key2' : Address} (h : key1' ≠ key1 ∨ key2' ≠ key2)
    (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).storageMap2 slot key1' key2' =
      s.storageMap2 slot key1' key2' := by
  simp [storageMap2, writeMap2]
  intro hkey
  cases h with
  | inl h1 => exact (h1 hkey.1).elim
  | inr h2 => exact (h2 hkey.2).elim

@[simp] theorem sender_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).thisAddress = s.thisAddress := rfl
@[simp] theorem knownAddresses_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).knownAddresses = s.knownAddresses := rfl
@[simp] theorem msgValue_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).msgValue = s.msgValue := rfl
@[simp] theorem blockTimestamp_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).blockTimestamp = s.blockTimestamp := rfl
@[simp] theorem blockNumber_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).blockNumber = s.blockNumber := rfl
@[simp] theorem events_writeMap2 (s : ContractState) (slot : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).events = s.events := rfl

def readArray (s : ContractState) (slot : Nat) : List Uint256 :=
  s.storageArray slot

def writeArray (s : ContractState) (slot : Nat) (values : List Uint256) : ContractState :=
  { s with storageArray := fun sl => if sl == slot then values else s.storageArray sl }

@[simp] theorem storage_writeArray (s : ContractState) (slot : Nat)
    (values : List Uint256) :
    (s.writeArray slot values).storage = s.storage := rfl

@[simp] theorem storageArray_writeArray_same (s : ContractState) (slot : Nat)
    (values : List Uint256) :
    (s.writeArray slot values).storageArray slot = values := by
  simp [writeArray]

@[simp] theorem storageArray_writeArray_other (s : ContractState)
    {slot slot' : Nat} (h : slot' ≠ slot) (values : List Uint256) :
    (s.writeArray slot values).storageArray slot' = s.storageArray slot' := by
  simp [writeArray, h]

@[simp] theorem storageArray_writeSlot (s : ContractState) (slot : Nat)
    (value : Uint256) :
    (s.writeSlot slot value).storageArray = s.storageArray := rfl

/-!
### Bulk lenses (C5)

Multi-slot writes used by the denotational layer (aliased packed fields,
word-spanning writes). Shapes match the historical raw record updates
exactly (`targets.contains`-guarded function update), so migrating a raw
site to a bulk lens is definitional. Like the single-slot lenses, these are
the only sanctioned multi-slot write surface over the storage channels.
-/

/-- Write `value` at every slot in `targets` (uint channel). -/
def writeSlots (s : ContractState) (targets : List Nat) (value : Uint256) :
    ContractState :=
  { s with storageWords := fun key => match key with
      | .slot slot => if targets.contains slot then value else s.storageWords key
      | _ => s.storageWords key }

/-- Read-modify-write every slot in `targets` (uint channel). -/
def modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) : ContractState :=
  { s with storageWords := fun key => match key with
      | .slot slot => if targets.contains slot then f (s.storageWords key) else s.storageWords key
      | _ => s.storageWords key }

/-- Write `value` at every transient slot in `targets`. -/
def writeTransientSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) : ContractState :=
  { s with storageWords := fun key => match key with
      | .transient slot => if targets.contains slot then value else s.storageWords key
      | _ => s.storageWords key }

/-- Read-modify-write every transient slot in `targets`. -/
def modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) : ContractState :=
  { s with storageWords := fun key => match key with
      | .transient slot => if targets.contains slot then f (s.storageWords key) else s.storageWords key
      | _ => s.storageWords key }

/-- Write `value` at every address slot in `targets`. -/
def writeAddrSlots (s : ContractState) (targets : List Nat) (value : Address) :
    ContractState :=
  { s with storageWords := fun key => match key with
      | .addr slot => if targets.contains slot then writeAddressWord (s.storageWords key) value
        else s.storageWords key
      | _ => s.storageWords key }

/-- Replace the whole uint channel through a transformer. The denotational
layer's flat-view rebuilds (mapping writes rendered through a `Nat → Nat`
storage view) are channel-wide, not slot-guarded; this is their sanctioned
surface. The C5 flip reimplements it as a `.slot`-key-restricted update. -/
def withStorageChannel (s : ContractState)
    (f : (Nat → Uint256) → Nat → Uint256) : ContractState :=
  { s with storageWords := fun key => match key with
      | .slot slot => f s.storage slot
      | _ => s.storageWords key }

private theorem mem_of_contains_true {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {x : α} (h : xs.contains x = true) : x ∈ xs :=
  (List.contains_iff_mem).mp h

private theorem not_mem_of_contains_false {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {x : α} (h : xs.contains x = false) : x ∉ xs := by
  intro hmem
  have := (List.contains_iff_mem).mpr hmem
  exact Bool.noConfusion (this.symm.trans h)

@[simp] theorem sender_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).thisAddress = s.thisAddress := rfl
@[simp] theorem selfBalance_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).selfBalance = s.selfBalance := rfl
@[simp] theorem calldata_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).calldata = s.calldata := rfl
@[simp] theorem calldataSize_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).calldataSize = s.calldataSize := rfl
@[simp] theorem msgValue_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).msgValue = s.msgValue := rfl

@[simp] theorem sender_writeAddrSlots (s : ContractState) (targets : List Nat)
    (value : Address) :
    (s.writeAddrSlots targets value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeAddrSlots (s : ContractState) (targets : List Nat)
    (value : Address) :
    (s.writeAddrSlots targets value).thisAddress = s.thisAddress := rfl
@[simp] theorem calldata_writeAddrSlots (s : ContractState) (targets : List Nat)
    (value : Address) :
    (s.writeAddrSlots targets value).calldata = s.calldata := rfl

@[simp] theorem sender_writeTransientSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeTransientSlots targets value).sender = s.sender := rfl
@[simp] theorem thisAddress_writeTransientSlots (s : ContractState)
    (targets : List Nat) (value : Uint256) :
    (s.writeTransientSlots targets value).thisAddress = s.thisAddress := rfl
@[simp] theorem calldata_writeTransientSlots (s : ContractState)
    (targets : List Nat) (value : Uint256) :
    (s.writeTransientSlots targets value).calldata = s.calldata := rfl

@[simp] theorem sender_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).sender = s.sender := rfl
@[simp] theorem thisAddress_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).thisAddress = s.thisAddress := rfl
@[simp] theorem calldata_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).calldata = s.calldata := rfl

@[simp] theorem storageArray_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_writeAddrSlots (s : ContractState) (targets : List Nat)
    (value : Address) :
    (s.writeAddrSlots targets value).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_writeTransientSlots (s : ContractState)
    (targets : List Nat) (value : Uint256) :
    (s.writeTransientSlots targets value).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_modifyTransientSlots (s : ContractState)
    (targets : List Nat) (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_withStorageChannel (s : ContractState)
    (f : (Nat → Uint256) → Nat → Uint256) :
    (s.withStorageChannel f).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_writeMap (s : ContractState) (slot : Nat) (key : Address)
    (value : Uint256) :
    (s.writeMap slot key value).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_writeMapUint (s : ContractState) (slot : Nat)
    (key value : Uint256) :
    (s.writeMapUint slot key value).storageArray = s.storageArray := rfl

@[simp] theorem storageArray_writeMap2 (s : ContractState) (slot : Nat)
    (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slot key1 key2 value).storageArray = s.storageArray := rfl

@[simp] theorem storage_writeSlots_mem (s : ContractState) (targets : List Nat)
    (value : Uint256) {slot : Nat} (h : targets.contains slot = true) :
    (s.writeSlots targets value).storage slot = value := by
  have hmem := mem_of_contains_true h
  simp [storage, writeSlots, hmem]

@[simp] theorem storage_writeSlots_not_mem (s : ContractState) (targets : List Nat)
    (value : Uint256) {slot : Nat} (h : targets.contains slot = false) :
    (s.writeSlots targets value).storage slot = s.storage slot := by
  have hmem := not_mem_of_contains_false h
  simp [storage, writeSlots, hmem]

@[simp] theorem storageAddr_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).storageAddr = s.storageAddr := by
  funext slot
  simp [storageAddr, writeSlots]

@[simp] theorem transientStorage_writeSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeSlots targets value).transientStorage = s.transientStorage := by
  funext slot
  simp [transientStorage, writeSlots]

@[simp] theorem storage_writeAddrSlots (s : ContractState) (targets : List Nat)
    (value : Address) :
    (s.writeAddrSlots targets value).storage = s.storage := by
  funext slot
  simp [storage, writeAddrSlots]

@[simp] theorem storageAddr_writeAddrSlots_mem (s : ContractState) (targets : List Nat)
    (value : Address) {slot : Nat} (h : targets.contains slot = true) :
    (s.writeAddrSlots targets value).storageAddr slot = value := by
  have hmem := mem_of_contains_true h
  simpa [storageAddr, writeAddrSlots, hmem] using
    wordToAddress_writeAddressWord (s.storageWords (.addr slot)) value

@[simp] theorem storageAddr_writeAddrSlots_not_mem (s : ContractState)
    (targets : List Nat) (value : Address) {slot : Nat}
    (h : targets.contains slot = false) :
    (s.writeAddrSlots targets value).storageAddr slot = s.storageAddr slot := by
  have hmem := not_mem_of_contains_false h
  simp [storageAddr, writeAddrSlots, hmem]

@[simp] theorem transientStorage_writeAddrSlots (s : ContractState)
    (targets : List Nat) (value : Address) :
    (s.writeAddrSlots targets value).transientStorage = s.transientStorage := by
  funext slot
  simp [transientStorage, writeAddrSlots]

@[simp] theorem storage_writeTransientSlots (s : ContractState) (targets : List Nat)
    (value : Uint256) :
    (s.writeTransientSlots targets value).storage = s.storage := by
  funext slot
  simp [storage, writeTransientSlots]

@[simp] theorem storageAddr_writeTransientSlots (s : ContractState)
    (targets : List Nat) (value : Uint256) :
    (s.writeTransientSlots targets value).storageAddr = s.storageAddr := by
  funext slot
  simp [storageAddr, writeTransientSlots]

@[simp] theorem transientStorage_writeTransientSlots_mem (s : ContractState)
    (targets : List Nat) (value : Uint256) {slot : Nat}
    (h : targets.contains slot = true) :
    (s.writeTransientSlots targets value).transientStorage slot = value := by
  have hmem := mem_of_contains_true h
  simp [transientStorage, writeTransientSlots, hmem]

@[simp] theorem transientStorage_writeTransientSlots_not_mem (s : ContractState)
    (targets : List Nat) (value : Uint256) {slot : Nat}
    (h : targets.contains slot = false) :
    (s.writeTransientSlots targets value).transientStorage slot =
      s.transientStorage slot := by
  have hmem := not_mem_of_contains_false h
  simp [transientStorage, writeTransientSlots, hmem]

@[simp] theorem storage_modifySlots_not_mem (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) {slot : Nat} (h : targets.contains slot = false) :
    (s.modifySlots targets f).storage slot = s.storage slot := by
  have hmem := not_mem_of_contains_false h
  simp [storage, modifySlots, hmem]

@[simp] theorem storage_modifySlots_mem (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) {slot : Nat} (h : targets.contains slot = true) :
    (s.modifySlots targets f).storage slot = f (s.storage slot) := by
  have hmem := mem_of_contains_true h
  simp [storage, modifySlots, hmem]

@[simp] theorem storageAddr_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).storageAddr = s.storageAddr := by
  funext slot
  simp [storageAddr, modifySlots]

@[simp] theorem transientStorage_modifySlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifySlots targets f).transientStorage = s.transientStorage := by
  funext slot
  simp [transientStorage, modifySlots]

@[simp] theorem storage_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).storage = s.storage := by
  funext slot
  simp [storage, modifyTransientSlots]

@[simp] theorem storageAddr_modifyTransientSlots (s : ContractState)
    (targets : List Nat) (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).storageAddr = s.storageAddr := by
  funext slot
  simp [storageAddr, modifyTransientSlots]

@[simp] theorem transientStorage_modifyTransientSlots_mem (s : ContractState)
    (targets : List Nat) (f : Uint256 → Uint256) {slot : Nat}
    (h : targets.contains slot = true) :
    (s.modifyTransientSlots targets f).transientStorage slot =
      f (s.transientStorage slot) := by
  have hmem := mem_of_contains_true h
  simp [transientStorage, modifyTransientSlots, hmem]

@[simp] theorem transientStorage_modifyTransientSlots_not_mem (s : ContractState)
    (targets : List Nat) (f : Uint256 → Uint256) {slot : Nat}
    (h : targets.contains slot = false) :
    (s.modifyTransientSlots targets f).transientStorage slot =
      s.transientStorage slot := by
  have hmem := not_mem_of_contains_false h
  simp [transientStorage, modifyTransientSlots, hmem]

@[simp] theorem sender_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).sender = s.sender := rfl
@[simp] theorem thisAddress_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).thisAddress = s.thisAddress := rfl
@[simp] theorem msgValue_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).msgValue = s.msgValue := rfl
@[simp] theorem selfBalance_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).selfBalance = s.selfBalance := rfl
@[simp] theorem blockTimestamp_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).blockTimestamp = s.blockTimestamp := rfl
@[simp] theorem blockNumber_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).blockNumber = s.blockNumber := rfl
@[simp] theorem chainId_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).chainId = s.chainId := rfl
@[simp] theorem blobBaseFee_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).blobBaseFee = s.blobBaseFee := rfl
@[simp] theorem calldataSize_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).calldataSize = s.calldataSize := rfl
@[simp] theorem events_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).events = s.events := rfl
@[simp] theorem memory_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).memory = s.memory := rfl
@[simp] theorem txOrigin_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).txOrigin = s.txOrigin := rfl
@[simp] theorem calldata_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).calldata = s.calldata := rfl
@[simp] theorem knownAddresses_modifyTransientSlots (s : ContractState)
    (targets : List Nat) (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).knownAddresses = s.knownAddresses := rfl
@[simp] theorem calls_modifyTransientSlots (s : ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) :
    (s.modifyTransientSlots targets f).calls = s.calls := rfl

@[simp] theorem storage_withStorageChannel (s : ContractState)
    (f : (Nat → Uint256) → Nat → Uint256) :
    (s.withStorageChannel f).storage = f s.storage := by
  funext slot
  simp [storage, withStorageChannel]

@[simp] theorem storageAddr_withStorageChannel (s : ContractState)
    (f : (Nat → Uint256) → Nat → Uint256) :
    (s.withStorageChannel f).storageAddr = s.storageAddr := by
  funext slot
  simp [storageAddr, withStorageChannel]

@[simp] theorem transientStorage_withStorageChannel (s : ContractState)
    (f : (Nat → Uint256) → Nat → Uint256) :
    (s.withStorageChannel f).transientStorage = s.transientStorage := by
  funext slot
  simp [transientStorage, withStorageChannel]

/-- Canonical full-state constructor from explicit storage channels. Clients
building a world from externally supplied channel functions (interpreter
harnesses, counterexample states) go through this instead of a raw record
literal, so the C5 flip can rebuild the internal representation from the
given channels in one place. Non-storage fields start at their defaults and
are customized by the caller with an ordinary record update. -/
def ofChannels
    (uintChannel : Nat → Uint256)
    (transientChannel : Nat → Uint256 := fun _ => 0)
    (addrChannel : Nat → Address := fun _ => 0)
    (mapChannel : Nat → Address → Uint256 := fun _ _ => 0)
    (mapUintChannel : Nat → Uint256 → Uint256 := fun _ _ => 0)
    (map2Channel : Nat → Address → Address → Uint256 := fun _ _ _ => 0)
    (arrayChannel : Nat → List Uint256 := fun _ => [])
    (sender : Address := 0)
    (thisAddress : Address := 0)
    (msgValue : Uint256 := 0)
    (blockTimestamp : Uint256 := 0) : ContractState :=
  { storageWords := fun key => match key with
      | .slot slot => uintChannel slot
      | .contractSlot _ _ => 0
      | .transient slot => transientChannel slot
      | .addr slot => addressToWord (addrChannel slot)
      | .map slot key => mapChannel slot key
      | .mapUint slot key => mapUintChannel slot key
      | .map2 slot key1 key2 => map2Channel slot key1 key2
    storageArray := arrayChannel
    sender := sender
    thisAddress := thisAddress
    msgValue := msgValue
    blockTimestamp := blockTimestamp
    knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty }

@[storage_simps] theorem readSlot_writeSlot_same (s : ContractState) (slot : Nat) (v : Uint256) :
    (s.writeSlot slot v).readSlot slot = v := by
  simp [readSlot, storage, writeSlot]

@[storage_simps] theorem readSlot_writeSlot_other (s : ContractState) {slot slot' : Nat}
    (h : slot' ≠ slot) (v : Uint256) :
    (s.writeSlot slot v).readSlot slot' = s.readSlot slot' := by
  simp [readSlot, storage, writeSlot, h]

@[storage_simps] theorem readContractSlot_zero (s : ContractState) (slot : Nat) :
    s.readContractSlot 0 slot = s.readSlot slot := by
  simp [readContractSlot]

@[storage_simps] theorem readContractSlot_writeContractSlot_same
    (s : ContractState) (contract slot : Nat) (v : Uint256) :
    (s.writeContractSlot contract slot v).readContractSlot contract slot = v := by
  by_cases h : contract = 0
  · subst contract
    simp [readContractSlot, readSlot, storage, writeContractSlot, writeSlot]
  · simp [readContractSlot, contractStorage, writeContractSlot, h]

@[storage_simps] theorem readContractSlot_writeContractSlot_other_contract
    (s : ContractState) {contract contract' slot : Nat} (h : contract' ≠ contract)
    (v : Uint256) :
    (s.writeContractSlot contract slot v).readContractSlot contract' slot =
      s.readContractSlot contract' slot := by
  by_cases hc : contract = 0
  · subst contract
    have hc' : contract' ≠ 0 := h
    simp [readContractSlot, contractStorage, writeContractSlot, writeSlot, hc']
  · by_cases hc' : contract' = 0
    · subst contract'
      simp [readContractSlot, writeContractSlot, readSlot, storage, hc]
    · simp [readContractSlot, contractStorage, writeContractSlot, hc, hc', h]

@[storage_simps] theorem readAddrSlot_writeAddrSlot_same (s : ContractState) (slot : Nat)
    (v : Address) : (s.writeAddrSlot slot v).readAddrSlot slot = v := by
  simpa [readAddrSlot, storageAddr, writeAddrSlot] using
    wordToAddress_writeAddressWord (s.storageWords (.addr slot)) v

/-- Address-slot get-put holds even when the canonical backing word has
nonzero bits above the 160-bit address payload. -/
@[storage_simps] theorem writeAddrSlot_readAddrSlot (s : ContractState) (slot : Nat) :
    s.writeAddrSlot slot (s.readAddrSlot slot) = s := by
  cases s
  simp only [writeAddrSlot, readAddrSlot, storageAddr]
  congr
  funext key
  by_cases h : key = StorageKey.addr slot
  · subst key
    have hself : (StorageKey.addr slot == StorageKey.addr slot) = true := by simp
    rw [if_pos hself]
    exact writeAddressWord_wordToAddress _
  · simp [h]

@[storage_simps] theorem readAddrSlot_writeAddrSlot_other (s : ContractState)
    {slot slot' : Nat} (h : slot' ≠ slot) (v : Address) :
    (s.writeAddrSlot slot v).readAddrSlot slot' = s.readAddrSlot slot' := by
  simp [readAddrSlot, storageAddr, writeAddrSlot, h]

@[storage_simps] theorem readTransient_writeTransient_same (s : ContractState) (slot : Nat)
    (v : Uint256) : (s.writeTransient slot v).readTransient slot = v := by
  simp [readTransient, transientStorage, writeTransient]

@[storage_simps] theorem readTransient_writeTransient_other (s : ContractState)
    {slot slot' : Nat} (h : slot' ≠ slot) (v : Uint256) :
    (s.writeTransient slot v).readTransient slot' = s.readTransient slot' := by
  simp [readTransient, transientStorage, writeTransient, h]

@[storage_simps] theorem readMap_writeMap_same (s : ContractState) (slot : Nat) (key : Address)
    (v : Uint256) : (s.writeMap slot key v).readMap slot key = v := by
  simp [readMap, storageMap, writeMap]

@[storage_simps] theorem readMap_writeMap_other_key (s : ContractState) (slot : Nat)
    {key key' : Address} (h : key' ≠ key) (v : Uint256) :
    (s.writeMap slot key v).readMap slot key' = s.readMap slot key' := by
  simp [readMap, storageMap, writeMap, h]

@[storage_simps] theorem readMapUint_writeMapUint_same (s : ContractState) (slot : Nat)
    (key : Uint256) (v : Uint256) :
    (s.writeMapUint slot key v).readMapUint slot key = v := by
  simp [readMapUint, storageMapUint, writeMapUint]

@[storage_simps] theorem readMap2_writeMap2_same (s : ContractState) (slot : Nat)
    (key1 key2 : Address) (v : Uint256) :
    (s.writeMap2 slot key1 key2 v).readMap2 slot key1 key2 = v := by
  simp [readMap2, storageMap2, writeMap2]

@[storage_simps] theorem readArray_writeArray_same (s : ContractState) (slot : Nat)
    (vs : List Uint256) : (s.writeArray slot vs).readArray slot = vs := by
  simp [readArray, writeArray]

@[storage_simps] theorem readArray_writeArray_other (s : ContractState) {slot slot' : Nat}
    (h : slot' ≠ slot) (vs : List Uint256) :
    (s.writeArray slot vs).readArray slot' = s.readArray slot' := by
  simp [readArray, writeArray, h]

-- C5 step 2: the lenses are no longer default-simp transparent.  Proofs
-- normalize lens reads over lens writes through the `storage_simps` simp set
-- (laws only — it deliberately does NOT unfold lenses to the raw record
-- representation, so it survives the C5 step-3 flip).  Proofs that genuinely
-- need the current raw representation unfold a specific lens by name
-- (`simp [ContractState.writeSlot]`); those sites are the step-3 burn-down.

end ContractState

-- Default zero state — all storage zero, empty addresses, no events.
-- Use `{ defaultState with sender := Address.ofNat 0xA11CE }` to customize fields.
def defaultState : ContractState where
  storageWords := fun _ => 0
  storageArray := fun _ => []
  sender := 0
  thisAddress := 0
  txOrigin := 0
  msgValue := 0
  selfBalance := 0
  blockTimestamp := 0
  blockNumber := 0
  chainId := 0
  knownAddresses := fun _ => Core.FiniteAddressSet.empty

-- Repr instance for ContractState (simplified for readability)
instance : Repr ContractState where
  reprPrec s _ := s!"ContractState(sender={repr s.sender}, thisAddress={repr s.thisAddress})"

-- Contract execution result (explicit success/failure)
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α
  deriving Repr

namespace ContractResult

-- Projections for backward compatibility with proofs.
-- WARNING: `fst` returns `default` on revert — proofs using `fst` must
-- independently establish that the result is `success`.
-- Prefer `getValue?` for new code.
def fst {α : Type} [Inhabited α] : ContractResult α → α
  | success a _ => a
  | revert _ _ => default

-- On revert, returns the state carried in the `ContractResult`.
-- When results are produced via `Contract.run`, this is always the original
-- pre-call snapshot (rollback-by-construction; see issue #254).
def snd {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s

-- Reduction rules for projections applied to constructors.
-- These ensure that when simp produces `ContractResult.success ...`, further
-- `.fst`/`.snd` applications are automatically reduced.
@[simp] theorem fst_success [Inhabited α] (a : α) (s : ContractState) :
  (ContractResult.success a s).fst = a := rfl

@[simp] theorem snd_success (a : α) (s : ContractState) :
  (ContractResult.success a s).snd = s := rfl

@[simp] theorem snd_revert (msg : String) (s : ContractState) :
  (ContractResult.revert (α := α) msg s).snd = s := rfl

end ContractResult

-- The contract monad with explicit success/failure
abbrev Contract (α : Type) := ContractState → ContractResult α

-- Monad operations for Contract
def pure {α : Type} (a : α) : Contract α :=
  fun s => ContractResult.success a s

def bind {α β : Type} (ma : Contract α) (f : α → Contract β) : Contract β :=
  fun s => match ma s with
    | ContractResult.success a s' => f a s'
    | ContractResult.revert msg s' => ContractResult.revert msg s'

-- Convenience: run a Contract with EVM-like revert semantics.
-- Any revert is normalized to the pre-call snapshot `s`.
def Contract.run {α : Type} (c : Contract α) (s : ContractState) : ContractResult α :=
  match c s with
  | ContractResult.success a s' => ContractResult.success a s'
  | ContractResult.revert msg _ => ContractResult.revert msg s

/-- Execute `attempt` with per-call rollback semantics and, on revert, run
`handler` from the original pre-call snapshot. Successful attempts keep their
post-state and do not invoke the handler. -/
def Contract.tryCatch {α : Type} (attempt : Contract α) (handler : String → Contract Unit) :
    Contract Unit :=
  fun s =>
    match Contract.run attempt s with
    | ContractResult.success _ s' => ContractResult.success () s'
    | ContractResult.revert msg rollback => handler msg rollback

set_option warning.simp.varHead false in
@[simp] theorem Contract.eq_of_run_success {α : Type} {c : Contract α} {s : ContractState}
    {a : α} {s' : ContractState} (h : c.run s = ContractResult.success a s') :
    c s = ContractResult.success a s' := by
  unfold Contract.run at h
  cases hcs : c s with
  | success a0 s0 =>
    simp [hcs] at h
    rcases h with ⟨ha, hs⟩
    subst ha
    subst hs
    rfl
  | revert msg s0 =>
    simp [hcs] at h

/-- A reverting prefix makes the whole bind revert to the pre-call snapshot. -/
theorem bind_run_revert {α β : Type} (ma : Contract α) (f : α → Contract β)
    (s : ContractState) (msg : String)
    (h : ma.run s = ContractResult.revert msg s) :
    (bind ma f).run s = ContractResult.revert msg s := by
  unfold Contract.run at h
  cases hma : ma s with
  | success _ _ =>
      simp [hma] at h
  | revert msg' _ =>
      simp [bind, Contract.run, hma] at h ⊢
      subst h
      rfl

/-- If `ma` succeeds without changing state, `run (bind ma f)` is `run (f a)`. -/
theorem bind_run_success {α β : Type} (ma : Contract α) (f : α → Contract β)
    (s : ContractState) (a : α)
    (h : ma.run s = ContractResult.success a s) :
    (bind ma f).run s = (f a).run s := by
  unfold Contract.run at h
  cases hma : ma s with
  | success a' s' =>
      simp [hma] at h
      rcases h with ⟨rfl, rfl⟩
      simp [bind, Contract.run, hma]
  | revert _ _ =>
      simp [hma] at h

@[simp] theorem pure_run (a : α) (state : ContractState) :
  (pure a : Contract α).run state = ContractResult.success a state := rfl

@[simp] theorem tryCatch_success_run
    (attempt : Contract α) (handler : String → Contract Unit) (state state' : ContractState)
    (value : α)
    (h : attempt.run state = ContractResult.success value state') :
    (Contract.tryCatch attempt handler).run state = ContractResult.success () state' := by
  unfold Contract.tryCatch Contract.run at *
  simp [h]

@[simp] theorem tryCatch_revert_run
    (attempt : Contract α) (handler : String → Contract Unit) (state : ContractState)
    (msg : String)
    (h : attempt.run state = ContractResult.revert msg state) :
    (Contract.tryCatch attempt handler).run state = (handler msg).run state := by
  unfold Contract.tryCatch Contract.run at *
  simp [h]

-- Helper: check if result is success
def ContractResult.isSuccess {α : Type} : ContractResult α → Bool
  | success _ _ => true
  | revert _ _ => false

-- Helper: extract value from success (unsafe, for testing)
def ContractResult.getValue? {α : Type} : ContractResult α → Option α
  | success a _ => some a
  | revert _ _ => none

-- Helper: extract state from result.
def ContractResult.getState {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s

-- Backward compatibility helpers for proofs (extracts from success case)
-- These helpers assume the contract succeeds and extract the result/state
namespace Contract

def runValue {α : Type} [Inhabited α] (c : Contract α) (s : ContractState) : α :=
  match c s with
  | ContractResult.success a _ => a
  | ContractResult.revert _ _ => default

def runState {α : Type} (c : Contract α) (s : ContractState) : ContractState :=
  match c s with
  | ContractResult.success _ s' => s'
  | ContractResult.revert _ _ => s

@[simp] theorem runState_eq_snd_run {α : Type} (c : Contract α) (s : ContractState) :
    c.runState s = (c.run s).snd := by
  unfold Contract.runState Contract.run ContractResult.snd
  cases h : c s <;> simp

end Contract

-- Storage operations for Uint256 (routed through the canonical lens API)
def getStorage (s : StorageSlot Uint256) : Contract Uint256 :=
  fun state => ContractResult.success (state.readSlot s.slot) state

def setStorage (s : StorageSlot Uint256) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () (state.writeSlot s.slot value)

def getPackedStorage (s : StorageSlot Uint256) (offset width : Nat) : Contract Uint256 :=
  fun state =>
    ContractResult.success
      ((state.readSlot s.slot).val / (2 ^ offset : Nat) % (2 ^ width : Nat)) state

def setPackedStorage (s : StorageSlot Uint256) (offset width : Nat) (value : Uint256) : Contract Unit :=
  fun state =>
    let current := (state.readSlot s.slot).val
    let updated := (current / (2 ^ (offset + width) : Nat) * (2 ^ (offset + width) : Nat) +
      current % (2 ^ offset : Nat) +
      (value.val % (2 ^ width : Nat)) * (2 ^ offset : Nat) : Nat)
    ContractResult.success () (state.writeSlot s.slot updated)

def getPackedTransientStorage (s : StorageSlot Uint256) (offset width : Nat) : Contract Uint256 :=
  fun state =>
    ContractResult.success
      ((state.readTransient s.slot).val / (2 ^ offset : Nat) % (2 ^ width : Nat)) state

def setPackedTransientStorage (s : StorageSlot Uint256) (offset width : Nat)
    (value : Uint256) : Contract Unit :=
  fun state =>
    let current := (state.readTransient s.slot).val
    let updated := (current / (2 ^ (offset + width) : Nat) * (2 ^ (offset + width) : Nat) +
      current % (2 ^ offset : Nat) +
      (value.val % (2 ^ width : Nat)) * (2 ^ offset : Nat) : Nat)
    ContractResult.success () (state.writeTransient s.slot updated)

@[simp] theorem getStorage_run (s : StorageSlot Uint256) (state : ContractState) :
  (getStorage s).run state = ContractResult.success (state.storage s.slot) state := rfl

@[simp] theorem setStorage_run (s : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
  (setStorage s value).run state = ContractResult.success () (state.writeSlot s.slot value) := rfl

-- Storage operations for Address (routed through the canonical lens API)
def getStorageAddr (s : StorageSlot Address) : Contract Address :=
  fun state => ContractResult.success (state.readAddrSlot s.slot) state

def setStorageAddr (s : StorageSlot Address) (value : Address) : Contract Unit :=
  fun state => ContractResult.success () (state.writeAddrSlot s.slot value)

@[simp] theorem getStorageAddr_run (s : StorageSlot Address) (state : ContractState) :
  (getStorageAddr s).run state = ContractResult.success (state.storageAddr s.slot) state := rfl

@[simp] theorem setStorageAddr_run (s : StorageSlot Address) (value : Address) (state : ContractState) :
  (setStorageAddr s value).run state = ContractResult.success () (state.writeAddrSlot s.slot value) := rfl

-- Mapping operations (Address → Uint256), routed through the canonical lens API.
-- `setMapping` additionally tracks the key in `knownAddresses` (sum properties).
def getMapping (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Uint256 :=
  fun state => ContractResult.success (state.readMap s.slot key) state

def setMapping (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state.writeMap s.slot key value with
    knownAddresses := fun slot =>
      if slot == s.slot then
        (state.knownAddresses slot).insert key
      else
        state.knownAddresses slot
  }

@[simp] theorem getMapping_run (s : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
  (getMapping s key).run state = ContractResult.success (state.storageMap s.slot key) state := rfl

@[simp] theorem setMapping_run (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (state : ContractState) :
  (setMapping s key value).run state = ContractResult.success () { state.writeMap s.slot key value with
    knownAddresses := fun slot =>
      if slot == s.slot then
        (state.knownAddresses slot).insert key
      else
        state.knownAddresses slot
  } := rfl

-- Typed address-valued mapping helpers on top of the word-backed storage model.
def getMappingAddr (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Address :=
  fun state => ContractResult.success (wordToAddress (state.readMap s.slot key)) state

def setMappingAddr (s : StorageSlot (Address → Uint256)) (key value : Address) : Contract Unit :=
  setMapping s key (addressToWord value)

@[simp] theorem getMappingAddr_run (s : StorageSlot (Address → Uint256)) (key : Address)
    (state : ContractState) :
  (getMappingAddr s key).run state =
    ContractResult.success (wordToAddress (state.storageMap s.slot key)) state := rfl

@[simp] theorem setMappingAddr_run (s : StorageSlot (Address → Uint256)) (key value : Address)
    (state : ContractState) :
  (setMappingAddr s key value).run state =
    (setMapping s key (addressToWord value)).run state := rfl

-- Double mapping operations (Address → Address → Uint256) (#154)
def getMapping2 (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) : Contract Uint256 :=
  fun state => ContractResult.success (state.readMap2 s.slot key1 key2) state

def setMapping2 (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () (state.writeMap2 s.slot key1 key2 value)

-- Full-result simp lemmas for double mappings
@[simp] theorem getMapping2_run (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
  (getMapping2 s key1 key2).run state = ContractResult.success (state.storageMap2 s.slot key1 key2) state := rfl

@[simp] theorem setMapping2_run (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (value : Uint256) (state : ContractState) :
  (setMapping2 s key1 key2 value).run state = ContractResult.success ()
    (state.writeMap2 s.slot key1 key2 value) := rfl

-- Uint256-keyed mapping operations (#154)
def getMappingUint (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) : Contract Uint256 :=
  fun state => ContractResult.success (state.readMapUint s.slot key) state

def setMappingUint (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () (state.writeMapUint s.slot key value)

-- Full-result simp lemmas for uint mappings
@[simp] theorem getMappingUint_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
  (getMappingUint s key).run state = ContractResult.success (state.storageMapUint s.slot key) state := rfl

@[simp] theorem setMappingUint_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Uint256) (state : ContractState) :
  (setMappingUint s key value).run state = ContractResult.success ()
    (state.writeMapUint s.slot key value) := rfl

def getMappingUintAddr (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) : Contract Address :=
  fun state => ContractResult.success (wordToAddress (state.readMapUint s.slot key)) state

def setMappingUintAddr (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Address) :
    Contract Unit :=
  setMappingUint s key (addressToWord value)

@[simp] theorem getMappingUintAddr_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (state : ContractState) :
  (getMappingUintAddr s key).run state =
    ContractResult.success (wordToAddress (state.storageMapUint s.slot key)) state := rfl

@[simp] theorem setMappingUintAddr_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (value : Address) (state : ContractState) :
  (setMappingUintAddr s key value).run state =
    (setMappingUint s key (addressToWord value)).run state := rfl

private def storageArraySetAt : List Uint256 → Nat → Uint256 → Option (List Uint256)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, idx + 1, value => do
      let updatedRest ← storageArraySetAt rest idx value
      some (head :: updatedRest)

private def storageArrayDropLast? : List Uint256 → Option (List Uint256)
  | [] => none
  | [_] => some []
  | head :: rest => do
      let updatedRest ← storageArrayDropLast? rest
      some (head :: updatedRest)

class StorageArrayElem (α : Type) where
  toWord : α → Uint256
  fromWord : Uint256 → α

instance : StorageArrayElem Uint256 where
  toWord value := value
  fromWord value := value

instance : StorageArrayElem Address where
  toWord value := addressToWord value
  fromWord value := wordToAddress value

instance : StorageArrayElem Bool where
  toWord value := boolToWord value
  fromWord value := value != 0

instance : StorageArrayElem (UIntN bits) where
  toWord value := Verity.Core.UIntN.toUint256 value
  fromWord value := Verity.Core.UIntN.ofUint256 bits value

-- Storage dynamic-array operations (#1571), routed through the canonical lens API
def getStorageArrayLength {α : Type} (s : StorageSlot (List α)) : Contract Uint256 :=
  fun state => ContractResult.success (((state.readArray s.slot).length : Nat) : Uint256) state

def getStorageArrayElement {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (index : Uint256) : Contract α :=
  fun state =>
    match (state.readArray s.slot)[index.val]? with
    | some value => ContractResult.success (StorageArrayElem.fromWord value) state
    | none => ContractResult.revert "Storage array index out of bounds" state

/-- Fixed-array source semantics: the declared length is authoritative and
    unmaterialized elements are Solidity's zero value. -/
def getFixedStorageArrayElement {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (size : Nat) (index : Uint256) : Contract α :=
  fun state =>
    if index.val < size then
      let value := (state.readArray s.slot)[index.val]?.getD 0
      ContractResult.success (StorageArrayElem.fromWord value) state
    else
      ContractResult.revert "Storage array index out of bounds" state

def pushStorageArray {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (value : α) : Contract Unit :=
  fun state =>
    ContractResult.success ()
      (state.writeArray s.slot (state.readArray s.slot ++ [StorageArrayElem.toWord value]))

def popStorageArray {α : Type} (s : StorageSlot (List α)) : Contract Unit :=
  fun state =>
    match storageArrayDropLast? (state.readArray s.slot) with
    | some updated => ContractResult.success () (state.writeArray s.slot updated)
    | none => ContractResult.revert "Storage array pop on empty array" state

def setStorageArrayElement {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (index : Uint256) (value : α) : Contract Unit :=
  fun state =>
    match storageArraySetAt (state.readArray s.slot) index.val (StorageArrayElem.toWord value) with
    | some updated => ContractResult.success () (state.writeArray s.slot updated)
    | none => ContractResult.revert "Storage array index out of bounds" state

/-- Update a fixed array after materializing its zero-initialized extent. -/
def setFixedStorageArrayElement {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (size : Nat) (index : Uint256) (value : α) : Contract Unit :=
  fun state =>
    if index.val < size then
      let taken := (state.readArray s.slot).take size
      let materialized := taken ++ List.replicate (size - taken.length) 0
      match storageArraySetAt materialized index.val (StorageArrayElem.toWord value) with
      | some updated => ContractResult.success () (state.writeArray s.slot updated)
      | none => ContractResult.revert "Storage array index out of bounds" state
    else
      ContractResult.revert "Storage array index out of bounds" state

@[simp] theorem getStorageArrayLength_run {α : Type} (s : StorageSlot (List α)) (state : ContractState) :
  (getStorageArrayLength s).run state =
    ContractResult.success (((state.storageArray s.slot).length : Nat) : Uint256) state := rfl

@[simp] theorem getStorageArrayElement_run_some {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (index : Uint256)
    (state : ContractState) (value : Uint256)
    (h : (state.storageArray s.slot)[index.val]? = some value) :
    (getStorageArrayElement s index).run state =
      ContractResult.success (StorageArrayElem.fromWord value) state := by
  simp [Contract.run, getStorageArrayElement, ContractState.readArray, h]

@[simp] theorem getStorageArrayElement_run_none {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (index : Uint256)
    (state : ContractState)
    (h : (state.storageArray s.slot)[index.val]? = none) :
    (getStorageArrayElement s index).run state =
      ContractResult.revert "Storage array index out of bounds" state := by
  simp [Contract.run, getStorageArrayElement, ContractState.readArray, h]

@[simp] theorem pushStorageArray_run {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α)) (value : α)
    (state : ContractState) :
  (pushStorageArray s value).run state = ContractResult.success () { state with
    storageArray := fun slot =>
      if slot == s.slot then state.storageArray s.slot ++ [StorageArrayElem.toWord value]
      else state.storageArray slot
  } := rfl

@[simp] theorem popStorageArray_run_some {α : Type} (s : StorageSlot (List α)) (state : ContractState)
    (updated : List Uint256)
    (h : storageArrayDropLast? (state.storageArray s.slot) = some updated) :
    (popStorageArray s).run state = ContractResult.success () { state with
      storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
    } := by
  simp [Contract.run, popStorageArray, ContractState.readArray, ContractState.writeArray, h]

@[simp] theorem popStorageArray_run_none {α : Type} (s : StorageSlot (List α)) (state : ContractState)
    (h : storageArrayDropLast? (state.storageArray s.slot) = none) :
    (popStorageArray s).run state =
      ContractResult.revert "Storage array pop on empty array" state := by
  simp [Contract.run, popStorageArray, ContractState.readArray, h]

@[simp] theorem setStorageArrayElement_run_some {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α))
    (index : Uint256) (value : α) (state : ContractState) (updated : List Uint256)
    (h : storageArraySetAt (state.storageArray s.slot) index.val (StorageArrayElem.toWord value) = some updated) :
    (setStorageArrayElement s index value).run state = ContractResult.success () { state with
      storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
    } := by
  simp [Contract.run, setStorageArrayElement, ContractState.readArray, ContractState.writeArray, h]

@[simp] theorem setStorageArrayElement_run_none {α : Type} [StorageArrayElem α]
    (s : StorageSlot (List α))
    (index : Uint256) (value : α) (state : ContractState)
    (h : storageArraySetAt (state.storageArray s.slot) index.val (StorageArrayElem.toWord value) = none) :
    (setStorageArrayElement s index value).run state =
      ContractResult.revert "Storage array index out of bounds" state := by
  simp [Contract.run, setStorageArrayElement, ContractState.readArray, h]

-- Event emission (#153)
def emitEvent (name : String) (args : List Uint256) (indexedArgs : List Uint256 := []) : Contract Unit :=
  fun state => ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
  }

@[simp] theorem emitEvent_run (name : String) (args : List Uint256) (indexedArgs : List Uint256) (state : ContractState) :
  (emitEvent name args indexedArgs).run state = ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
  } := rfl

-- Read-only context accessors
def msgSender : Contract Address :=
  fun state => ContractResult.success state.sender state

def contractAddress : Contract Address :=
  fun state => ContractResult.success state.thisAddress state

/-- `tx.origin` — the EOA at the root of the call chain.  Distinct
    from `msgSender`/`caller` when the call passes through a contract
    intermediary.  ERC-4337 v0.9's `nonReentrant` modifier uses
    `tx.origin == msg.sender` together with `extcodesize(msg.sender) ==
    0` to reject every contract caller. -/
def txOrigin : Contract Address :=
  fun state => ContractResult.success state.txOrigin state

def msgValue : Contract Uint256 :=
  fun state => ContractResult.success state.msgValue state

def selfBalance : Contract Uint256 :=
  fun state => ContractResult.success state.selfBalance state

def blockTimestamp : Contract Uint256 :=
  fun state => ContractResult.success state.blockTimestamp state

def blockNumber : Contract Uint256 :=
  fun state => ContractResult.success state.blockNumber state

protected def blobbasefee : Contract Uint256 :=
  fun state => ContractResult.success state.blobBaseFee state

def chainid : Contract Uint256 :=
  fun state => ContractResult.success state.chainId state

@[simp] theorem msgSender_run (state : ContractState) :
  msgSender.run state = ContractResult.success state.sender state := rfl

@[simp] theorem contractAddress_run (state : ContractState) :
  contractAddress.run state = ContractResult.success state.thisAddress state := rfl

@[simp] theorem txOrigin_run (state : ContractState) :
  txOrigin.run state = ContractResult.success state.txOrigin state := rfl

@[simp] theorem msgValue_run (state : ContractState) :
  msgValue.run state = ContractResult.success state.msgValue state := rfl

@[simp] theorem selfBalance_run (state : ContractState) :
  selfBalance.run state = ContractResult.success state.selfBalance state := rfl

@[simp] theorem blockTimestamp_run (state : ContractState) :
  blockTimestamp.run state = ContractResult.success state.blockTimestamp state := rfl

@[simp] theorem blockNumber_run (state : ContractState) :
  blockNumber.run state = ContractResult.success state.blockNumber state := rfl

@[simp] theorem blobbasefee_run (state : ContractState) :
  Verity.blobbasefee.run state = ContractResult.success state.blobBaseFee state := rfl

@[simp] theorem chainid_run (state : ContractState) :
  chainid.run state = ContractResult.success state.chainId state := rfl

-- Require guard (explicit failure on condition = false)
def require (condition : Bool) (message : String) : Contract Unit :=
  fun s => if condition
           then ContractResult.success () s
           else ContractResult.revert message s

/-- Reentrancy guard primitive.
Uses `lockSlot` as a mutex (`0` = unlocked, nonzero = locked), sets it before
running `body`, and clears it on both success and revert paths. -/
def nonReentrant (lockSlot : StorageSlot Uint256) (body : Contract α) : Contract α :=
  fun s =>
    if s.storage lockSlot.slot == 0 then
      let sLocked := (setStorage lockSlot 1).runState s
      match body sLocked with
      | ContractResult.success a s' =>
          ContractResult.success a ((setStorage lockSlot 0).runState s')
      | ContractResult.revert msg s' =>
          ContractResult.revert msg ((setStorage lockSlot 0).runState s')
    else
      ContractResult.revert "ReentrancyGuard: reentrant call" s

-- Simp lemmas for require
@[simp] theorem require_true (msg : String) (s : ContractState) :
  (require true msg).run s = ContractResult.success () s := rfl

@[simp] theorem require_false (msg : String) (s : ContractState) :
  (require false msg).run s = ContractResult.revert msg s := rfl

theorem require_succeeds (cond : Bool) (msg : String) (s : ContractState) :
  cond = true → (require cond msg).run s = ContractResult.success () s := by
  intro h; subst h; rfl

@[simp] theorem nonReentrant_locked_reverts
    (lockSlot : StorageSlot Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.storage lockSlot.slot ≠ 0) :
    (nonReentrant lockSlot body).run s =
      ContractResult.revert "ReentrancyGuard: reentrant call" s := by
  have hNe : (s.storage lockSlot.slot == 0) = false := by
    simp [hLocked]
  simp [Contract.run, nonReentrant, hNe]

/-- EIP-1153 transient-storage reentrancy guard primitive.

Uses the transient-storage slot at `lockOffset` as a mutex (`0` = unlocked,
nonzero = locked), sets it before running `body`, and clears it on both
success and revert paths. Mirrors OpenZeppelin's `ReentrancyGuardTransient`.

The transient-storage variant is preferred over storage-slot
`nonReentrant` for new contracts: it is automatically cleared at the end
of every transaction, eliminating the upgrade-related storage-layout
concerns of storage-slot guards. -/
def nonReentrantTransient (lockOffset : Uint256) (body : Contract α) : Contract α :=
  fun s =>
    if s.transientStorage (lockOffset : Nat) == 0 then
      let sLocked := s.writeTransient (lockOffset : Nat) 1
      match body sLocked with
      | ContractResult.success a s' =>
          ContractResult.success a (s'.writeTransient (lockOffset : Nat) 0)
      | ContractResult.revert msg s' =>
          ContractResult.revert msg (s'.writeTransient (lockOffset : Nat) 0)
    else
      ContractResult.revert "ReentrancyGuardTransient: reentrant call" s

@[simp] theorem nonReentrantTransient_locked_reverts
    (lockOffset : Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.transientStorage (lockOffset : Nat) ≠ 0) :
    (nonReentrantTransient lockOffset body).run s =
      ContractResult.revert "ReentrancyGuardTransient: reentrant call" s := by
  have hNe : (s.transientStorage (lockOffset : Nat) == 0) = false := by
    simp [hLocked]
  simp [Contract.run, nonReentrantTransient, hNe]

theorem nonReentrantTransient_revert_preserves_state
    (lockOffset : Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.transientStorage (lockOffset : Nat) ≠ 0) :
    ((nonReentrantTransient lockOffset body).run s).snd = s := by
  rw [nonReentrantTransient_locked_reverts lockOffset body s hLocked]
  rfl

-- Regression for #254: mutations before a revert do not leak through `run`.
theorem run_revert_rolls_back_storage (value : Uint256) (s : ContractState) :
  ((bind (setStorage ⟨0⟩ value) (fun _ => require false "revert")).run s) =
    ContractResult.revert "revert" s := by
  rfl

-- Monad instance for do-notation
instance : Monad Contract where
  pure := pure
  bind := bind

/-!
## Contract Monad Laws

The Contract monad satisfies all three monad laws, ensuring that do-notation
rewrites performed by Lean during elaboration preserve program semantics.
This eliminates a trust assumption noted in issue #146.
-/

-- Left identity: bind (pure a) f = f a
@[simp] theorem Contract.bind_pure_left (a : α) (f : α → Contract β) :
    bind (pure a) f = f a := rfl

-- Right identity: bind m pure = m
@[simp] theorem Contract.bind_pure_right (m : Contract α) :
    bind m pure = m := by
  funext s
  simp only [bind, pure]
  cases m s with
  | success a s' => rfl
  | revert msg s' => rfl

-- Associativity: bind (bind m f) g = bind m (fun x => bind (f x) g)
@[simp] theorem Contract.bind_assoc (m : Contract α) (f : α → Contract β) (g : β → Contract γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext s
  simp only [bind]
  cases m s with
  | success a s' => rfl
  | revert msg s' => rfl

end Verity
