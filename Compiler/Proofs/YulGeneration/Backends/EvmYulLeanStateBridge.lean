/-
  EvmYulLeanStateBridge: Type-level scaffolding for the Phase 2 state bridge
  between Verity's `YulState` and EVMYulLean's `SharedState .Yul`.

  This module defines the conversion functions needed to translate between
  Verity's flat execution state and EVMYulLean's account-map–based state.
  The conversion covers:

  1. **Variable bindings**: `List (String × Nat)` ↔ `VarStore` (Finmap)
  2. **Storage**: `Nat → Nat` ↔ `Storage` (TreeMap UInt256 UInt256)
  3. **Execution environment**: flat fields ↔ `ExecutionEnv .Yul`
  4. **Block information**: flat fields ↔ `BlockHeader`

  Phase 2 proof obligations (tracked in issue #1722):
  - Round-trip lemma: `fromSharedState (toSharedState s) = s` for observable fields
  - Storage read commutation: `sload` in EVMYulLean = Verity's storage lookup
  - Storage write commutation: `sstore` in EVMYulLean = Verity's storage update
  - Environment field extraction: `caller`/`address`/`timestamp`/etc. agree

  Design constraints:
  - Verity's `storage : Nat → Nat` is infinite-domain; EVMYulLean's `Storage`
    is finite (RBMap). The bridge only observes slots that were written.
  - Verity has no account model; EVMYulLean has `AccountMap`. The bridge
    creates a minimal single-account state.
  - Verity's calldata is `List Nat` (32-byte words); EVMYulLean's is `ByteArray`.
    The bridge converts between word-level and byte-level representations.
-/

import Compiler.Proofs.YulGeneration.RuntimeTypes
import EvmYul.Yul.State
import EvmYul.SharedState
import EvmYul.State.Account
import EvmYul.UInt256
import EvmYul.Maps.StorageMap
import Std.Data.TreeMap
import Std.Data.TreeSet


/-! ## Local ByteArray get? shim (canonical 4.31 surface)

Lean 4.31 `ByteArray` has no `get?`. Provide a typed local helper via `.data`
which reduces to `Array` operations with known `getElem_ofFn`/`append` lemmas.
-/

/-- Lean 4.31-compatible optional byte lookup used by bridge consumers. -/
def byteArrayGet? (a : ByteArray) (i : Nat) : Option UInt8 :=
  a.data[i]?

private theorem byteArrayGet?_ofFn {n : Nat} (f : Fin n → UInt8) (i : Nat) (hi : i < n) :
    byteArrayGet? (ByteArray.ofFn f) i = some (f ⟨i, hi⟩) := by
  simp [byteArrayGet?, ByteArray.data_ofFn, Array.getElem?_ofFn]
  simp [hi]

private theorem byteArrayGet?_append_left
    {a b : ByteArray} {i : Nat} (h : i < a.size) :
    byteArrayGet? (a ++ b) i = byteArrayGet? a i := by
  simp only [byteArrayGet?]
  simp [Array.getElem?_append_left h]

private theorem byteArrayGet?_append_right
    {a b : ByteArray} {i : Nat} (hle : a.size ≤ i)
    (h : i < (a ++ b).size) :
    byteArrayGet? (a ++ b) i = byteArrayGet? b (i - a.size) := by
  simp only [byteArrayGet?]
  simp [Array.getElem?_append_right hle]

/-! ## Std.TreeMap shims derived strictly from canonical Std lemmas

We derive `find?` alias + `get?_insert_*` / `get?_erase_self` from
`DTreeMap.Const.get?_insert` / `get?_erase_self` on the `.inner` representation.
Orientation follows `cmp k a = .eq` via `ReflCmp`.
-/

namespace Std.TreeMap

abbrev find? {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) (k : α) : Option β :=
  m.get? k

theorem get?_insert_of_eq {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) (k a : α) (v : β) (h : cmp k a = Ordering.eq) :
    (m.insert k v).get? a = some v := by
  simp only [TreeMap.get?, TreeMap.insert]
  simp [DTreeMap.Const.get?_insert, h]

theorem get?_insert_of_ne {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) (k k' : α) (v : β)
    (hne : cmp k k' ≠ Ordering.eq) :
    (m.insert k v).get? k' = m.get? k' := by
  simp only [TreeMap.get?, TreeMap.insert, DTreeMap.Const.get?_insert]
  simp [hne]

theorem get?_erase_self {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) (k : α) :
    (m.erase k).get? k = none := by
  simp only [TreeMap.get?, TreeMap.erase]
  exact DTreeMap.Const.get?_erase_self

/-- The `find?` spelling retained by native bridge proofs, derived from the
    canonical `TreeMap.get?` lemmas. -/
theorem find?_insert_of_eq {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) {k k' : α} {v : β} (h : cmp k' k = Ordering.eq) :
    (m.insert k v).find? k' = some v := by
  apply get?_insert_of_eq m k k' v
  simpa [h] using (Std.OrientedCmp.eq_swap (cmp := cmp) (a := k) (b := k'))

theorem find?_insert_of_ne {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) {k k' : α} {v : β} (h : cmp k' k ≠ Ordering.eq) :
    (m.insert k v).find? k' = m.find? k' := by
  apply get?_insert_of_ne m k k' v
  intro hEq
  apply h
  simpa [hEq] using (Std.OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k))

theorem find?_erase_self {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) (k : α) :
    (m.erase k).find? k = none :=
  get?_erase_self m k

theorem find?_erase_of_ne {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]
    (m : TreeMap α β cmp) {k k' : α} (h : cmp k' k ≠ Ordering.eq) :
    (m.erase k).find? k' = m.find? k' := by
  simp only [find?, TreeMap.get?, TreeMap.erase, DTreeMap.Const.get?_erase]
  have h' : cmp k k' ≠ Ordering.eq := by
    intro hEq
    apply h
    simpa [hEq] using (Std.OrientedCmp.eq_swap (cmp := cmp) (a := k') (b := k))
  simp [h']

end Std.TreeMap

namespace Compiler.Proofs.YulGeneration.Backends.StateBridge

open Compiler.Proofs.YulGeneration
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)
open EvmYul

/-- Stable wrapper to avoid any field-projection misparse during TreeMap migration.
    Mechanical 4.31 surface only. -/
private abbrev toEvmUInt256 (w : IRStorageWord) : UInt256 := IRStorageWord.toUInt256 w

/-! ## Nat ↔ UInt256 Conversions (declared early for shim use) -/

/-- Convert a Verity Nat value to an EVMYulLean UInt256. -/
abbrev natToUInt256 (n : Nat) : UInt256 := UInt256.ofNat n

/-- Convert an EVMYulLean UInt256 to a Verity Nat value. -/
abbrev uint256ToNat (u : UInt256) : Nat := u.toNat

/-! ## UInt256 compare shims (must precede any EvmYul.Storage use)

EvmYul.Storage = Std.TreeMap UInt256 UInt256 compare.
We provide the TransCmp instance + comparison facts early so that
`get?`/`insert` lemmas synthesize correctly on EvmYul.Storage terms.
-/

private theorem ordering_then_eq (o : Ordering) : o.then .eq = o := by
  cases o <;> rfl

private theorem UInt256_compare_eq_fin (a b : Fin UInt256.size) :
    @compare UInt256 _ (UInt256.mk a) (UInt256.mk b) = @compare (Fin UInt256.size) _ a b := by
  change (compare a b).then .eq = compare a b
  exact ordering_then_eq _

instance instTransCmpUInt256 : Std.TransCmp (α := UInt256) compare where
  eq_swap {a b} := by
    cases a with | mk va => cases b with | mk vb =>
    simp only [UInt256_compare_eq_fin]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} hab hbc := by
    cases a with | mk va => cases b with | mk vb => cases c with | mk vc =>
    simp only [UInt256_compare_eq_fin] at hab hbc ⊢
    exact Std.TransCmp.isLE_trans hab hbc

theorem UInt256_eq_of_compare_eq {u v : UInt256}
    (h : compare u v = Ordering.eq) : u = v := by
  cases u with | mk uv =>
  cases v with | mk vv =>
  rw [UInt256_compare_eq_fin] at h
  have heq : uv = vv := Std.LawfulEqCmp.eq_of_compare h
  subst heq
  rfl

theorem natToUInt256_injective {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : natToUInt256 a = natToUInt256 b) : a = b := by
  have hval : a % UInt256.size = b % UInt256.size := by
    have := congrArg (fun u => u.val.val) h
    simpa [natToUInt256, UInt256.ofNat, Id.run, Fin.ofNat] using this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval

theorem compare_natToUInt256_ne {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hab : a ≠ b) :
    compare (natToUInt256 a) (natToUInt256 b) ≠ Ordering.eq := by
  intro heq
  exact hab (natToUInt256_injective ha hb (UInt256_eq_of_compare_eq heq))

/-! ## Variable Store Bridge

Verity uses `List (String × Nat)` for variable bindings (most recent first).
EVMYulLean uses `VarStore` which is `Finmap (λ _ : String ↦ UInt256)`.

Key semantic difference: Verity's list-based store allows shadowing (duplicate
keys); `getVar` returns the *first* match. EVMYulLean's Finmap is a map
(unique keys). The bridge takes the most recent binding for each variable. -/

/-- Convert Verity variable bindings to EVMYulLean VarStore.
    Uses foldl so that the first (most recent) binding for each variable wins,
    matching Verity's `getVar` shadowing semantics.

    Note: We use the expanded Finmap type rather than the VarStore abbrev
    throughout this definition because Lean 4's unifier does not always
    unfold abbrevs when matching against Finmap's universe-polymorphic
    structure.  The result is still VarStore-compatible since VarStore is
    a transparent abbreviation. -/
noncomputable def varsToVarStore (vars : List (String × Nat)) :
    Finmap (fun _ : Identifier => Literal) :=
  vars.foldl (init := (∅ : Finmap (fun _ : Identifier => Literal)))
    fun store (name, val) =>
      let id : Identifier := name
      if (Finmap.lookup id store).isSome then store
      else Finmap.insert id (natToUInt256 val) store

/-- Convert EVMYulLean VarStore back to Verity variable bindings.
    Order is not preserved (Finmap has no canonical ordering). -/
noncomputable def varStoreToVars (store : Finmap (fun _ : Identifier => Literal)) :
    List (String × Nat) :=
  store.entries.toList.map fun ⟨name, val⟩ => ((name : String), uint256ToNat val)

/-! ## Storage Bridge

Verity uses `Nat → Nat` (total function, default 0 for unwritten slots).
EVMYulLean uses `Storage` = `TreeMap UInt256 UInt256` (finite map, default 0).

The round-trip requires knowing which slots are "observable" — the bridge
can only reconstruct slots that are in the EVMYulLean TreeMap. For the
forward direction (Verity → EVMYulLean), we need to know which slots to
project. In practice, this is the set of slots written during execution. -/

/-- Look up a storage slot in EVMYulLean's Storage map, returning 0 for
    unwritten slots (matching Verity's `Nat → Nat` semantics). -/
def storageLookup (s : EvmYul.Storage) (slot : UInt256) : UInt256 :=
  match s.find? slot with
  | some val => val
  | none => ⟨0⟩

/-- Write a storage slot in EVMYulLean's Storage map. -/
def storageWrite (s : EvmYul.Storage) (slot val : UInt256) : EvmYul.Storage :=
  s.insert slot val

/-- Project a finite set of Verity storage slots into an EVMYulLean Storage map.

Nat slot inputs are normalized through `IRStorageSlot.ofNat`, matching the
EVMYulLean `UInt256` key used in the projected map. -/
def projectStorage (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) : EvmYul.Storage :=
  slots.foldl (init := (Std.TreeMap.empty : EvmYul.Storage)) fun acc slot =>
    let key := natToUInt256 slot
    let val := toEvmUInt256 (storage (IRStorageSlot.ofNat slot))
    acc.insert key val

/-! ## Execution Environment Bridge

Maps Verity's flat YulState fields to EVMYulLean's `ExecutionEnv .Yul`. -/

/-- Convert a Verity address (Nat) to an EVMYulLean AccountAddress.
    EVMYulLean's AccountAddress is `Fin (2^160)`. -/
def natToAddress (n : Nat) : AccountAddress :=
  ⟨n % (2 ^ 160), Nat.mod_lt _ (by decide)⟩

/-- Create a minimal EVMYulLean BlockHeader from Verity's block fields.
    Fields not modeled by Verity (e.g. baseFeePerGas, gasLimit) are set to
    default zero values. EVMYulLean derives `blobbasefee()` from
    `excessBlobGas`, so this zero header represents only
    `EvmYul.MIN_BASE_FEE_PER_BLOB_GAS`; the native harness fails closed when a
    selected runtime path reads `blobbasefee()` with any other transaction
    `blobBaseFee`. -/
def mkBlockHeader (state : YulState) : BlockHeader :=
  { parentHash := ⟨0⟩
    ommersHash := ⟨0⟩
    beneficiary := ⟨0, by decide⟩
    stateRoot := ⟨0⟩
    transRoot := ByteArray.empty
    receiptRoot := ByteArray.empty
    logsBloom := ByteArray.empty
    difficulty := 0
    number := state.blockNumber
    gasLimit := 0
    gasUsed := 0
    timestamp := state.blockTimestamp
    extraData := ByteArray.empty
    nonce := ⟨0, by decide⟩
    prevRandao := ⟨0⟩
    baseFeePerGas := 0
    parentBeaconBlockRoot := ByteArray.empty
    withdrawalsRoot := ByteArray.empty
    blobGasUsed := ⟨0, by decide⟩
    excessBlobGas := ⟨0, by decide⟩ }

/-- Convert Verity calldata (List of 32-byte words) to EVMYulLean calldata
    (ByteArray). Each word is encoded as a big-endian 32-byte chunk.
    Prepends the 4-byte function selector. -/
def calldataToByteArray (selector : Nat) (calldata : List Nat) : ByteArray :=
  -- 4 bytes for selector + 32 bytes per word
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes (w : Nat) : ByteArray :=
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  calldata.foldl (init := selectorBytes) fun acc w => acc ++ wordBytes w

private theorem calldataToByteArray_selectorBytes_size (selector : Nat) :
    (ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)).size = 4 := by
  simp

private theorem calldataToByteArray_wordBytes_size (w : Nat) :
    (ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)).size = 32 := by
  simp

private theorem calldataToByteArray_fold_size
    (wordBytes : Nat → ByteArray)
    (hWord : ∀ w, (wordBytes w).size = 32) :
    ∀ (acc : ByteArray) (calldata : List Nat),
      (calldata.foldl (init := acc) fun acc w => acc ++ wordBytes w).size =
        acc.size + calldata.length * 32 := by
  intro acc calldata
  induction calldata generalizing acc with
  | nil =>
      simp
  | cons w ws ih =>
      simp [List.foldl_cons, ByteArray.size_append, hWord, ih, Nat.add_assoc]
      omega

private theorem calldataToByteArray_fold_get?_left
    (wordBytes : Nat → ByteArray)
    (hWord : ∀ w, (wordBytes w).size = 32) :
    ∀ (acc : ByteArray) (calldata : List Nat) (i : Nat), i < acc.size →
      byteArrayGet? (calldata.foldl (init := acc) fun acc w => acc ++ wordBytes w) i =
        byteArrayGet? acc i := by
  intro acc calldata
  induction calldata generalizing acc with
  | nil =>
      intro i h
      rfl
  | cons w ws ih =>
      intro i h
      simp only [List.foldl_cons]
      calc
        byteArrayGet? (ws.foldl (init := acc ++ wordBytes w) fun acc w => acc ++ wordBytes w) i
            = byteArrayGet? (acc ++ wordBytes w) i := by
                apply ih
                rw [ByteArray.size_append, hWord]
                omega
        _ = byteArrayGet? acc i := byteArrayGet?_append_left h

private theorem calldataToByteArray_fold_get?_word
    (wordBytes : Nat → ByteArray)
    (hWord : ∀ w, (wordBytes w).size = 32)
    (hByte :
      ∀ w i, i < 32 →
        byteArrayGet? (wordBytes w) i =
          some (UInt8.ofNat (w / 2^((31 - i) * 8) % 256))) :
    ∀ (acc : ByteArray) (calldata : List Nat) (idx arg : Nat)
      (rest : List Nat) (i : Nat),
      calldata.drop idx = arg :: rest →
      i < 32 →
      byteArrayGet? (calldata.foldl (init := acc) fun acc w => acc ++ wordBytes w) (acc.size + 32 * idx + i) =
        some (UInt8.ofNat (arg / 2^((31 - i) * 8) % 256)) := by
  intro acc calldata idx
  induction idx generalizing acc calldata with
  | zero =>
      intro arg rest i hdrop hi
      simp only [List.drop_zero] at hdrop
      subst calldata
      simp only [List.foldl_cons]
      rw [calldataToByteArray_fold_get?_left wordBytes hWord]
      · rw [byteArrayGet?_append_right]
        · simpa using hByte arg i hi
        · omega
        · rw [ByteArray.size_append, hWord]
          omega
      · rw [ByteArray.size_append, hWord]
        omega
  | succ idx ih =>
      intro arg rest i hdrop hi
      cases calldata with
      | nil =>
          simp at hdrop
      | cons head tail =>
          simp only [List.drop_succ_cons] at hdrop
          simp only [List.foldl_cons]
          have h := ih (acc ++ wordBytes head) tail arg rest i hdrop hi
          simpa [ByteArray.size_append, hWord, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h

/-- The bridged calldata byte array has the same observable length as Verity's
    `calldatasize`: 4 selector bytes plus 32 bytes per calldata word. -/
theorem calldataToByteArray_size (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).size = 4 + calldata.length * 32 := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hSel : selectorBytes.size = 4 := by
    simp [selectorBytes]
  have hWord : ∀ w, (wordBytes w).size = 32 := by
    intro w
    simp [wordBytes]
  have hFold := calldataToByteArray_fold_size wordBytes hWord selectorBytes calldata
  simpa [selectorBytes, wordBytes, hSel] using hFold

@[simp] theorem calldataToByteArray_selectorByte0 (selector : Nat) (calldata : List Nat) :
    byteArrayGet? (calldataToByteArray selector calldata) 0 =
      some (UInt8.ofNat (selector / 2^24 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · simp [byteArrayGet?_append_right, byteArrayGet?_ofFn, selectorBytes]
  · simp

@[simp] theorem calldataToByteArray_selectorByte1 (selector : Nat) (calldata : List Nat) :
    byteArrayGet? (calldataToByteArray selector calldata) 1 =
      some (UInt8.ofNat (selector / 2^16 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · simp [byteArrayGet?_append_right, byteArrayGet?_ofFn, selectorBytes]
  · simp

@[simp] theorem calldataToByteArray_selectorByte2 (selector : Nat) (calldata : List Nat) :
    byteArrayGet? (calldataToByteArray selector calldata) 2 =
      some (UInt8.ofNat (selector / 2^8 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · simp [byteArrayGet?_append_right, byteArrayGet?_ofFn, selectorBytes]
  · simp

@[simp] theorem calldataToByteArray_selectorByte3 (selector : Nat) (calldata : List Nat) :
    byteArrayGet? (calldataToByteArray selector calldata) 3 =
      some (UInt8.ofNat (selector % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · simp [byteArrayGet?_append_right, byteArrayGet?_ofFn, selectorBytes]
  · simp

/-- Byte-level projection for any aligned ABI argument word in bridged calldata.
    If `calldata.drop idx = arg :: rest`, then byte `4 + 32*idx + i` is the
    `i`th big-endian byte of `arg`. -/
theorem calldataToByteArray_argByte_of_drop_eq_cons
    (selector : Nat) (calldata : List Nat) (idx arg : Nat) (rest : List Nat)
    (hdrop : calldata.drop idx = arg :: rest) (i : Nat) (hi : i < 32) :
    byteArrayGet? (calldataToByteArray selector calldata) (4 + 32 * idx + i) =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  have hByte :
      ∀ w i, i < 32 →
        byteArrayGet? (wordBytes w) i =
          some (UInt8.ofNat (w / 2^((31 - i) * 8) % 256)) := by
    intro w i hi
    -- Mechanical: keep the Fin function and pass to the ofFn shim (exact-head 4.31 surface)
    let f : Fin 32 → UInt8 := fun j => UInt8.ofNat (w / 2^((31 - j.1) * 8) % 256)
    exact byteArrayGet?_ofFn f i hi
  have h :=
    calldataToByteArray_fold_get?_word wordBytes hWord hByte selectorBytes
      calldata idx arg rest i hdrop hi
  simpa [selectorBytes, wordBytes] using h

/-- Byte-level projection for the first ABI argument word in bridged calldata.
    This is the offset-4 calldata analogue of the selector byte lemmas above:
    byte `4 + i` is the `i`th big-endian byte of the first 32-byte argument. -/
theorem calldataToByteArray_arg0Byte
    (selector arg : Nat) (rest : List Nat) (i : Nat) (hi : i < 32) :
    byteArrayGet? (calldataToByteArray selector (arg :: rest)) (4 + i) =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  exact calldataToByteArray_argByte_of_drop_eq_cons selector (arg :: rest) 0 arg rest rfl i hi

/-! ## Full State Conversion

The main bridge functions that convert between Verity's YulState and
EVMYulLean's Yul execution state. -/

/-- Convert Verity's YulState to an EVMYulLean SharedState.
    Requires the set of observable storage slots for projection. -/
def toSharedState (state : YulState) (observableSlots : List Nat) :
    SharedState .Yul :=
  let addr := natToAddress state.thisAddress
  let storage := projectStorage state.storage observableSlots
  let emptyCode : Yul.Ast.contractCode .Yul := Inhabited.default
  let account : Account .Yul :=
    { nonce := ⟨0⟩
      balance := ⟨0⟩
      storage := storage
      code := emptyCode
      tstorage := Std.TreeMap.empty }
  let accountMap : AccountMap .Yul :=
    (Std.TreeMap.empty).insert addr account
  let execEnv : ExecutionEnv .Yul :=
    { codeOwner := addr
      sender := natToAddress state.sender
      source := natToAddress state.sender
      weiValue := natToUInt256 state.msgValue
      calldata := calldataToByteArray state.selector state.calldata
      code := emptyCode
      gasPrice := 0
      header := mkBlockHeader state
      depth := 0
      perm := false
      blobVersionedHashes := [] }
  { -- State τ fields
    accountMap := accountMap
    σ₀ := Std.TreeMap.empty
    totalGasUsedInBlock := 0
    transactionReceipts := #[]
    substate := Inhabited.default
    executionEnv := execEnv
    blocks := #[]
    genesisBlockHeader := mkBlockHeader state
    createdAccounts := Std.TreeSet.empty
    -- MachineState fields
    gasAvailable := ⟨0⟩
    activeWords := ⟨0⟩
    memory := ByteArray.empty
    returnData := ByteArray.empty
    H_return := ByteArray.empty }

/-- Extract observable storage from an EVMYulLean state for the contract
    at the given address. Returns the Verity-style storage function.

The bounded IR slot is already the EVM storage key, so extraction is lossless
with respect to the IR storage domain. -/
def extractStorage (sharedState : SharedState .Yul) (addr : AccountAddress) :
    IRStorageSlot → IRStorageWord :=
  fun slot =>
    match sharedState.accountMap.get? addr with
    | some account =>
      match account.storage.get? (IRStorageSlot.toUInt256 slot) with
      | some val => val
      | none => 0
    | none => 0

/-! ## Storage Bridge Proofs -/

/-- Helper: folding inserts over a list of slots that does NOT contain `slot`
    preserves whatever `find?` value the accumulator had for `natToUInt256 slot`. -/
theorem foldl_insert_find_not_mem (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hNotMem : slot ∉ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (hSlotRange : slot < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (toEvmUInt256 (storage (IRStorageSlot.ofNat s)))) acc).get? (natToUInt256 slot) = acc.get? (natToUInt256 slot) := by
  induction slots generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hNotMemTl : slot ∉ tl := fun h => hNotMem (List.mem_cons_of_mem _ h)
    have hne : hd ≠ slot := fun h => hNotMem (h ▸ List.mem_cons_self)
    have hd_range : hd < UInt256.size := hRange hd (List.mem_cons_self)
    rw [ih hNotMemTl (fun s hs => hRange s (List.mem_cons_of_mem _ hs))]
    -- compare_natToUInt256_ne expects (ha hb hab) for compare (natToUInt256 a) (natToUInt256 b) ≠ eq
    -- Here we need cmp (nat hd) (nat slot) ≠ eq  (k=hd inserted, k'=slot looked up)
    exact Std.TreeMap.get?_insert_of_ne acc (natToUInt256 hd) (natToUInt256 slot)
      (toEvmUInt256 (storage (IRStorageSlot.ofNat hd)))
      (compare_natToUInt256_ne hd_range hSlotRange hne)

/-- Helper: after folding a suffix of slots into an accumulator, if `slot`
    is in that suffix, then the accumulated map contains the right value.

    This generalizes `storageLookup_projectStorage` to work with any
    accumulator (not just `empty`), which is needed for the induction. -/
theorem foldl_insert_find (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (toEvmUInt256 (storage (IRStorageSlot.ofNat s)))) acc).get? (natToUInt256 slot) = some (toEvmUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact absurd hSlot List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hSlot with
    | inl heq =>
      subst heq
      by_cases hmem : slot ∈ tl
      · -- slot also appears later in tl; the last insert wins with same value
        exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _
      · -- slot not in tl: the fold over tl preserves the inserted value
        have hSlotRange : slot < UInt256.size := hRange slot (List.mem_cons_self)
        rw [foldl_insert_find_not_mem storage tl slot hmem
          (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) hSlotRange]
        exact Std.TreeMap.get?_insert_of_eq acc (natToUInt256 slot) (natToUInt256 slot)
          (toEvmUInt256 (storage (IRStorageSlot.ofNat slot))) Std.ReflCmp.compare_self
    | inr hmem =>
      exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _

/-- Equal projected EVM storage keys denote equal bounded IR storage slots. -/
theorem IRStorageSlot_ofNat_eq_of_natToUInt256_eq {a b : Nat}
    (h : natToUInt256 a = natToUInt256 b) :
    IRStorageSlot.ofNat a = IRStorageSlot.ofNat b := by
  simpa [natToUInt256, IRStorageSlot.ofNat] using h

/-- Folding projected storage slots preserves an already-correct lookup for a
    bounded target key. Any later Nat alias for the same EVM key writes the same
    bounded IR slot value, so no Nat range/injectivity hypothesis is needed. -/
theorem foldl_insert_preserves_find_projected_value
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (acc : EvmYul.Storage)
    (hAcc :
      acc.get? (natToUInt256 slot) =
        some (toEvmUInt256 (storage (IRStorageSlot.ofNat slot)))) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (toEvmUInt256 (storage (IRStorageSlot.ofNat s)))) acc).get? (natToUInt256 slot) =
        some (toEvmUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact hAcc
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      by_cases hcmp : compare (natToUInt256 slot) (natToUInt256 hd) = Ordering.eq
      · have hkey : natToUInt256 slot = natToUInt256 hd :=
          UInt256_eq_of_compare_eq hcmp
        have hslot : IRStorageSlot.ofNat hd = IRStorageSlot.ofNat slot :=
          (IRStorageSlot_ofNat_eq_of_natToUInt256_eq hkey.symm)
        apply ih
        -- After hkey the keys are equal; use the self-insert lemma with Refl (mechanical 4.31).
        rw [hkey]
        rw [Std.TreeMap.get?_insert_of_eq acc (natToUInt256 hd) (natToUInt256 hd)
              (toEvmUInt256 (storage (IRStorageSlot.ofNat hd))) Std.ReflCmp.compare_self]
        simp [hslot]
      · apply ih
        have hne : compare (natToUInt256 hd) (natToUInt256 slot) ≠ Ordering.eq := by
          intro heq
          -- If cmp hd slot = eq then hd = slot (UInt), hence cmp slot hd = eq by refl; contradicts hcmp
          have h_eq : natToUInt256 hd = natToUInt256 slot := UInt256_eq_of_compare_eq heq
          have : compare (natToUInt256 slot) (natToUInt256 hd) = Ordering.eq := by
            rw [h_eq]
            exact Std.ReflCmp.compare_self
          exact hcmp this
        rw [Std.TreeMap.get?_insert_of_ne acc (natToUInt256 hd) (natToUInt256 slot) (toEvmUInt256 (storage (IRStorageSlot.ofNat hd))) hne]
        exact hAcc

/-- Helper: after folding a suffix of Nat slots into an accumulator, if `slot`
    appears in that suffix, then the accumulated projected map contains the
    bounded value for `slot`.

    This form deliberately has no Nat range hypothesis: slots that alias
    modulo `2^256` denote the same `IRStorageSlot` and therefore write the
    same projected value. -/
theorem foldl_insert_find_projected (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s =>
        m.insert (natToUInt256 s)
          (toEvmUInt256 (storage (IRStorageSlot.ofNat s)))) acc).find? (natToUInt256 slot) =
        some (toEvmUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact absurd hSlot List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hSlot with
    | inl heq =>
      subst heq
      apply foldl_insert_preserves_find_projected_value
      rw [Std.TreeMap.get?_insert_of_eq acc (natToUInt256 slot) (natToUInt256 slot)
        (toEvmUInt256 (storage (IRStorageSlot.ofNat slot))) Std.ReflCmp.compare_self]
    | inr hmem => exact ih hmem _

/-- Storage lookup commutes: reading a slot from the projected storage
    yields the same value as reading it from Verity's storage function.

    The `hRange` hypothesis ensures `natToUInt256` is injective on the
    slot list (EVM storage slots are always < 2^256). Without it, two
    distinct Nat slots could collide under modular reduction and the
    last-write-wins semantics of `foldl` would make the theorem false. -/
theorem storageLookup_projectStorage (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (_hRange : ∀ s ∈ slots, s < UInt256.size) :
    storageLookup (projectStorage storage slots) (natToUInt256 slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [storageLookup, projectStorage]
  rw [foldl_insert_find_projected storage slots slot hSlot]
  rfl

/-- Range-free storage lookup for projected bounded IR storage. -/
theorem storageLookup_projectStorage_projected
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots) :
    storageLookup (projectStorage storage slots) (natToUInt256 slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [storageLookup, projectStorage]
  rw [foldl_insert_find_projected storage slots slot hSlot]
  rfl

/-- Nat→UInt256→Nat round-trip for values in range.
    Proof: `ofNat n = ⟨Fin.ofNat _ n⟩ = ⟨⟨n % size, _⟩⟩`, and
    `toNat` extracts `.val.val`, so the goal reduces to `n % size = n`
    which follows from `Nat.mod_eq_of_lt h`. -/
theorem uint256_roundtrip (n : Nat) (h : n < UInt256.size) :
    uint256ToNat (natToUInt256 n) = n := by
  simp only [uint256ToNat, natToUInt256, UInt256.toNat, UInt256.ofNat, Id.run]
  exact Nat.mod_eq_of_lt h

end Compiler.Proofs.YulGeneration.Backends.StateBridge
