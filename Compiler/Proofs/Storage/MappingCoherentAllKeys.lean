/-
  C5 step 4 (final slice): global all-keys shadow-vs-flat coherence.

  `storageKeySlot` here is the field-list form promised by issue #2330:
  it takes the declared `CompilationModel.Field` layout and collapses a
  source `StorageKey` to the flat `Channel` and compiler slot it must
  agree with. The layout is load-bearing, not decoration:

  * a persistent root word backed by a `dynamicArray` field has no flat
    word counterpart (`encodeStorageAt` reads a list length there), so it
    collapses to `none`;
  * a mapping entry collapses only when the declared field at its base
    slot has the matching key shape. Distinct base slots alone do not
    imply distinct hashed locations.

  `MappingCoherentAllKeys` is the all-keys (∀ `StorageKey`) form, not a
  single-key or listed-pair form. It is useful for initialization and
  mapping-free contracts. Aligned mapping writes instead preserve the
  finite `MappingCoherentOnKeys` relation under `LayoutNonAliasOn`.

  Trust: non-alias evidence covers only the supplied accessed footprint,
  including reserved non-mapping slots when they are tracked. No global
  injectivity assumption or project axiom is used.
-/

import Compiler.Proofs.Storage.FieldEncode

namespace Compiler.Proofs.Storage.MappingCoherentGlobal

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Proofs.Storage.FieldEncode
open Compiler.Proofs.IRGeneration.SourceSemantics

/-- Flat read channel a source key collapses into.

    `contract c` stays a channel of its own for every `c`, including `0`:
    the model does not identify `StorageKey.contractSlot 0 n` with
    `StorageKey.slot n`, and claiming it would be broken by a plain
    `writeSlot`. -/
inductive Channel where
  | persistent
  | address
  | transient
  | contract (c : Nat)
  deriving DecidableEq, Repr

/-- Flat-channel read at a compiler slot. -/
def channelRead (s : ContractState) : Channel → Nat → Uint256
  | .persistent, n => s.storage n
  | .address, n => s.storageWords (.addr n)
  | .transient, n => s.storageWords (.transient n)
  | .contract c, n => s.storageWords (.contractSlot c n)

/-- Declared mapping key shape at a resolved persistent base slot. -/
def fieldMapKindAt (fields : List Field) (n : Nat) : Option MappingType :=
  match findResolvedFieldAtSlot fields n with
  | some f => match f.ty with
    | .mappingTyped mt => some mt
    | _ => none
  | none => none

/-- One resolved slot carries at most one declared mapping shape, so two
    distinct declared shapes force distinct base slots. This is the layout
    fact that separates the mapping channels. -/
theorem base_ne_of_kind_ne {fields : List Field} {n n' : Nat} {mt mt' : MappingType}
    (h : fieldMapKindAt fields n = some mt) (h' : fieldMapKindAt fields n' = some mt')
    (hne : mt ≠ mt') : n ≠ n' := by
  intro heq
  subst heq
  rw [h] at h'
  exact hne (Option.some.inj h')

/-- Layout-checked collapse of a source key to its flat channel and
    compiler slot. `none` marks a key with no flat word counterpart under
    this layout. -/
def storageKeySlot (fields : List Field) : StorageKey → Option (Channel × Nat)
  | .slot n =>
      match findResolvedFieldAtSlot fields n with
      | some f => if fieldUsesDynamicArrayStorage f then none else some (.persistent, n)
      | none => some (.persistent, n)
  | .addr n => some (.address, n)
  | .transient n => some (.transient, n)
  | .contractSlot c n => some (.contract c, n)
  | .scoped _ _ => none
  -- Hashed mapping chains are related to the flat channel by
  -- `Compiler.Proofs.Storage.HashedMappingLayout`, not by this layout table.
  | .mapChain _ _ _ => none
  | .transientMapChain _ _ => none
  | .map n key =>
      match fieldMapKindAt fields n with
      | some (.simple .address) =>
          some (.persistent, solidityMappingSlot n (addressToWord key).val)
      | _ => none
  | .mapUint n key =>
      match fieldMapKindAt fields n with
      | some (.simple .uint256) => some (.persistent, solidityMappingSlot n key.val)
      | _ => none
  | .map2 n k1 k2 =>
      match fieldMapKindAt fields n with
      | some (.nested .address .address) =>
          some (.persistent,
            abstractNestedMappingSlot n (addressToWord k1).val (addressToWord k2).val)
      | _ => none

/-- Source keys whose flat image is a keccak-derived mapping slot. -/
def isMappingEntryKey : StorageKey → Bool
  | .map _ _ => true
  | .mapUint _ _ => true
  | .map2 _ _ _ => true
  | _ => false

/-- **Global all-keys shadow-vs-flat coherence.** Every source key that the
    declared layout collapses to a flat channel holds the same word as that
    flat channel at the derived compiler slot. Quantified over all
    `StorageKey`s — not a single key and not a listed finite set. -/
def MappingCoherentAllKeys (fields : List Field) (s : ContractState) : Prop :=
  ∀ (k : StorageKey) (ch : Channel) (n : Nat),
    storageKeySlot fields k = some (ch, n) → s.storageWords k = channelRead s ch n

/-- Coherence only at the finite accessed footprint. Global coherence is useful
    for mapping-free layouts and initialization, but mapping writes preserve this
    finite relation rather than claiming preservation at every possible key. -/
def MappingCoherentOnKeys (fields : List Field) (accessed : List StorageKey)
    (s : ContractState) : Prop :=
  ∀ k ∈ accessed, ∀ ch n,
    storageKeySlot fields k = some (ch, n) → s.storageWords k = channelRead s ch n

/-- Distinct accessed symbolic keys must have distinct locations in each flat
    channel. Include reserved scalar keys in `accessed` to certify separation
    from non-mapping storage as well as mapping-vs-mapping separation. -/
def LayoutNonAliasOn (fields : List Field) (accessed : List StorageKey) : Prop :=
  ∀ k ∈ accessed, ∀ k' ∈ accessed, ∀ ch n n',
    storageKeySlot fields k = some (ch, n) →
    storageKeySlot fields k' = some (ch, n') → k ≠ k' → n ≠ n'

/-- Layout certificate: a declared mapping base slot is never itself a
    keccak-derived slot. Same shape as the image-avoidance `∀` already
    taken by `writeSlot_preserves_mappingCoherent`; not an axiom. -/
def MappingBasesNotDerived (fields : List Field) : Prop :=
  ∀ n : Nat, (fieldMapKindAt fields n).isSome → ∀ b k : Nat, solidityMappingSlot b k ≠ n

/-- Every declared mapping base slot is an in-range EVM storage key.
    This range property does not establish collision freedom. -/
def MappingBasesInRange (fields : List Field) : Prop :=
  ∀ n : Nat, (fieldMapKindAt fields n).isSome → n < Compiler.Constants.evmModulus

/-- `n` is not the flat image of any layout-derived mapping entry. -/
def DerivedMappingSlotsAvoid (fields : List Field) (n : Nat) : Prop :=
  ∀ (k : StorageKey) (ch : Channel) (m : Nat),
    storageKeySlot fields k = some (ch, m) → isMappingEntryKey k = true → m ≠ n

/-! ### Shape lemmas for the collapse -/

theorem storageKeySlot_slot_eq {fields : List Field} {m : Nat} {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.slot m) = some (ch, n)) :
    ch = .persistent ∧ n = m := by
  simp only [storageKeySlot] at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem storageKeySlot_addr_eq {fields : List Field} {m : Nat} {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.addr m) = some (ch, n)) :
    ch = .address ∧ n = m := by
  simp only [storageKeySlot, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem storageKeySlot_transient_eq {fields : List Field} {m : Nat} {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.transient m) = some (ch, n)) :
    ch = .transient ∧ n = m := by
  simp only [storageKeySlot, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem storageKeySlot_contractSlot_eq {fields : List Field} {c m : Nat} {ch : Channel}
    {n : Nat} (h : storageKeySlot fields (.contractSlot c m) = some (ch, n)) :
    ch = .contract c ∧ n = m := by
  simp only [storageKeySlot, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- A collapsing `.map` key pins both the declared shape at its base slot and
    the derived flat slot. -/
theorem storageKeySlot_map_eq {fields : List Field} {m : Nat} {key : Address}
    {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.map m key) = some (ch, n)) :
    fieldMapKindAt fields m = some (.simple .address) ∧ ch = .persistent ∧
      n = solidityMappingSlot m (addressToWord key).val := by
  simp only [storageKeySlot] at h
  split at h
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨heq, h.1.symm, h.2.symm⟩
  · simp at h

theorem storageKeySlot_mapUint_eq {fields : List Field} {m : Nat} {key : Uint256}
    {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.mapUint m key) = some (ch, n)) :
    fieldMapKindAt fields m = some (.simple .uint256) ∧ ch = .persistent ∧
      n = solidityMappingSlot m key.val := by
  simp only [storageKeySlot] at h
  split at h
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨heq, h.1.symm, h.2.symm⟩
  · simp at h

theorem storageKeySlot_map2_eq {fields : List Field} {m : Nat} {k1 k2 : Address}
    {ch : Channel} {n : Nat}
    (h : storageKeySlot fields (.map2 m k1 k2) = some (ch, n)) :
    fieldMapKindAt fields m = some (.nested .address .address) ∧ ch = .persistent ∧
      n = abstractNestedMappingSlot m (addressToWord k1).val (addressToWord k2).val := by
  simp only [storageKeySlot] at h
  split at h
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨heq, h.1.symm, h.2.symm⟩
  · simp at h

/-- The declared `.map` collapse in the forward direction. -/
theorem storageKeySlot_map_of_kind {fields : List Field} {m : Nat} (key : Address)
    (hkind : fieldMapKindAt fields m = some (.simple .address)) :
    storageKeySlot fields (.map m key) =
      some (.persistent, solidityMappingSlot m (addressToWord key).val) := by
  simp only [storageKeySlot, hkind]

theorem storageKeySlot_mapUint_of_kind {fields : List Field} {m : Nat} (key : Uint256)
    (hkind : fieldMapKindAt fields m = some (.simple .uint256)) :
    storageKeySlot fields (.mapUint m key) =
      some (.persistent, solidityMappingSlot m key.val) := by
  simp only [storageKeySlot, hkind]

theorem storageKeySlot_map2_of_kind {fields : List Field} {m : Nat} (k1 k2 : Address)
    (hkind : fieldMapKindAt fields m = some (.nested .address .address)) :
    storageKeySlot fields (.map2 m k1 k2) =
      some (.persistent,
        abstractNestedMappingSlot m (addressToWord k1).val (addressToWord k2).val) := by
  simp only [storageKeySlot, hkind]

/-! ### Relation to the per-channel globals -/

/-- The all-keys invariant follows from the three per-channel globals for
    **any** field layout: the non-mapping channels are definitional. -/
theorem mappingCoherentAllKeys_of_globals (fields : List Field) (s : ContractState)
    (hrange : MappingBasesInRange fields)
    (h1 : MappingCoherent s) (h2 : MappingCoherentUint s) (h3 : MappingCoherentMap2 s) :
    MappingCoherentAllKeys fields s := by
  intro k ch n h
  cases k with
  | slot m =>
      obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m =>
      obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m =>
      obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m =>
      obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key =>
      obtain ⟨hk, rfl, rfl⟩ := storageKeySlot_map_eq h
      exact h1 m key (hrange m (by rw [hk]; rfl))
  | mapUint m key =>
      obtain ⟨hk, rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      exact h2 m key (hrange m (by rw [hk]; rfl))
  | map2 m k1 k2 =>
      obtain ⟨hk, rfl, rfl⟩ := storageKeySlot_map2_eq h
      exact h3 m k1 k2 (hrange m (by rw [hk]; rfl))

/-- Instantiation at a declared address-keyed mapping. -/
theorem mappingCoherentAllKeys_map {fields : List Field} {s : ContractState} {m : Nat}
    (h : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields m = some (.simple .address)) (key : Address) :
    s.storageMap m key = s.storage (solidityMappingSlot m (addressToWord key).val) :=
  h (.map m key) _ _ (storageKeySlot_map_of_kind key hkind)

theorem mappingCoherentAllKeys_mapUint {fields : List Field} {s : ContractState} {m : Nat}
    (h : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields m = some (.simple .uint256)) (key : Uint256) :
    s.storageMapUint m key = s.storage (solidityMappingSlot m key.val) :=
  h (.mapUint m key) _ _ (storageKeySlot_mapUint_of_kind key hkind)

theorem mappingCoherentAllKeys_map2 {fields : List Field} {s : ContractState} {m : Nat}
    (h : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields m = some (.nested .address .address)) (k1 k2 : Address) :
    s.storageMap2 m k1 k2 =
      s.storage (abstractNestedMappingSlot m (addressToWord k1).val (addressToWord k2).val) :=
  h (.map2 m k1 k2) _ _ (storageKeySlot_map2_of_kind k1 k2 hkind)

theorem defaultState_mappingCoherentAllKeys (fields : List Field) :
    MappingCoherentAllKeys fields defaultState := by
  intro _ ch _ _
  cases ch <;> rfl

/-! ### Off-key write laws at the `storageWords` level

`Verity.Core` already proves these through the `storage`/`storageMap*` lenses.
The all-keys invariant is phrased directly on `storageWords`, so the same facts
are restated here in `storageWords` form; that keeps the preservation proofs on
`simp only` and away from key-normalisation. -/

theorem channelRead_persistent (s : ContractState) (n : Nat) :
    channelRead s .persistent n = s.storageWords (.slot n) := rfl

theorem writeSlot_slot_of_ne (s : ContractState) (w : Nat) (v : Uint256) {n : Nat}
    (h : n ≠ w) : (s.writeSlot w v).storageWords (.slot n) = s.storageWords (.slot n) := by
  simp [writeSlot, h]

theorem writeSlot_map (s : ContractState) (w : Nat) (v : Uint256) (m : Nat) (key : Address) :
    (s.writeSlot w v).storageWords (.map m key) = s.storageWords (.map m key) := by
  simp [writeSlot]

theorem writeSlot_mapUint (s : ContractState) (w : Nat) (v : Uint256) (m : Nat) (key : Uint256) :
    (s.writeSlot w v).storageWords (.mapUint m key) = s.storageWords (.mapUint m key) := by
  simp [writeSlot]

theorem writeSlot_map2 (s : ContractState) (w : Nat) (v : Uint256) (m : Nat) (k1 k2 : Address) :
    (s.writeSlot w v).storageWords (.map2 m k1 k2) = s.storageWords (.map2 m k1 k2) := by
  simp [writeSlot]

theorem writeMap_slot (s : ContractState) (w : Nat) (key : Address) (v : Uint256) (n : Nat) :
    (s.writeMap w key v).storageWords (.slot n) = s.storageWords (.slot n) := by
  simp [writeMap]

theorem writeMap_mapUint (s : ContractState) (w : Nat) (key : Address) (v : Uint256)
    (m : Nat) (key' : Uint256) :
    (s.writeMap w key v).storageWords (.mapUint m key') = s.storageWords (.mapUint m key') := by
  simp [writeMap]

theorem writeMap_map2 (s : ContractState) (w : Nat) (key : Address) (v : Uint256)
    (m : Nat) (k1 k2 : Address) :
    (s.writeMap w key v).storageWords (.map2 m k1 k2) = s.storageWords (.map2 m k1 k2) := by
  simp [writeMap]

theorem writeMapUint_slot (s : ContractState) (w : Nat) (key v : Uint256) (n : Nat) :
    (s.writeMapUint w key v).storageWords (.slot n) = s.storageWords (.slot n) := by
  simp [writeMapUint]

theorem writeMapUint_map (s : ContractState) (w : Nat) (key v : Uint256)
    (m : Nat) (key' : Address) :
    (s.writeMapUint w key v).storageWords (.map m key') = s.storageWords (.map m key') := by
  simp [writeMapUint]

theorem writeMapUint_map2 (s : ContractState) (w : Nat) (key v : Uint256)
    (m : Nat) (k1 k2 : Address) :
    (s.writeMapUint w key v).storageWords (.map2 m k1 k2) = s.storageWords (.map2 m k1 k2) := by
  simp [writeMapUint]

theorem writeMap2_slot (s : ContractState) (w : Nat) (k1 k2 : Address) (v : Uint256) (n : Nat) :
    (s.writeMap2 w k1 k2 v).storageWords (.slot n) = s.storageWords (.slot n) := by
  simp [writeMap2]

theorem writeMap2_map (s : ContractState) (w : Nat) (k1 k2 : Address) (v : Uint256)
    (m : Nat) (key' : Address) :
    (s.writeMap2 w k1 k2 v).storageWords (.map m key') = s.storageWords (.map m key') := by
  simp [writeMap2]

theorem writeMap2_mapUint (s : ContractState) (w : Nat) (k1 k2 : Address) (v : Uint256)
    (m : Nat) (key' : Uint256) :
    (s.writeMap2 w k1 k2 v).storageWords (.mapUint m key') = s.storageWords (.mapUint m key') := by
  simp [writeMap2]

/-! ### Cross-channel slot separation

Hash separation requires an explicit certificate over the accessed ABI pairs.
Distinct declared base slots alone do not establish distinct derived slots. -/

theorem nested_ne_simple {fields : List Field} {m b : Nat} {a k2 c : Nat}
    (hbases : MappingBasesNotDerived fields)
    (hkind : (fieldMapKindAt fields b).isSome = true)
    {accessedPairs : List (Nat × Nat)} (cert : CollisionFreeOn accessedPairs)
    (hp : (solidityMappingSlot m a, k2) ∈ accessedPairs)
    (hq : (b, c) ∈ accessedPairs) :
    abstractNestedMappingSlot m a k2 ≠ solidityMappingSlot b c := by
  intro heq
  simp only [abstractNestedMappingSlot, abstractMappingSlot] at heq
  exact (hbases b hkind m a)
    (mappingSlot_pair_eq_of_collisionFreeOn cert hp hq heq).1

theorem simple_ne_of_base_ne {m b : Nat} {a c : Nat}
    {accessedPairs : List (Nat × Nat)} (cert : CollisionFreeOn accessedPairs)
    (hp : (m, a) ∈ accessedPairs) (hq : (b, c) ∈ accessedPairs)
    (hb : m ≠ b) :
    solidityMappingSlot m a ≠ solidityMappingSlot b c := fun heq =>
   hb (mappingSlot_pair_eq_of_collisionFreeOn cert hp hq heq).1

/-! ### Preservation by the in-tree write helpers -/

/-- The diagonal case of aligned `writeMap`: another address-keyed entry, which
    is either the written pair itself or separated from it by key/base
    disequality. -/
theorem writeMap_aligned_map_case (fields : List Field) (s : ContractState)
    (slot : Nat) (key : Address) (v : Uint256) (m : Nat) (key' : Address)
    (hkind' : fieldMapKindAt fields m = some (.simple .address))
    (hna : StorageKey.map m key' ≠ StorageKey.map slot key →
      solidityMappingSlot m (addressToWord key').val ≠
        solidityMappingSlot slot (addressToWord key).val)
    (hcoh : MappingCoherentAllKeys fields s) :
    ((s.writeMap slot key v).writeSlot
      (solidityMappingSlot slot (addressToWord key).val) v).storageMap m key' =
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storage
        (solidityMappingSlot m (addressToWord key').val) := by
  by_cases hm : m = slot
  · subst hm
    by_cases hk : key' = key
    · subst hk
      exact writeMap_aligned_same s m key' v
    · have hne : StorageKey.map m key' ≠ StorageKey.map m key := by
        intro heq; injection heq with _ hk'; exact hk hk'
      exact writeMap_aligned_other s m key v m key'
        (mappingCoherentAllKeys_map hcoh hkind' key') hne
        (hna hne)
  · have hne : StorageKey.map m key' ≠ StorageKey.map slot key := by
      intro heq; injection heq with hm' _; exact hm hm'
    exact writeMap_aligned_other s slot key v m key'
      (mappingCoherentAllKeys_map hcoh hkind' key') hne
      (hna hne)

/-- The diagonal case of aligned `writeMapUint`. -/
theorem writeMapUint_aligned_mapUint_case (fields : List Field) (s : ContractState)
    (slot : Nat) (key v : Uint256) (m : Nat) (key' : Uint256)
    (hkind' : fieldMapKindAt fields m = some (.simple .uint256))
    (hna : StorageKey.mapUint m key' ≠ StorageKey.mapUint slot key →
      solidityMappingSlot m key'.val ≠ solidityMappingSlot slot key.val)
    (hcoh : MappingCoherentAllKeys fields s) :
    ((s.writeMapUint slot key v).writeSlot
      (solidityMappingSlot slot key.val) v).storageMapUint m key' =
      ((s.writeMapUint slot key v).writeSlot
        (solidityMappingSlot slot key.val) v).storage
        (solidityMappingSlot m key'.val) := by
  by_cases hm : m = slot
  · subst hm
    by_cases hk : key' = key
    · subst hk
      exact writeMapUint_aligned_same s m key' v
    · have hne : StorageKey.mapUint m key' ≠ StorageKey.mapUint m key := by
        intro heq; injection heq with _ hk'; exact hk hk'
      exact writeMapUint_aligned_other s m key v m key'
        (mappingCoherentAllKeys_mapUint hcoh hkind' key') hne
        (hna hne)
  · have hne : StorageKey.mapUint m key' ≠ StorageKey.mapUint slot key := by
      intro heq; injection heq with hm' _; exact hm hm'
    exact writeMapUint_aligned_other s slot key v m key'
      (mappingCoherentAllKeys_mapUint hcoh hkind' key') hne
      (hna hne)

/-- The diagonal case of aligned `writeMap2`. -/
theorem writeMap2_aligned_map2_case (fields : List Field) (s : ContractState)
    (slot : Nat) (k1 k2 : Address) (v : Uint256) (m : Nat) (j1 j2 : Address)
    (hkind' : fieldMapKindAt fields m = some (.nested .address .address))
    (hna : StorageKey.map2 m j1 j2 ≠ StorageKey.map2 slot k1 k2 →
      abstractNestedMappingSlot m (addressToWord j1).val (addressToWord j2).val ≠
        abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
    (hcoh : MappingCoherentAllKeys fields s) :
    ((s.writeMap2 slot k1 k2 v).writeSlot
      (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
      v).storageMap2 m j1 j2 =
      ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
        v).storage
        (abstractNestedMappingSlot m (addressToWord j1).val (addressToWord j2).val) := by
  by_cases hm : m = slot
  · subst hm
    by_cases h1 : j1 = k1
    · by_cases h2 : j2 = k2
      · subst h1; subst h2
        exact writeMap2_aligned_same s m j1 j2 v
      · have hne : StorageKey.map2 m j1 j2 ≠ StorageKey.map2 m k1 k2 := by
          intro heq; injection heq with _ _ hj2; exact h2 hj2
        exact writeMap2_aligned_other s m k1 k2 v m j1 j2
          (mappingCoherentAllKeys_map2 hcoh hkind' j1 j2) hne
          (hna hne)
    · have hne : StorageKey.map2 m j1 j2 ≠ StorageKey.map2 m k1 k2 := by
        intro heq; injection heq with _ hj1 _; exact h1 hj1
      exact writeMap2_aligned_other s m k1 k2 v m j1 j2
        (mappingCoherentAllKeys_map2 hcoh hkind' j1 j2) hne
        (hna hne)
  · have hne : StorageKey.map2 m j1 j2 ≠ StorageKey.map2 slot k1 k2 := by
      intro heq; injection heq with hm' _ _; exact hm hm'
    exact writeMap2_aligned_other s slot k1 k2 v m j1 j2
      (mappingCoherentAllKeys_map2 hcoh hkind' j1 j2) hne
      (hna hne)

/-- An aligned address-map write preserves the certified finite footprint. -/
theorem writeMap_aligned_preserves_mappingCoherentOnKeys
    (fields : List Field) (s : ContractState) (slot : Nat) (key : Address) (v : Uint256)
    (hkind : fieldMapKindAt fields slot = some (.simple .address))
    (accessed : List StorageKey) (hna : LayoutNonAliasOn fields accessed)
    (hw : StorageKey.map slot key ∈ accessed)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentOnKeys fields accessed
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v) := by
  have hwrite := storageKeySlot_map_of_kind key hkind
  intro k hk ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      exact writeMap_aligned_map_case fields s slot key v m key' hkind'
        (hna _ hk _ hw _ _ _ (storageKeySlot_map_of_kind key' hkind') hwrite) hcoh
  | mapUint m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      have hslot : solidityMappingSlot m key'.val ≠
          solidityMappingSlot slot (addressToWord key).val :=
        hna _ hk _ hw _ _ _ (storageKeySlot_mapUint_of_kind key' hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_mapUint hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_mapUint, writeMap_mapUint,
        writeSlot_slot_of_ne _ _ _ hslot, writeMap_slot]
      exact hcoh'
  | map2 m k1 k2 =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      have hslot :
          abstractNestedMappingSlot m (addressToWord k1).val (addressToWord k2).val ≠
            solidityMappingSlot slot (addressToWord key).val :=
         hna _ hk _ hw _ _ _ (storageKeySlot_map2_of_kind k1 k2 hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_map2 hcoh hkind' k1 k2
      simp only [channelRead_persistent, writeSlot_map2, writeMap_map2,
        writeSlot_slot_of_ne _ _ _ hslot, writeMap_slot]
      exact hcoh'

theorem writeMapUint_aligned_preserves_mappingCoherentOnKeys
    (fields : List Field) (s : ContractState) (slot : Nat) (key v : Uint256)
    (hkind : fieldMapKindAt fields slot = some (.simple .uint256))
    (accessed : List StorageKey) (hna : LayoutNonAliasOn fields accessed)
    (hw : StorageKey.mapUint slot key ∈ accessed)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentOnKeys fields accessed
      ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v) := by
  have hwrite := storageKeySlot_mapUint_of_kind key hkind
  intro k hk ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      have hslot : solidityMappingSlot m (addressToWord key').val ≠
          solidityMappingSlot slot key.val :=
        hna _ hk _ hw _ _ _ (storageKeySlot_map_of_kind key' hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_map hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_map, writeMapUint_map,
        writeSlot_slot_of_ne _ _ _ hslot, writeMapUint_slot]
      exact hcoh'
  | mapUint m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      exact writeMapUint_aligned_mapUint_case fields s slot key v m key' hkind'
        (hna _ hk _ hw _ _ _ (storageKeySlot_mapUint_of_kind key' hkind') hwrite) hcoh
  | map2 m k1 k2 =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      have hslot :
          abstractNestedMappingSlot m (addressToWord k1).val (addressToWord k2).val ≠
            solidityMappingSlot slot key.val :=
        hna _ hk _ hw _ _ _ (storageKeySlot_map2_of_kind k1 k2 hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_map2 hcoh hkind' k1 k2
      simp only [channelRead_persistent, writeSlot_map2, writeMapUint_map2,
        writeSlot_slot_of_ne _ _ _ hslot, writeMapUint_slot]
      exact hcoh'

theorem writeMap2_aligned_preserves_mappingCoherentOnKeys
    (fields : List Field) (s : ContractState) (slot : Nat) (k1 k2 : Address) (v : Uint256)
    (hkind : fieldMapKindAt fields slot = some (.nested .address .address))
    (accessed : List StorageKey) (hna : LayoutNonAliasOn fields accessed)
    (hw : StorageKey.map2 slot k1 k2 ∈ accessed)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentOnKeys fields accessed
      ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) v) := by
  have hwrite := storageKeySlot_map2_of_kind k1 k2 hkind
  intro k hk ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      have hslot : solidityMappingSlot m (addressToWord key').val ≠
           abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val :=
        hna _ hk _ hw _ _ _ (storageKeySlot_map_of_kind key' hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_map hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_map, writeMap2_map,
        writeSlot_slot_of_ne _ _ _ hslot, writeMap2_slot]
      exact hcoh'
  | mapUint m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      have hslot : solidityMappingSlot m key'.val ≠
           abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val :=
        hna _ hk _ hw _ _ _ (storageKeySlot_mapUint_of_kind key' hkind') hwrite (by simp)
      have hcoh' := mappingCoherentAllKeys_mapUint hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_mapUint, writeMap2_mapUint,
        writeSlot_slot_of_ne _ _ _ hslot, writeMap2_slot]
      exact hcoh'
  | map2 m j1 j2 =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      exact writeMap2_aligned_map2_case fields s slot k1 k2 v m j1 j2 hkind'
        (hna _ hk _ hw _ _ _ (storageKeySlot_map2_of_kind j1 j2 hkind') hwrite) hcoh

/-- A lone flat `writeSlot` keeps the global invariant when the written word is
    not the image of any layout-derived mapping entry. Same image-avoidance
    shape as `writeSlot_preserves_mappingCoherent`. -/
theorem writeSlot_preserves_mappingCoherentAllKeys
    (fields : List Field) (s : ContractState) (w : Nat) (v : Uint256)
    (havoid : DerivedMappingSlotsAvoid fields w)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentAllKeys fields (s.writeSlot w v) := by
  intro k ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      have hne := havoid _ _ _ h rfl
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      have hcoh' := mappingCoherentAllKeys_map hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_map, writeSlot_slot_of_ne _ _ _ hne]
      exact hcoh'
  | mapUint m key' =>
      have hne := havoid _ _ _ h rfl
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      have hcoh' := mappingCoherentAllKeys_mapUint hcoh hkind' key'
      simp only [channelRead_persistent, writeSlot_mapUint, writeSlot_slot_of_ne _ _ _ hne]
      exact hcoh'
  | map2 m j1 j2 =>
      have hne := havoid _ _ _ h rfl
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      have hcoh' := mappingCoherentAllKeys_map2 hcoh hkind' j1 j2
      simp only [channelRead_persistent, writeSlot_map2, writeSlot_slot_of_ne _ _ _ hne]
      exact hcoh'

/-- `writeAddrSlot` never writes a `StorageKey.slot`, so it discharges the
    image-avoidance side condition outright. -/
theorem writeAddrSlot_preserves_mappingCoherentAllKeys
    (fields : List Field) (s : ContractState) (w : Nat) (a : Address)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentAllKeys fields (s.writeAddrSlot w a) := by
  intro k ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      simpa [channelRead, storageMap, storage, writeAddrSlot] using
        mappingCoherentAllKeys_map hcoh hkind' key'
  | mapUint m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      simpa [channelRead, storageMapUint, storage, writeAddrSlot] using
        mappingCoherentAllKeys_mapUint hcoh hkind' key'
  | map2 m j1 j2 =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      simpa [channelRead, storageMap2, storage, writeAddrSlot] using
        mappingCoherentAllKeys_map2 hcoh hkind' j1 j2

/-- Transient writes land on a different `StorageKey` constructor. -/
theorem writeTransient_preserves_mappingCoherentAllKeys
    (fields : List Field) (s : ContractState) (w : Nat) (v : Uint256)
    (hcoh : MappingCoherentAllKeys fields s) :
    MappingCoherentAllKeys fields (s.writeTransient w v) := by
  intro k ch n h
  cases k with
  | slot m => obtain ⟨rfl, rfl⟩ := storageKeySlot_slot_eq h; rfl
  | addr m => obtain ⟨rfl, rfl⟩ := storageKeySlot_addr_eq h; rfl
  | transient m => obtain ⟨rfl, rfl⟩ := storageKeySlot_transient_eq h; rfl
  | contractSlot c m => obtain ⟨rfl, rfl⟩ := storageKeySlot_contractSlot_eq h; rfl
  | «scoped» _ _ => simp [storageKeySlot] at h
  | mapChain _ _ _ => simp [storageKeySlot] at h
  | transientMapChain _ _ => simp [storageKeySlot] at h
  | map m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map_eq h
      simpa [channelRead, storageMap, storage, writeTransient] using
        mappingCoherentAllKeys_map hcoh hkind' key'
  | mapUint m key' =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_mapUint_eq h
      simpa [channelRead, storageMapUint, storage, writeTransient] using
        mappingCoherentAllKeys_mapUint hcoh hkind' key'
  | map2 m j1 j2 =>
      obtain ⟨hkind', rfl, rfl⟩ := storageKeySlot_map2_eq h
      simpa [channelRead, storageMap2, storage, writeTransient] using
        mappingCoherentAllKeys_map2 hcoh hkind' j1 j2

/-! ### End-to-end read bridge

Lens read = flat `encodeStorageAt` read at the derived slot, under the global
all-keys invariant. The two non-occupation side conditions say the derived
keccak slot is not also a declared field slot and not a dynamic-array element
slot; they are the same hypotheses `FieldEncode` already uses. -/

/-- **Lens read = flat read.** `readMap` at a declared `mapping(address => uint256)`
    is exactly what `encodeStorageAt` returns at the derived Solidity slot. -/
theorem readMap_eq_encodeStorageAt_of_coherent
    {fields : List Field} {s : ContractState} {slot : Nat} {key : Address}
    (hcoh : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields slot = some (.simple .address))
    (hresolved :
      findResolvedFieldAtSlot fields
        (solidityMappingSlot slot (addressToWord key).val) = none)
    (hdyn :
      findDynamicArrayElementAtSlot fields s
        (solidityMappingSlot slot (addressToWord key).val) = none) :
    (s.readMap slot key).val =
      encodeStorageAt fields s (solidityMappingSlot slot (addressToWord key).val) := by
  rw [encodeStorageAt_of_unresolved hresolved hdyn]
  exact congrArg Core.Uint256.val (mappingCoherentAllKeys_map hcoh hkind key)

theorem readMapUint_eq_encodeStorageAt_of_coherent
    {fields : List Field} {s : ContractState} {slot : Nat} {key : Uint256}
    (hcoh : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields slot = some (.simple .uint256))
    (hresolved :
      findResolvedFieldAtSlot fields (solidityMappingSlot slot key.val) = none)
    (hdyn :
      findDynamicArrayElementAtSlot fields s (solidityMappingSlot slot key.val) = none) :
    (s.readMapUint slot key).val =
      encodeStorageAt fields s (solidityMappingSlot slot key.val) := by
  rw [encodeStorageAt_of_unresolved hresolved hdyn]
  exact congrArg Core.Uint256.val (mappingCoherentAllKeys_mapUint hcoh hkind key)

theorem readMap2_eq_encodeStorageAt_of_coherent
    {fields : List Field} {s : ContractState} {slot : Nat} {k1 k2 : Address}
    (hcoh : MappingCoherentAllKeys fields s)
    (hkind : fieldMapKindAt fields slot = some (.nested .address .address))
    (hresolved :
      findResolvedFieldAtSlot fields
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) =
        none)
    (hdyn :
      findDynamicArrayElementAtSlot fields s
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) =
        none) :
    (s.readMap2 slot k1 k2).val =
      encodeStorageAt fields s
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) := by
  rw [encodeStorageAt_of_unresolved hresolved hdyn]
  exact congrArg Core.Uint256.val (mappingCoherentAllKeys_map2 hcoh hkind k1 k2)

/-! ### Dynamic-array root vs. element slot coherence

Dynamic-array element slots are aligned across `Denote`, `SourceSemantics`,
`ObsAlgebra`, and `StructArrayStorage`:

* `Denote.arrayBaseSlot` / `SourceSemantics.arrayBaseSlot` and
  `SourceSemantics.findDynamicArrayElementAtSlot` (`SourceSemantics.lean`)
  place element `i` of the array rooted at slot `s` at
  `(keccak256(bytes32(s)) + i) % 2^256`.
* `StructArrayStorage.lean` (`sourceArrayBaseSlot_eq_solidityArrayBaseSlot`,
  `sourceArrayElementSlot_eq_solidityArrayElemSlot`,
  `slotPointer_sourceArrayElementSlot_eq_storageArrayElementPointer`) proves
  this coincides with `ObsAlgebra.solidityArrayElemSlot s i 1` and
  `storageArrayElementPointer s i`.

Containment at the array root: `storageKeySlot` returns `none` at a persistent
root whose resolved field is a `dynamicArray`, so `MappingCoherentAllKeys`
claims nothing about dynamic-array roots (`encodeStorageAt` reads the list
length there, whereas element words occupy ordinary persistent slots). -/

theorem storageKeySlot_slot_dynamicArray {fields : List Field} {n : Nat} {f : Field}
    (hf : findResolvedFieldAtSlot fields n = some f)
    (hdyn : fieldUsesDynamicArrayStorage f = true) :
    storageKeySlot fields (.slot n) = none := by
  simp only [storageKeySlot, hf, hdyn, if_true]

end Compiler.Proofs.Storage.MappingCoherentGlobal
