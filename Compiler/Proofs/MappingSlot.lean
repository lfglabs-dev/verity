import EvmYul
import Mathlib.Data.List.Nodup
import Compiler.Constants
import Compiler.Proofs.KeccakBound
import Compiler.Proofs.IRGeneration.IRStorageWord

namespace Compiler.Proofs

open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

/-!
Mapping slot abstraction used by proof interpreters.

The active backend is keccak-faithful (`solidityMappingSlot`).

## Range axiom eliminated; slot collision-resistance is axiomatic

The mapping-slot definition now uses the kernel-computable `KeccakEngine.keccak256`
so that the output-length bound is structurally provable. The FFI version (`ffi.KEC`)
may optionally be registered via `@[implemented_by]` for runtime performance if
build-time benchmarks show a regression.
-/

/-- Mapping-slot backend chosen for proof semantics. -/
inductive MappingSlotBackend where
  | keccak
  deriving DecidableEq, Repr

/--
Active proof-model backend.

`keccak` is the active, EVM-faithful mapping-slot model.
-/
def activeMappingSlotBackend : MappingSlotBackend := .keccak

/-- Whether the active backend matches EVM keccak-derived slot layout exactly. -/
def activeMappingSlotBackendIsEvmFaithful : Bool := true

/-- ABI-encode `(key, baseSlot)` as two 32-byte words (Solidity mapping convention). -/
def abiEncodeMappingSlot (baseSlot key : Nat) : ByteArray :=
  let keyWord : EvmYul.UInt256 := .ofNat key
  let baseSlotWord : EvmYul.UInt256 := .ofNat baseSlot
  keyWord.toByteArray ++ baseSlotWord.toByteArray

/-- FFI-based mapping slot computation (fast, used at runtime via @[implemented_by]).
    Not used in proofs — proofs reason about `solidityMappingSlot` which uses the
    kernel-computable Keccak. -/
private def solidityMappingSlot_ffi (baseSlot key : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (ffi.KEC (abiEncodeMappingSlot baseSlot key))

/-- Solidity mapping storage slot derivation: `keccak256(abi.encode(key, baseSlot))`.

    Uses the kernel-computable Keccak engine so proofs can reason about the output
    size (always 32 bytes → result < 2^256). The FFI version is registered via
    `@[implemented_by]` for runtime performance. -/
@[implemented_by solidityMappingSlot_ffi]
def solidityMappingSlot (baseSlot key : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key))

/-- `EvmYul.UInt256.ofNat` reduces its argument modulo `2^256`. -/
theorem evmYul_uint256_ofNat_mod (n : Nat) :
    EvmYul.UInt256.ofNat (n % Compiler.Constants.evmModulus) = EvmYul.UInt256.ofNat n := by
  unfold EvmYul.UInt256.ofNat
  simp only [Id.run]
  congr 1
  apply Fin.ext
  simp [Fin.ofNat, EvmYul.UInt256.size]

/-- The ABI encoding only sees base slot and key modulo `2^256`. -/
theorem abiEncodeMappingSlot_mod (baseSlot key : Nat) :
    abiEncodeMappingSlot (baseSlot % Compiler.Constants.evmModulus)
        (key % Compiler.Constants.evmModulus) =
      abiEncodeMappingSlot baseSlot key := by
  simp only [abiEncodeMappingSlot, evmYul_uint256_ofNat_mod]

/-- The mapping-slot derivation only sees base slot and key modulo `2^256`.
    In particular `solidityMappingSlot b k = solidityMappingSlot b (k + 2^256)`,
    which is why `solidityMappingSlot_injective` must be range-restricted. -/
theorem solidityMappingSlot_mod (baseSlot key : Nat) :
    solidityMappingSlot (baseSlot % Compiler.Constants.evmModulus)
        (key % Compiler.Constants.evmModulus) =
      solidityMappingSlot baseSlot key := by
  unfold solidityMappingSlot
  rw [abiEncodeMappingSlot_mod]

/-- Collision-resistance of Solidity mapping-slot derivation
    `keccak256(abi.encode(key, baseSlot))` on in-range (`< 2^256`) base
    slots and keys, i.e. on the 64-byte ABI words actually hashed.

    **Not** injectivity of keccak256 on arbitrary `ByteArray`s (256-bit
    output, infinite domain). The range hypotheses are required: the ABI
    encoding reduces both arguments modulo `2^256` (`solidityMappingSlot_mod`),
    so an unrestricted statement over `Nat` is refutable
    (`solidityMappingSlot 0 0 = solidityMappingSlot 0 (2^256)`).
    See `docs/AXIOMS.md`. -/
axiom solidityMappingSlot_injective
    (base₁ key₁ base₂ key₂ : Nat) :
    base₁ < Compiler.Constants.evmModulus →
    key₁ < Compiler.Constants.evmModulus →
    base₂ < Compiler.Constants.evmModulus →
    key₂ < Compiler.Constants.evmModulus →
    solidityMappingSlot base₁ key₁ = solidityMappingSlot base₂ key₂ →
    base₁ = base₂ ∧ key₁ = key₂

/-- Unbounded consequence of `solidityMappingSlot_injective`: equal derived
    slots force equal base slots and keys modulo `2^256`. -/
theorem solidityMappingSlot_injective_mod (base₁ key₁ base₂ key₂ : Nat)
    (h : solidityMappingSlot base₁ key₁ = solidityMappingSlot base₂ key₂) :
    base₁ % Compiler.Constants.evmModulus = base₂ % Compiler.Constants.evmModulus ∧
      key₁ % Compiler.Constants.evmModulus = key₂ % Compiler.Constants.evmModulus := by
  have hpos : 0 < Compiler.Constants.evmModulus := by decide
  apply solidityMappingSlot_injective _ _ _ _
    (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
  rw [solidityMappingSlot_mod, solidityMappingSlot_mod]
  exact h

theorem solidityMappingSlot_ne {base₁ key₁ base₂ key₂ : Nat}
    (hb₁ : base₁ < Compiler.Constants.evmModulus)
    (hk₁ : key₁ < Compiler.Constants.evmModulus)
    (hb₂ : base₂ < Compiler.Constants.evmModulus)
    (hk₂ : key₂ < Compiler.Constants.evmModulus)
    (h : base₁ ≠ base₂ ∨ key₁ ≠ key₂) :
    solidityMappingSlot base₁ key₁ ≠ solidityMappingSlot base₂ key₂ := by
  intro heq
  rcases solidityMappingSlot_injective base₁ key₁ base₂ key₂ hb₁ hk₁ hb₂ hk₂ heq with ⟨hb, hk⟩
  cases h with
  | inl hbase => exact hbase hb
  | inr hkey => exact hkey hk

/-- Active proof-model mapping slot encoding backend. -/
def abstractMappingSlot (baseSlot key : Nat) : Nat := solidityMappingSlot baseSlot key

/-- Active proof-model mapping slot tag sentinel (backend-specific). -/
def abstractMappingTag : Nat := 0

/-- Active proof-model mapping slot decoder backend. -/
def abstractDecodeMappingSlot (_slot : Nat) : Option (Nat × Nat) := none

/-- Active proof-model nested mapping slot helper. -/
def abstractNestedMappingSlot (baseSlot key1 key2 : Nat) : Nat :=
  abstractMappingSlot (abstractMappingSlot baseSlot key1) key2

/-- Concrete storage location for a mapping value word.  Offsets are normalized
    to the EVM storage-key width, matching generated mapping-struct member
    accesses. -/
def mappingSlotLocation (baseSlot key wordOffset : Nat) : Nat :=
  (solidityMappingSlot baseSlot key + wordOffset) % Compiler.Constants.evmModulus

/-- Concrete storage location for a nested-mapping value word. -/
def nestedMappingSlotLocation (baseSlot key1 key2 wordOffset : Nat) : Nat :=
  (solidityMappingSlot (solidityMappingSlot baseSlot key1) key2 + wordOffset) %
    Compiler.Constants.evmModulus

/-- Finite list of mapping-derived locations touched by one generated proof port. -/
def mappingSlotLocations (baseSlot : Nat) (keysAndOffsets : List (Nat × Nat)) : List Nat :=
  keysAndOffsets.map fun keyAndOffset =>
    mappingSlotLocation baseSlot keyAndOffset.1 keyAndOffset.2

/-- Finite list of nested-mapping-derived locations touched by one generated proof port. -/
def nestedMappingSlotLocations
    (baseSlot : Nat) (keysAndOffsets : List (Nat × Nat × Nat)) : List Nat :=
  keysAndOffsets.map fun keyAndOffset =>
    nestedMappingSlotLocation baseSlot keyAndOffset.1 keyAndOffset.2.1 keyAndOffset.2.2

/-- Local non-alias proposition for two concrete storage slots. -/
abbrev StorageSlotNonAlias (a b : Nat) : Prop := a ≠ b

/-- Finite distinctness certificate for the concrete storage slots a proof port
    actually touches.  This is the restricted replacement surface for downstream
    global mapping-slot injectivity assumptions: generators may prove or emit one
    certificate per finite location set, and consumers derive only the pairwise
    facts they use. -/
abbrev StorageSlotsDistinct (slots : List Nat) : Prop := slots.Nodup

/-- Layout-certificate-backed non-alias evidence for one finite location set. -/
structure StorageSlotNonAliasCertificate (slots : List Nat) : Prop where
  distinct : StorageSlotsDistinct slots

/-- Derived mapping-table view from flat storage. -/
def storageAsMappings (storage : IRStorageSlot → IRStorageWord) : Nat → Nat → IRStorageWord :=
  fun baseSlot key => storage (IRStorageSlot.ofNat (solidityMappingSlot baseSlot key))

/-- Read a mapping entry directly from base slot and key. -/
def abstractLoadMappingEntry
    (storage : IRStorageSlot → IRStorageWord)
    (baseSlot key : Nat) : IRStorageWord :=
  storage (IRStorageSlot.ofNat (solidityMappingSlot baseSlot key))

/-- Write a mapping entry directly from base slot and key. -/
def abstractStoreMappingEntry
    (storage : IRStorageSlot → IRStorageWord)
    (baseSlot key value : Nat) : IRStorageSlot → IRStorageWord :=
  fun s => if s = IRStorageSlot.ofNat (solidityMappingSlot baseSlot key) then
    IRStorageWord.ofNat value
  else
    storage s

/-- Read through the active mapping-slot backend from flat storage. -/
def abstractLoadStorageOrMapping
    (storage : IRStorageSlot → IRStorageWord)
    (slot : Nat) : IRStorageWord :=
  storage (IRStorageSlot.ofNat slot)

/-- Write through the active mapping-slot backend to flat storage. -/
def abstractStoreStorageOrMapping
    (storage : IRStorageSlot → IRStorageWord)
    (slot value : Nat) : IRStorageSlot → IRStorageWord :=
  fun s => if s = IRStorageSlot.ofNat slot then IRStorageWord.ofNat value else storage s

@[simp] theorem abstractMappingSlot_eq_solidity (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key = solidityMappingSlot baseSlot key := rfl

@[simp] theorem abstractMappingTag_eq_zero :
    abstractMappingTag = 0 := rfl

@[simp] theorem abstractDecodeMappingSlot_eq_none (slot : Nat) :
    abstractDecodeMappingSlot slot = none := rfl

@[simp] theorem activeMappingSlotBackend_eq_keccak :
    activeMappingSlotBackend = .keccak := rfl

@[simp] theorem activeMappingSlotBackendIsEvmFaithful_eq_true :
    activeMappingSlotBackendIsEvmFaithful = true := rfl

@[simp] theorem abstractNestedMappingSlot_eq_solidityNested (baseSlot key1 key2 : Nat) :
    abstractNestedMappingSlot baseSlot key1 key2 =
      solidityMappingSlot (solidityMappingSlot baseSlot key1) key2 := by
  simp [abstractNestedMappingSlot]

theorem StorageSlotNonAliasCertificate.nonAlias_get
    {slots : List Nat} (cert : StorageSlotNonAliasCertificate slots)
    {i j : Nat} (hi : i < slots.length) (hj : j < slots.length)
    (hne : i ≠ j) :
    StorageSlotNonAlias slots[i] slots[j] := by
  intro hEq
  exact hne ((cert.distinct.getElem_inj_iff (i := i) (j := j) (hi := hi) (hj := hj)).mp hEq)

theorem StorageSlotNonAliasCertificate.of_distinct
    {slots : List Nat} (h : StorageSlotsDistinct slots) :
    StorageSlotNonAliasCertificate slots :=
  ⟨h⟩

theorem StorageSlotNonAliasCertificate.nonAlias_pair
    {a b : Nat} (cert : StorageSlotNonAliasCertificate [a, b]) :
    StorageSlotNonAlias a b := by
  simpa using
    (cert.nonAlias_get (i := 0) (j := 1) (hi := by simp) (hj := by simp)
      (hne := by decide))

theorem mappingSlotLocations_nonAlias_get
    {baseSlot : Nat} {keysAndOffsets : List (Nat × Nat)}
    (cert : StorageSlotNonAliasCertificate
      (mappingSlotLocations baseSlot keysAndOffsets))
    {i j : Nat}
    (hi : i < (mappingSlotLocations baseSlot keysAndOffsets).length)
    (hj : j < (mappingSlotLocations baseSlot keysAndOffsets).length)
    (hne : i ≠ j) :
    StorageSlotNonAlias
      (mappingSlotLocations baseSlot keysAndOffsets)[i]
      (mappingSlotLocations baseSlot keysAndOffsets)[j] :=
  cert.nonAlias_get hi hj hne

theorem nestedMappingSlotLocations_nonAlias_get
    {baseSlot : Nat} {keysAndOffsets : List (Nat × Nat × Nat)}
    (cert : StorageSlotNonAliasCertificate
      (nestedMappingSlotLocations baseSlot keysAndOffsets))
    {i j : Nat}
    (hi : i < (nestedMappingSlotLocations baseSlot keysAndOffsets).length)
    (hj : j < (nestedMappingSlotLocations baseSlot keysAndOffsets).length)
    (hne : i ≠ j) :
    StorageSlotNonAlias
      (nestedMappingSlotLocations baseSlot keysAndOffsets)[i]
      (nestedMappingSlotLocations baseSlot keysAndOffsets)[j] :=
  cert.nonAlias_get hi hj hne

@[simp] theorem abstractLoadMappingEntry_eq
    (storage : IRStorageSlot → IRStorageWord)
    (baseSlot key : Nat) :
    abstractLoadMappingEntry storage baseSlot key =
      storage (IRStorageSlot.ofNat (solidityMappingSlot baseSlot key)) := rfl

@[simp] theorem abstractStoreMappingEntry_eq
    (storage : IRStorageSlot → IRStorageWord)
    (baseSlot key value : Nat) :
    abstractStoreMappingEntry storage baseSlot key value =
      (fun s => if s = IRStorageSlot.ofNat (solidityMappingSlot baseSlot key) then
        IRStorageWord.ofNat value
      else
        storage s) := rfl

@[simp] theorem abstractLoadStorageOrMapping_eq
    (storage : IRStorageSlot → IRStorageWord)
    (slot : Nat) :
    abstractLoadStorageOrMapping storage slot = storage (IRStorageSlot.ofNat slot) := rfl

@[simp] theorem abstractStoreStorageOrMapping_eq
    (storage : IRStorageSlot → IRStorageWord)
    (slot value : Nat) :
    abstractStoreStorageOrMapping storage slot value =
      (fun s => if s = IRStorageSlot.ofNat slot then IRStorageWord.ofNat value else storage s) := rfl

/-- Keccak256 output interpreted as a big-endian 256-bit natural is less than 2^256.
    This is mathematically true because keccak produces exactly 32 bytes, so
    `fromByteArrayBigEndian` gives a value < 2^(8*32) = 2^256 = evmModulus.

    Previously an axiom — now a theorem thanks to the kernel-computable Keccak engine
    which exposes the output length to the proof system. -/
theorem solidityMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    solidityMappingSlot baseSlot key < Compiler.Constants.evmModulus := by
  unfold solidityMappingSlot
  exact fromByteArrayBigEndian_lt_of_size _ (by
    rw [KeccakEngine.keccak256_size])

@[simp] theorem mappingSlotLocation_zero (baseSlot key : Nat) :
    mappingSlotLocation baseSlot key 0 = solidityMappingSlot baseSlot key := by
  unfold mappingSlotLocation
  exact Nat.mod_eq_of_lt (solidityMappingSlot_lt_evmModulus baseSlot key)

theorem abstractMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key < Compiler.Constants.evmModulus :=
  solidityMappingSlot_lt_evmModulus baseSlot key

theorem abstractNestedMappingSlot_injective
    (base₁ key₁ key₂ base₂ key₁' key₂' : Nat)
    (hb₁ : base₁ < Compiler.Constants.evmModulus)
    (hk₁ : key₁ < Compiler.Constants.evmModulus)
    (hk₂ : key₂ < Compiler.Constants.evmModulus)
    (hb₂ : base₂ < Compiler.Constants.evmModulus)
    (hk₁' : key₁' < Compiler.Constants.evmModulus)
    (hk₂' : key₂' < Compiler.Constants.evmModulus)
    (h : abstractNestedMappingSlot base₁ key₁ key₂ =
      abstractNestedMappingSlot base₂ key₁' key₂') :
    base₁ = base₂ ∧ key₁ = key₁' ∧ key₂ = key₂' := by
  have hinj :=
    solidityMappingSlot_injective
      (solidityMappingSlot base₁ key₁) key₂
      (solidityMappingSlot base₂ key₁') key₂'
      (solidityMappingSlot_lt_evmModulus _ _) hk₂
      (solidityMappingSlot_lt_evmModulus _ _) hk₂' (by
        simpa [abstractNestedMappingSlot, abstractMappingSlot] using h)
  rcases hinj with ⟨hinner, hkey2⟩
  rcases solidityMappingSlot_injective base₁ key₁ base₂ key₁' hb₁ hk₁ hb₂ hk₁' hinner
    with ⟨hbase, hkey1⟩
  exact ⟨hbase, hkey1, hkey2⟩

theorem abstractNestedMappingSlot_ne
    {base₁ key₁ key₂ base₂ key₁' key₂' : Nat}
    (hb₁ : base₁ < Compiler.Constants.evmModulus)
    (hk₁ : key₁ < Compiler.Constants.evmModulus)
    (hk₂ : key₂ < Compiler.Constants.evmModulus)
    (hb₂ : base₂ < Compiler.Constants.evmModulus)
    (hk₁' : key₁' < Compiler.Constants.evmModulus)
    (hk₂' : key₂' < Compiler.Constants.evmModulus)
    (h : base₁ ≠ base₂ ∨ key₁ ≠ key₁' ∨ key₂ ≠ key₂') :
    abstractNestedMappingSlot base₁ key₁ key₂ ≠
      abstractNestedMappingSlot base₂ key₁' key₂' := by
  intro heq
  rcases abstractNestedMappingSlot_injective base₁ key₁ key₂ base₂ key₁' key₂'
      hb₁ hk₁ hk₂ hb₂ hk₁' hk₂' heq
    with ⟨hb, hk1, hk2⟩
  rcases h with h | h | h
  · exact h hb
  · exact h hk1
  · exact h hk2

theorem solidityMappingSlot_add_lt_evmModulus (baseSlot key wordOffset : Nat)
    (h : wordOffset < Compiler.Constants.evmModulus - solidityMappingSlot baseSlot key) :
    solidityMappingSlot baseSlot key + wordOffset < Compiler.Constants.evmModulus := by
  omega

/-- The sum of a mapping slot and a word offset fits in 256 bits.
    This holds because keccak256 output < 2^256 and word offsets are
    bounded explicitly by the available headroom under `2^256`. -/
theorem solidityMappingSlot_add_wordOffset_lt_evmModulus
    (baseSlot key wordOffset : Nat)
    (h : wordOffset < Compiler.Constants.evmModulus - solidityMappingSlot baseSlot key) :
    solidityMappingSlot baseSlot key + wordOffset < Compiler.Constants.evmModulus := by
  exact solidityMappingSlot_add_lt_evmModulus baseSlot key wordOffset h

/-! ### Hashed mapping-chain layout (interpretation of `StorageKey.mapChain`)

The executable plane keeps nested / struct mapping words under the symbolic
key `Verity.StorageKey.mapChain baseSlot keys wordOffset`. Their Solidity
storage location folds `keccak256(key ‖ acc)` left-to-right over the key path
and adds the word offset modulo `2^256`. None of the facts below use
`solidityMappingSlot_injective`. -/

/-- Solidity storage location of word `wordOffset` of the value stored under
    the key path `keys` of the mapping rooted at `baseSlot`. -/
def mappingChainSlotLocation (baseSlot : Nat) (keys : List Nat) (wordOffset : Nat) : Nat :=
  (keys.foldl solidityMappingSlot baseSlot + wordOffset) % Compiler.Constants.evmModulus

theorem mappingChainSlotLocation_single (baseSlot key wordOffset : Nat) :
    mappingChainSlotLocation baseSlot [key] wordOffset =
      mappingSlotLocation baseSlot key wordOffset := rfl

theorem mappingChainSlotLocation_pair (baseSlot key1 key2 wordOffset : Nat) :
    mappingChainSlotLocation baseSlot [key1, key2] wordOffset =
      nestedMappingSlotLocation baseSlot key1 key2 wordOffset := rfl

theorem foldl_solidityMappingSlot_lt_evmModulus (acc : Nat) (keys : List Nat)
    (h : acc < Compiler.Constants.evmModulus) :
    keys.foldl solidityMappingSlot acc < Compiler.Constants.evmModulus := by
  induction keys generalizing acc with
  | nil => exact h
  | cons key keys ih => exact ih _ (solidityMappingSlot_lt_evmModulus acc key)

/-- A non-empty key path at word offset `0` is exactly the folded keccak slot. -/
theorem mappingChainSlotLocation_zero (baseSlot key : Nat) (keys : List Nat) :
    mappingChainSlotLocation baseSlot (key :: keys) 0 =
      (key :: keys).foldl solidityMappingSlot baseSlot := by
  unfold mappingChainSlotLocation
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt
    (foldl_solidityMappingSlot_lt_evmModulus _ keys (solidityMappingSlot_lt_evmModulus _ _))

end Compiler.Proofs
