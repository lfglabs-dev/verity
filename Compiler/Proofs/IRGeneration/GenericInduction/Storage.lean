import Compiler.Proofs.IRGeneration.GenericInduction.ExprStmt

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

private theorem encodeStorageAt_writeUintSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ SourceSemantics.wordNormalize slot) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world [slot] value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · have hneq' : query ≠ slot % Compiler.Constants.evmModulus := by
      simpa [SourceSemantics.wordNormalize] using hneq
    simp [SourceSemantics.writeUintSlots, SourceSemantics.wordNormalize, hneq']
  · simp [SourceSemantics.writeUintSlots]
  · simp [SourceSemantics.writeUintSlots]

private theorem encodeStorageAt_writeUintSlots_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slots : List Nat}
    {query value : Nat}
    (hnotMem : query ∉ slots.map SourceSemantics.wordNormalize) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world slots value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp only [SourceSemantics.writeUintSlots]
    rw [show (slots.map SourceSemantics.wordNormalize).contains query = false from by
      simpa using hnotMem]
    simp
  · simp [SourceSemantics.writeUintSlots]
  · simp [SourceSemantics.writeUintSlots]

set_option maxHeartbeats 800000 in
private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key query value : Nat}
    (hquery : query < Compiler.Constants.evmModulus)
    (hneq : query ≠ SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key)) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp only [SourceSemantics.writeUintKeyedMappingSlots, List.foldl_cons, List.foldl_nil]
    have hneq' :
        query ≠ Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus := by
      simpa [SourceSemantics.wordNormalize, Compiler.Proofs.abstractMappingSlot_eq_solidity] using hneq
    have hslotNe :
        IRStorageSlot.ofNat query ≠
          IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot slot key) := by
      intro h
      apply hneq'
      have hnat := congrArg IRStorageSlot.toNat h
      simpa [IRStorageSlot.toNat_ofNat, SourceSemantics.wordNormalize,
        Compiler.Constants.evmModulus, EvmYul.UInt256.size, Nat.mod_eq_of_lt hquery] using hnat
    have hqueryMod : query % Verity.Core.UINT256_MODULUS = query := by
      simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using
        Nat.mod_eq_of_lt hquery
    simp [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot,
      hneq', hslotNe, hqueryMod, SourceSemantics.wordNormalize]
    apply Verity.Core.Uint256.ext
    simp [Verity.Core.Uint256.modulus, Nat.mod_eq_of_lt (world.storage query).isLt]
  · simp [SourceSemantics.writeUintKeyedMappingSlots]
  · simp [SourceSemantics.writeUintKeyedMappingSlots]

private theorem encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {keys : List Nat}
    {query value : Nat}
    (hneq : query ≠ SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys)) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · have hneq' :
        query ≠ SourceSemantics.mappingSlotChain slot keys % Compiler.Constants.evmModulus := by
      simpa [SourceSemantics.wordNormalize] using hneq
    simp [SourceSemantics.writeAddressKeyedMappingChainSlots,
      SourceSemantics.wordNormalize, hneq']
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots]

def mappingWordTargetSlot (slot key wordOffset : Nat) : Nat :=
  SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)

def mapping2WordTargetSlot (slot key1 key2 wordOffset : Nat) : Nat :=
  SourceSemantics.wordNormalize
    (Compiler.Proofs.abstractMappingSlot
      (Compiler.Proofs.abstractMappingSlot slot key1)
      key2 + wordOffset)

private theorem IRStorageSlot.toNat_ofNat_wordNormalize (slot : Nat) :
    (IRStorageSlot.ofNat slot).toNat = SourceSemantics.wordNormalize slot := by
  rfl

private theorem IRStorageSlot.toNat_ofNat_wordNormalize_arg (slot : Nat) :
    (IRStorageSlot.ofNat (SourceSemantics.wordNormalize slot)).toNat =
      SourceSemantics.wordNormalize slot := by
  simp [IRStorageSlot.toNat_ofNat_wordNormalize, SourceSemantics.wordNormalize,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

private theorem IRStorageSlot.ofNat_wordNormalize (slot : Nat) :
    IRStorageSlot.ofNat (SourceSemantics.wordNormalize slot) = IRStorageSlot.ofNat slot := by
  apply IRStorageSlot.eq_of_toNat_eq
  simp [IRStorageSlot.toNat_ofNat_wordNormalize, SourceSemantics.wordNormalize,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

private theorem SourceSemantics.wordNormalize_lt_evmModulus (slot : Nat) :
    SourceSemantics.wordNormalize slot < Compiler.Constants.evmModulus := by
  unfold SourceSemantics.wordNormalize
  exact Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS])

private theorem IRStorageSlot.toNat_ofNat_of_lt {slot : Nat}
    (hslot : slot < Compiler.Constants.evmModulus) :
    (IRStorageSlot.ofNat slot).toNat = slot := by
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize, SourceSemantics.wordNormalize,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using
    Nat.mod_eq_of_lt hslot

private theorem IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat
    {query : IRStorageSlot} {slot : Nat}
    (hneq : query ≠ IRStorageSlot.ofNat slot) :
    query.toNat ≠ SourceSemantics.wordNormalize slot := by
  intro h
  apply hneq
  apply IRStorageSlot.eq_of_toNat_eq
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using h

private theorem IRStorageSlot.ne_toNat_of_ne_ofNat_of_lt
    {query : IRStorageSlot} {slot : Nat}
    (hneq : query ≠ IRStorageSlot.ofNat slot)
    (hslot : slot < Compiler.Constants.evmModulus) :
    query.toNat ≠ slot := by
  intro h
  exact IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hneq
    (by simpa [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
      Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt hslot] using h)

private theorem uint256_add_val_eq_mod (a b : Nat) :
    (Verity.Core.Uint256.ofNat a + Verity.Core.Uint256.ofNat b).val =
      (a + b) % Compiler.Constants.evmModulus := by
  change ((a % Compiler.Constants.evmModulus) + (b % Compiler.Constants.evmModulus)) %
      Compiler.Constants.evmModulus =
    (a + b) % Compiler.Constants.evmModulus
  exact (Nat.add_mod a b Compiler.Constants.evmModulus).symm

theorem mappingWordTargetSlot_eq_uint256_add (slot key wordOffset : Nat) :
    mappingWordTargetSlot slot key wordOffset =
      (Verity.Core.Uint256.ofNat wordOffset +
        Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val := by
  unfold mappingWordTargetSlot SourceSemantics.wordNormalize
  simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity]

theorem mapping2WordTargetSlot_eq_uint256_add (slot key1 key2 wordOffset : Nat) :
    mapping2WordTargetSlot slot key1 key2 wordOffset =
      (Verity.Core.Uint256.ofNat wordOffset +
        Verity.Core.Uint256.ofNat
          (Compiler.Proofs.solidityMappingSlot
            (Compiler.Proofs.solidityMappingSlot slot key1) key2)).val := by
  unfold mapping2WordTargetSlot SourceSemantics.wordNormalize
  simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity]

private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    (hneq : query ≠ mappingWordTargetSlot slot key wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq : query = (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mappingWordTargetSlot slot key wordOffset := by
        rw [mappingWordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod (Compiler.Proofs.solidityMappingSlot slot key) wordOffset
            Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMappingWordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMappingWordSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingWordSlots]

private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    {packed : PackedBits}
    (hneq : query ≠ mappingWordTargetSlot slot key wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq : query = (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mappingWordTargetSlot slot key wordOffset := by
        rw [mappingWordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod (Compiler.Proofs.solidityMappingSlot slot key) wordOffset
            Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]

def findResolvedFieldAtSlotCopy (fields : List Field) (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if SourceSemantics.wordNormalize resolvedSlot = SourceSemantics.wordNormalize slot ||
            (field.aliasSlots.map SourceSemantics.wordNormalize).contains
              (SourceSemantics.wordNormalize slot) then
          some field
        else
          go rest (idx + 1)
  go fields 0

def findResolvedFieldAtSlotCopyFrom
    (fields : List Field) (idx : Nat) (slot : Nat) : Option Field :=
  match fields with
  | [] => none
  | field :: rest =>
      let resolvedSlot := field.slot.getD idx
      if SourceSemantics.wordNormalize resolvedSlot = SourceSemantics.wordNormalize slot ||
          (field.aliasSlots.map SourceSemantics.wordNormalize).contains
            (SourceSemantics.wordNormalize slot) then
        some field
      else
      findResolvedFieldAtSlotCopyFrom rest (idx + 1) slot

private theorem SourceSemantics.wordNormalize_idem (slot : Nat) :
    SourceSemantics.wordNormalize (SourceSemantics.wordNormalize slot) =
      SourceSemantics.wordNormalize slot := by
  simp [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus]

theorem findResolvedFieldAtSlotCopyFrom_wordNormalize
    (fields : List Field) (idx slot : Nat) :
    findResolvedFieldAtSlotCopyFrom fields idx (SourceSemantics.wordNormalize slot) =
      findResolvedFieldAtSlotCopyFrom fields idx slot := by
  induction fields generalizing idx with
  | nil => rfl
  | cons field rest ih =>
      simp only [findResolvedFieldAtSlotCopyFrom]
      rw [SourceSemantics.wordNormalize_idem]
      split <;> simp_all

theorem findResolvedFieldAtSlotCopy_wordNormalize
    (fields : List Field) (slot : Nat) :
    findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
      findResolvedFieldAtSlotCopy fields slot := by
  have hgo :
      ∀ (remaining : List Field) (idx : Nat),
      findResolvedFieldAtSlotCopy.go (SourceSemantics.wordNormalize slot) remaining idx =
          findResolvedFieldAtSlotCopy.go slot remaining idx := by
    intro remaining
    induction remaining with
    | nil =>
        intro idx
        rfl
    | cons field rest ih =>
        intro idx
        simp only [findResolvedFieldAtSlotCopy.go]
        rw [SourceSemantics.wordNormalize_idem]
        split
        · rfl
        · exact ih (idx + 1)
  simp only [findResolvedFieldAtSlotCopy]
  exact hgo fields 0

def findDynamicArrayElementAtSlotCopy
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if Compiler.Proofs.solidityMappingSlot baseSlot idx = SourceSemantics.wordNormalize targetSlot then
          some value.val
        else
          scanElements baseSlot rest (idx + 1)
  let rec go (remaining : List Field) (idx : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        match field.ty with
        | .dynamicArray _ =>
            match scanElements resolvedSlot (world.storageArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

private def encodeStorageAtCopy
    (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlotCopy fields slot with
  | some field =>
      if SourceSemantics.fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else if SourceSemantics.fieldUsesDynamicArrayStorage field then
        (world.storageArray slot).length
      else
        (world.storage slot).val
  | none =>
      match findDynamicArrayElementAtSlotCopy fields world slot with
      | some value => value
      | none => (world.storage slot).val

private theorem findResolvedFieldAtSlot_go_eq_copy
    (remaining : List Field) (idx : Nat) (slot : Nat) :
    SourceSemantics.findResolvedFieldAtSlot.go slot remaining idx =
      findResolvedFieldAtSlotCopy.go slot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
    simp only [SourceSemantics.findResolvedFieldAtSlot.go, findResolvedFieldAtSlotCopy.go]
    split <;> simp_all

theorem findResolvedFieldAtSlotCopy_eq
    (fields : List Field) (slot : Nat) :
    SourceSemantics.findResolvedFieldAtSlot fields slot =
      findResolvedFieldAtSlotCopy fields slot := by
  simp only [SourceSemantics.findResolvedFieldAtSlot, findResolvedFieldAtSlotCopy]
  exact findResolvedFieldAtSlot_go_eq_copy fields 0 slot

private theorem findDynamicArrayElementAtSlot_scanElements_eq_copy
    (baseSlot : Nat) (elems : List Verity.Core.Uint256) (idx : Nat) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot.scanElements targetSlot baseSlot elems idx =
      findDynamicArrayElementAtSlotCopy.scanElements targetSlot baseSlot elems idx := by
  induction elems generalizing idx with
  | nil => rfl
  | cons v rest ih =>
    simp only [SourceSemantics.findDynamicArrayElementAtSlot.scanElements,
               findDynamicArrayElementAtSlotCopy.scanElements]
    split <;> simp_all

private theorem findDynamicArrayElementAtSlot_go_eq_copy
    (remaining : List Field) (world : Verity.ContractState)
    (idx : Nat) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot.go world targetSlot remaining idx =
      findDynamicArrayElementAtSlotCopy.go world targetSlot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
    simp only [SourceSemantics.findDynamicArrayElementAtSlot.go,
               findDynamicArrayElementAtSlotCopy.go]
    simp only [findDynamicArrayElementAtSlot_scanElements_eq_copy]
    split
    · split <;> simp_all
    · simp_all

theorem findDynamicArrayElementAtSlotCopy_eq
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot fields world targetSlot =
      findDynamicArrayElementAtSlotCopy fields world targetSlot := by
  simp only [SourceSemantics.findDynamicArrayElementAtSlot, findDynamicArrayElementAtSlotCopy]
  exact findDynamicArrayElementAtSlot_go_eq_copy fields world 0 targetSlot

theorem findDynamicArrayElementAtSlotCopy_scanElements_wordNormalize
    (baseSlot : Nat) (elems : List Verity.Core.Uint256) (idx targetSlot : Nat) :
    findDynamicArrayElementAtSlotCopy.scanElements
        (SourceSemantics.wordNormalize targetSlot) baseSlot elems idx =
      findDynamicArrayElementAtSlotCopy.scanElements targetSlot baseSlot elems idx := by
  induction elems generalizing idx with
  | nil => rfl
  | cons _ rest ih =>
      simp only [findDynamicArrayElementAtSlotCopy.scanElements]
      rw [SourceSemantics.wordNormalize_idem]
      split
      · rfl
      · exact ih (idx + 1)

theorem findDynamicArrayElementAtSlotCopy_go_wordNormalize
    (remaining : List Field) (world : Verity.ContractState) (idx targetSlot : Nat) :
    findDynamicArrayElementAtSlotCopy.go world (SourceSemantics.wordNormalize targetSlot)
        remaining idx =
      findDynamicArrayElementAtSlotCopy.go world targetSlot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
      simp only [findDynamicArrayElementAtSlotCopy.go]
      rw [findDynamicArrayElementAtSlotCopy_scanElements_wordNormalize]
      split
      · split
        · rfl
        · exact ih (idx + 1)
      · exact ih (idx + 1)

theorem findDynamicArrayElementAtSlotCopy_wordNormalize
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) :
    findDynamicArrayElementAtSlotCopy fields world (SourceSemantics.wordNormalize targetSlot) =
      findDynamicArrayElementAtSlotCopy fields world targetSlot := by
  simp only [findDynamicArrayElementAtSlotCopy]
  exact findDynamicArrayElementAtSlotCopy_go_wordNormalize fields world 0 targetSlot

private theorem encodeStorageAt_eq_copy
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat} :
    SourceSemantics.encodeStorageAt fields world slot =
      encodeStorageAtCopy fields world slot := by
  simp only [SourceSemantics.encodeStorageAt, encodeStorageAtCopy,
             findResolvedFieldAtSlotCopy_eq, findDynamicArrayElementAtSlotCopy_eq]
  split <;> simp_all
  split <;> simp_all

private def fieldWriteEntriesAt
    (idx : Nat) (field : Field) : List (Nat × String × Option PackedBits) :=
  firstFieldWriteSlotConflict.fieldOccupiedSlots field (field.slot.getD idx)

private theorem fieldWriteEntriesAt_base_mem
    (idx : Nat) (field : Field) :
    SourceSemantics.wordNormalize (field.slot.getD idx) ∈
      (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
  obtain ⟨name, ty, isTransient, slotOpt, packedBits, aliasSlots⟩ := field
  cases ty with
  | adt _ maxFields =>
      simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
        SourceSemantics.wordNormalize]
      exact Or.inl ⟨0, by omega, by simp⟩
  | _ =>
      simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
        SourceSemantics.wordNormalize]

private theorem exists_mem_zipIdx_of_mem
    {α : Type} {x : α} {xs : List α} {start : Nat}
    (hmem : x ∈ xs) :
    ∃ i, (x, i) ∈ xs.zipIdx start := by
  induction xs generalizing start with
  | nil => simp at hmem
  | cons y ys ih =>
      simp at hmem
      rcases hmem with rfl | hmem
      · exact ⟨start, by simp [List.zipIdx]⟩
      · obtain ⟨i, hi⟩ := ih (start := start + 1) hmem
        exact ⟨i, by simp [List.zipIdx, hi]⟩

private theorem fieldWriteEntriesAt_alias_mem
    {idx : Nat} {field : Field} {slot : Nat}
    (hmem : slot ∈ field.aliasSlots) :
    SourceSemantics.wordNormalize slot ∈
      (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
    obtain ⟨name, ty, isTransient, slotOpt, packedBits, aliasSlots⟩ := field
    obtain ⟨aliasIdx, halias⟩ : ∃ i, (slot, i) ∈ aliasSlots.zipIdx :=
      exists_mem_zipIdx_of_mem hmem
    cases ty with
    | uint256 =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩
    | address =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩
    | adt _ maxFields =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨s!"{name}.aliasSlots[{aliasIdx}]", none, slot, aliasIdx, halias, 0, by omega, by simp⟩
    | dynamicArray _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩
    | mappingTyped _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩
    | mappingStruct _ _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩
    | mappingStruct2 _ _ _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨_, _, _, _, halias, rfl, rfl, rfl⟩

private theorem fieldWriteEntriesAt_packed_none_of_unpacked
    {idx : Nat} {field : Field} {packed : Option PackedBits}
    (hunpacked : field.packedBits = none)
    (hmem : packed ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.2.2)) :
    packed = none := by
  obtain ⟨name, ty, slotOpt, packedBits, aliasSlots⟩ := field
  simp at hunpacked
  subst hunpacked
  cases ty <;>
    simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots] at hmem <;>
    aesop

private def firstInFieldConflictCopy
    (seen : List (Nat × String × Option PackedBits))
    (current : List (Nat × String × Option PackedBits)) :
    Option (Nat × String × String) :=
  match current with
  | [] => none
  | (slot, ownerName, packed) :: tail =>
      match seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
      | some (_, prevName, _) => some (slot, prevName, ownerName)
      | none => firstInFieldConflictCopy ((slot, ownerName, packed) :: seen) tail

private def firstFieldWriteSlotConflictCopyFrom
    (seen : List (Nat × String × Option PackedBits))
    (idx : Nat) (fields : List Field) : Option (Nat × String × String) :=
  match fields with
  | [] => none
  | field :: rest =>
      let writeSlots := fieldWriteEntriesAt idx field
      match firstInFieldConflictCopy seen writeSlots with
      | some conflict => some conflict
      | none => firstFieldWriteSlotConflictCopyFrom (writeSlots.reverse ++ seen) (idx + 1) rest

private theorem list_findSlotPackedNone_ne_none
    {seen : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hmem : slot ∈ seen.map (fun entry => entry.1)) :
    (seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 none)) ≠ none := by
  induction seen with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp at hmem
      by_cases hEq : entry.1 = slot
      · subst hEq
        simp only [List.find?]
        cases entry.2.2 with
        | none => simp [packedSlotsConflict]
        | some _ => simp [packedSlotsConflict]
      · have hrest : slot ∈ List.map (fun entry => entry.1) rest := by
          rcases hmem with ⟨rfl, _⟩ | ⟨_, _, hmem'⟩
          · exact absurd rfl hEq
          · exact List.mem_map.mpr ⟨(slot, _, _), hmem', rfl⟩
        have hih := ih hrest
        change List.find? _ (entry :: rest) ≠ none
        rw [List.find?_cons]
        split
        · simp
        · exact hih

private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hcurrent : slot ∈ current.map (fun entry => entry.1))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by
  induction current generalizing seen with
  | nil =>
      simp at hcurrent
  | cons entry rest ih =>
      simp at hcurrent
      have hpnone : entry.2.2 = none := hunpacked entry.2.2 (by simp)
      have hunpackedRest :
          ∀ packed ∈ rest.map (fun restEntry => restEntry.2.2), packed = none := by
        intro packed hmem
        exact hunpacked packed (by simp [hmem])
      -- entry = (entry.1, entry.2.1, entry.2.2) and entry.2.2 = none
      obtain ⟨e1, e21, e22⟩ := entry
      simp at hpnone
      subst hpnone
      -- Now entry = (e1, e21, none)
      rcases hcurrent with ⟨rfl, _⟩ | ⟨_, _, hrest⟩
      · -- slot = e1
        have hfindSeen := list_findSlotPackedNone_ne_none hseen
        simp only [firstInFieldConflictCopy]
        cases hf : seen.find? (fun seenEntry => seenEntry.1 == e1 && packedSlotsConflict seenEntry.2.2 none)
        · exact absurd hf hfindSeen
        · simp
      · have hrest' : slot ∈ rest.map (fun entry => entry.1) :=
          List.mem_map.mpr ⟨(slot, _, _), hrest, rfl⟩
        intro hnone
        simp only [firstInFieldConflictCopy] at hnone
        cases hfind : seen.find? (fun seenEntry => seenEntry.1 == e1 && packedSlotsConflict seenEntry.2.2 none)
        · rw [hfind] at hnone
          simp at hnone
          have hseen' :
              slot ∈ (((e1, e21, none) :: seen).map (fun seenEntry => seenEntry.1)) := by
            simp [hseen]
          exact (ih hseen' hrest' hunpackedRest) hnone
        · rw [hfind] at hnone; simp at hnone

private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    (hseen : SourceSemantics.wordNormalize targetSlot ∈ seen.map (fun entry => entry.1))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
  induction fields generalizing seen idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at hfind
  | cons field rest ih =>
      simp only [findFieldWithResolvedSlotCopyFrom] at hfind
      simp only [findFieldWriteSlotsCopyFrom] at hwrite
      simp only [firstFieldWriteSlotConflictCopyFrom]
      by_cases hname : field.name == fieldName
      · -- field.name matches: hfind and hwrite resolve here
        simp [hname] at hfind hwrite
        obtain ⟨rfl, rfl⟩ := hfind
        subst hwrite
        -- Need: firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) ≠ none
        -- targetSlot ∈ writeSlots = (field.slot.getD idx :: field.aliasSlots)
        -- fieldWriteEntriesAt produces entries with first components matching writeSlots
        -- and all packed bits = field.packedBits = none
        have htarget_in_entries :
            SourceSemantics.wordNormalize targetSlot ∈
              (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
          simp only [List.mem_cons] at hslot
          rcases hslot with hslot | halias
          · subst targetSlot
            exact fieldWriteEntriesAt_base_mem idx field
          · exact fieldWriteEntriesAt_alias_mem halias
        have hunpacked_entries :
            ∀ packed ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.2.2),
              packed = none := by
          intro packed hmem
          exact fieldWriteEntriesAt_packed_none_of_unpacked hunpacked hmem
        have hconflict := firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
          hseen htarget_in_entries hunpacked_entries
        cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
        | none => exact absurd hc hconflict
        | some _ => simp
      · -- field.name doesn't match: recurse
        simp [hname] at hfind hwrite
        have hseen' :
              SourceSemantics.wordNormalize targetSlot ∈
                ((fieldWriteEntriesAt idx field).reverse ++ seen).map
                (fun entry => entry.1) := by
          rw [List.map_append, List.mem_append]
          exact Or.inr hseen
        cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
        | some _ => simp
        | none => exact ih hseen' hfind hwrite

private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_singleton
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hseen : SourceSemantics.wordNormalize slot ∈ seen.map (fun entry => entry.1))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
  exact
    firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
      hseen hfind hwrite (by simp) hunpacked

theorem findResolvedFieldAtSlotCopyFrom_of_member
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    {seen : List (Nat × String × Option PackedBits)}
    (hnoConflict : firstFieldWriteSlotConflictCopyFrom seen idx fields = none)
    (hfind : findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite : findFieldWriteSlotsCopyFrom fields idx fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopyFrom fields idx targetSlot = some f := by
  induction fields generalizing seen idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at hfind
  | cons field rest ih =>
    simp only [findFieldWithResolvedSlotCopyFrom] at hfind
    simp only [findFieldWriteSlotsCopyFrom] at hwrite
    simp only [firstFieldWriteSlotConflictCopyFrom] at hnoConflict
    simp only [findResolvedFieldAtSlotCopyFrom]
    by_cases hname : field.name == fieldName
    · -- field.name matches: f = field, writeSlots = slot :: aliasSlots
      simp [hname] at hfind hwrite
      obtain ⟨rfl, rfl⟩ := hfind
      subst writeSlots
      simp only [List.mem_cons] at hslot
      rcases hslot with rfl | hmem
      · simp
      · rw [show
          (List.map SourceSemantics.wordNormalize field.aliasSlots).contains
            (SourceSemantics.wordNormalize targetSlot) = true by
            rw [List.contains_eq_mem]
            exact decide_eq_true (List.mem_map.mpr ⟨targetSlot, hmem, rfl⟩)]
        simp
    · -- field.name doesn't match: recurse
      simp [hname] at hfind hwrite
      cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
      | some conflict => rw [hc] at hnoConflict; simp at hnoConflict
      | none =>
        rw [hc] at hnoConflict
        -- After simp, condition is Prop-level: = or ∈
        by_cases hcapture :
            SourceSemantics.wordNormalize (field.slot.getD idx) =
              SourceSemantics.wordNormalize targetSlot ∨
            ∃ a ∈ field.aliasSlots,
              SourceSemantics.wordNormalize a = SourceSemantics.wordNormalize targetSlot
        · exfalso
          have htargetInEntries :
              SourceSemantics.wordNormalize targetSlot ∈
                (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
            rcases hcapture with hbase | ⟨a, haMem, haEq⟩
            · have hb := fieldWriteEntriesAt_base_mem idx field
              rw [hbase] at hb
              exact hb
            · have haIn := fieldWriteEntriesAt_alias_mem (idx := idx) (field := field) haMem
              rw [haEq] at haIn
              exact haIn
          have htargetInSeen :
              SourceSemantics.wordNormalize targetSlot ∈
              ((fieldWriteEntriesAt idx field).reverse ++ seen).map
                (fun entry => entry.1) := by
            rw [List.map_append, List.mem_append, List.map_reverse]
            exact Or.inl (List.mem_reverse.mpr htargetInEntries)
          exact (firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
            htargetInSeen hfind hwrite hslot hunpacked) hnoConflict
        · push_neg at hcapture
          rw [show
            (decide (SourceSemantics.wordNormalize (field.slot.getD idx) =
                SourceSemantics.wordNormalize targetSlot) ||
              (List.map SourceSemantics.wordNormalize field.aliasSlots).contains
                (SourceSemantics.wordNormalize targetSlot)) = false by
            simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not,
              List.contains_eq_mem, List.mem_map]
            exact ⟨hcapture.1, by
              intro hmem
              rcases hmem with ⟨a, haMem, haEq⟩
              exact hcapture.2 a haMem haEq⟩]
          exact ih hnoConflict hfind hwrite

theorem findResolvedFieldAtSlotCopy_go_eq_CopyFrom
    (flds : List Field) (i s : Nat) :
    findResolvedFieldAtSlotCopy.go s flds i = findResolvedFieldAtSlotCopyFrom flds i s := by
  induction flds generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    simp only [findResolvedFieldAtSlotCopy.go, findResolvedFieldAtSlotCopyFrom]
    split <;> simp_all

private theorem firstInFieldConflict_eq_Copy
    (seen current : List (Nat × String × Option PackedBits)) :
    firstFieldWriteSlotConflict.go.firstInFieldConflict seen current =
      firstInFieldConflictCopy seen current := by
  induction current generalizing seen with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨slot, ownerName, packed⟩ := entry
    simp only [firstFieldWriteSlotConflict_firstInFieldConflict_cons,
               firstInFieldConflictCopy]
    cases seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
    | none => exact ih _
    | some _ => rfl

private theorem firstFieldWriteSlotConflict_go_eq_CopyFrom
    (seen : List (Nat × String × Option PackedBits))
    (i : Nat) (flds : List Field) :
    firstFieldWriteSlotConflict.go seen i flds =
      firstFieldWriteSlotConflictCopyFrom seen i flds := by
  induction flds generalizing seen i with
  | nil => rfl
  | cons fld rest ih =>
    rw [firstFieldWriteSlotConflict_go_cons]
    dsimp only []
    rw [firstInFieldConflict_eq_Copy]
    change
      (match firstInFieldConflictCopy seen (fieldWriteEntriesAt i fld) with
       | some conflict => some conflict
       | none =>
           firstFieldWriteSlotConflict.go
             ((fieldWriteEntriesAt i fld).reverse ++ seen) (i + 1) rest) =
        firstFieldWriteSlotConflictCopyFrom seen i (fld :: rest)
    simp only [firstFieldWriteSlotConflictCopyFrom]
    cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt i fld) with
    | none =>
        simpa [hc] using ih ((fieldWriteEntriesAt i fld).reverse ++ seen) (i + 1)
    | some _ =>
        simp [hc]

theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields targetSlot = some f := by
  -- Bridge result
  show findResolvedFieldAtSlotCopy.go targetSlot fields 0 = some f
  rw [findResolvedFieldAtSlotCopy_go_eq_CopyFrom]
  -- Bridge hypotheses
  have hfindCopy : findFieldWithResolvedSlotCopyFrom fields 0 fieldName = some (f, slot) :=
    findFieldWithResolvedSlot_eq_CopyFrom fields fieldName ▸ hfind
  have hwriteCopy : findFieldWriteSlotsCopyFrom fields 0 fieldName = some writeSlots :=
    findFieldWriteSlots_eq_CopyFrom fields fieldName ▸ hwrite
  have hnoConflictCopy : firstFieldWriteSlotConflictCopyFrom [] 0 fields = none :=
    firstFieldWriteSlotConflict_go_eq_CopyFrom [] 0 fields ▸ hnoConflict
  exact findResolvedFieldAtSlotCopyFrom_of_member
    hnoConflictCopy hfindCopy hwriteCopy hslot hunpacked

theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields slot = some f := by
  exact
    findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
      hnoConflict hfind hwrite (by simp) hunpacked

private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by
  simpa [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hnotAddr, hnotDyn]

private theorem encodeStorageAt_eq_storageAddr_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (_hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storageAddr slot).val := by
  simpa [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, haddr]

private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
        (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key)) = value := by
  rw [encodeStorageAt_eq_copy]
  have hresolved' :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key)) = none := by
    rw [findResolvedFieldAtSlotCopy_wordNormalize]
    exact hresolved
  simp only [encodeStorageAtCopy, hresolved']
  have harray : (SourceSemantics.writeUintKeyedMappingSlots
      world [slot] key value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeUintKeyedMappingSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key)) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2]
    rw [findDynamicArrayElementAtSlotCopy_wordNormalize]
    exact hdyn
  simp only [hdyn']
  simp only [SourceSemantics.writeUintKeyedMappingSlots, List.foldl_cons, List.foldl_nil]
  simp only [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot]
  simp only [IRStorageSlot.ofNat_wordNormalize, ite_true, Verity.Core.Uint256.val_ofNat,
    Compiler.Proofs.IRGeneration.IRStorageWord.toNat_ofNat,
    SourceSemantics.UInt256_size_eq_UINT256_MODULUS]
  have hvalue' : value < Verity.Core.UINT256_MODULUS := hvalue
  show value % Verity.Core.UINT256_MODULUS % Verity.Core.UINT256_MODULUS = value
  rw [Nat.mod_eq_of_lt hvalue', Nat.mod_eq_of_lt hvalue']

private theorem encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {keys : List Nat}
    {value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
        (SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys)) = value := by
  rw [encodeStorageAt_eq_copy]
  have hresolved' :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys)) = none := by
    rw [findResolvedFieldAtSlotCopy_wordNormalize]
    exact hresolved
  simp only [encodeStorageAtCopy, hresolved']
  have harray : (SourceSemantics.writeAddressKeyedMappingChainSlots
      world [slot] keys value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingChainSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys)) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys))
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys))
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2]
    rw [findDynamicArrayElementAtSlotCopy_wordNormalize]
    exact hdyn
  simp only [hdyn']
  simp only [SourceSemantics.writeAddressKeyedMappingChainSlots, List.map_cons, List.map_nil,
    List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq, ite_true]
  simp only [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hvalue

private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
        (SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset)) = value := by
  rw [encodeStorageAt_eq_copy]
  have hresolved' :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset)) = none := by
    rw [findResolvedFieldAtSlotCopy_wordNormalize]
    exact hresolved
  simp only [encodeStorageAtCopy, hresolved']
  have harray : (SourceSemantics.writeAddressKeyedMappingWordSlots
      world [slot] key wordOffset value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingWordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset)) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset))
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset))
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2]
    rw [findDynamicArrayElementAtSlotCopy_wordNormalize]
    exact hdyn
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMappingWordSlots, mappingWordTargetSlot,
    SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat]
  have htargetLt :
      (Verity.Core.Uint256.ofNat wordOffset +
          Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val <
        Compiler.Constants.evmModulus :=
    (Verity.Core.Uint256.ofNat wordOffset +
      Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).isLt
  simp [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    htargetLt, Nat.mod_eq_of_lt hvalue]
  simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS] using hvalue

private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    {packed : PackedBits}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mappingWordTargetSlot slot key wordOffset) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset) =
      SourceSemantics.packedWordWrite
        (world.storage (mappingWordTargetSlot slot key wordOffset)).val
        value
        packed := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
      world [slot] key wordOffset packed value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (mappingWordTargetSlot slot key wordOffset)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots, mappingWordTargetSlot,
    SourceSemantics.wordNormalize, SourceSemantics.packedWordWrite,
    Verity.Core.Uint256.val_ofNat]
  have hlt :
      (((Verity.Core.Uint256.ofNat (world.storage (mappingWordTargetSlot slot key wordOffset)).val).and
        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
        (Verity.Core.Uint256.shl packed.offset
          (Verity.Core.Uint256.and value (packedMaskNat packed)))).val <
        Compiler.Constants.evmModulus := by
    exact
      ((((Verity.Core.Uint256.ofNat (world.storage (mappingWordTargetSlot slot key wordOffset)).val).and
        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
        (Verity.Core.Uint256.shl packed.offset
          (Verity.Core.Uint256.and value (packedMaskNat packed)))).isLt)
  simpa [mappingWordTargetSlot, SourceSemantics.wordNormalize,
    Compiler.Proofs.abstractMappingSlot_eq_solidity] using hlt

private theorem encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
        {slot key1 key2 query value : Nat}
        (hquery : query < Compiler.Constants.evmModulus)
        (hneq :
          IRStorageSlot.ofNat query ≠
            IRStorageSlot.ofNat (Compiler.Proofs.abstractMappingSlot
            (Compiler.Proofs.abstractMappingSlot slot key1)
            key2)) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
        query =
        SourceSemantics.encodeStorageAt fields world query := by
      apply SourceSemantics.encodeStorageAt_congr
      · simp only [SourceSemantics.writeAddressKeyedMapping2Slots, List.foldl_cons, List.foldl_nil]
        have hneq' :
            ¬IRStorageSlot.ofNat query =
              IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot
                (Compiler.Proofs.solidityMappingSlot slot key1) key2) := by
          simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using hneq
        simp [Compiler.Proofs.abstractStoreMappingEntry, hneq', Nat.mod_eq_of_lt hquery,
          Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
        apply Verity.Core.Uint256.ext
        have hltLit :
            (world.storage query).val <
              115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using
            (world.storage query).isLt
        simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
          Nat.mod_eq_of_lt (world.storage query).isLt, Nat.mod_eq_of_lt hltLit]
      · simp [SourceSemantics.writeAddressKeyedMapping2Slots]
      · simp [SourceSemantics.writeAddressKeyedMapping2Slots]

private theorem encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
        (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2)) = value := by
  rw [encodeStorageAt_eq_copy]
  have hresolved' :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
            (Compiler.Proofs.abstractMappingSlot slot key1) key2)) = none := by
    rw [findResolvedFieldAtSlotCopy_wordNormalize]
    exact hresolved
  simp only [encodeStorageAtCopy, hresolved']
  have harray : (SourceSemantics.writeAddressKeyedMapping2Slots
      world [slot] key1 key2 value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMapping2Slots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2)) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2))
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2))
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2]
    rw [findDynamicArrayElementAtSlotCopy_wordNormalize]
    exact hdyn
  simp only [hdyn']
  simp only [SourceSemantics.writeAddressKeyedMapping2Slots, List.foldl_cons, List.foldl_nil]
  simp only [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot]
  simp only [IRStorageSlot.ofNat_wordNormalize, ite_true, Verity.Core.Uint256.val_ofNat,
    Compiler.Proofs.IRGeneration.IRStorageWord.toNat_ofNat,
    SourceSemantics.UInt256_size_eq_UINT256_MODULUS]
  have hvalue' : value < Verity.Core.UINT256_MODULUS := hvalue
  show value % Verity.Core.UINT256_MODULUS % Verity.Core.UINT256_MODULUS = value
  rw [Nat.mod_eq_of_lt hvalue', Nat.mod_eq_of_lt hvalue']

private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset query value : Nat}
    (hneq :
      query ≠ mapping2WordTargetSlot slot key1 key2 wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq :
        query =
          (Compiler.Proofs.solidityMappingSlot
            (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
            Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mapping2WordTargetSlot slot key1 key2 wordOffset := by
        rw [mapping2WordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat
                (Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1) key2)).val =
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
              Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1) key2 %
                  Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2)
            wordOffset Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]
  · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]

private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
        (SourceSemantics.wordNormalize (mapping2WordTargetSlot slot key1 key2 wordOffset)) = value := by
  rw [encodeStorageAt_eq_copy]
  have hresolved' :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.wordNormalize (mapping2WordTargetSlot slot key1 key2 wordOffset)) = none := by
    rw [findResolvedFieldAtSlotCopy_wordNormalize]
    exact hresolved
  simp only [encodeStorageAtCopy, hresolved']
  have harray : (SourceSemantics.writeAddressKeyedMapping2WordSlots
      world [slot] key1 key2 wordOffset value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (SourceSemantics.wordNormalize (mapping2WordTargetSlot slot key1 key2 wordOffset)) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (SourceSemantics.wordNormalize (mapping2WordTargetSlot slot key1 key2 wordOffset))
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.wordNormalize (mapping2WordTargetSlot slot key1 key2 wordOffset))
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2]
    rw [findDynamicArrayElementAtSlotCopy_wordNormalize]
    exact hdyn
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMapping2WordSlots, mapping2WordTargetSlot,
    SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat]
  have htargetLt :
      (Verity.Core.Uint256.ofNat wordOffset +
          Verity.Core.Uint256.ofNat
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2)).val <
        Compiler.Constants.evmModulus :=
    (Verity.Core.Uint256.ofNat wordOffset +
      Verity.Core.Uint256.ofNat
        (Compiler.Proofs.solidityMappingSlot
          (Compiler.Proofs.solidityMappingSlot slot key1) key2)).isLt
  simp [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    htargetLt, Nat.mod_eq_of_lt hvalue]
  simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS] using hvalue

private def abstractStoreStorageOrMappingMany
    (storage : Compiler.Proofs.IRGeneration.IRStorageSlot →
      Compiler.Proofs.IRGeneration.IRStorageWord)
    (slots : List Nat) (value : Nat) :
    Compiler.Proofs.IRGeneration.IRStorageSlot →
      Compiler.Proofs.IRGeneration.IRStorageWord :=
  match slots with
  | [] => storage
  | slot :: rest =>
      abstractStoreStorageOrMappingMany
        (Compiler.Proofs.abstractStoreStorageOrMapping storage slot value)
        rest
        value

private theorem abstractStoreStorageOrMappingMany_eq
    {storage : Compiler.Proofs.IRGeneration.IRStorageSlot →
      Compiler.Proofs.IRGeneration.IRStorageWord}
    {slots : List Nat}
    {value : Nat} {query : Compiler.Proofs.IRGeneration.IRStorageSlot} :
    abstractStoreStorageOrMappingMany storage slots value query =
      if ∃ slot ∈ slots, query = Compiler.Proofs.IRGeneration.IRStorageSlot.ofNat slot then
        Compiler.Proofs.IRGeneration.IRStorageWord.ofNat value
      else storage query := by
  induction slots generalizing storage with
  | nil =>
      simp [abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      simp only [abstractStoreStorageOrMappingMany]
      rw [ih]
      by_cases hEq : query = Compiler.Proofs.IRGeneration.IRStorageSlot.ofNat slot
      · subst hEq
        simp [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      · simp [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hEq]

private theorem runtimeStateMatchesIR_writeUintSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  ·
    by_cases hEq : query = IRStorageSlot.ofNat slot
    · subst hEq
      rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = some f := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) = some f from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
      rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' hnotAddr hnotDyn]
      simp [SourceSemantics.writeUintSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS, Verity.Core.Uint256.val_ofNat]
      exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (Nat.mod_eq_of_lt hvalue).symm
    · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      simp only [hEq, ↓reduceIte]
      rw [hstorage]
      exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (encodeStorageAt_writeUintSlots_singleton_other
          (IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot
            (value &&& Compiler.Constants.addressMask) } := by
    rcases hruntime with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
    refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
    funext query
    by_cases hEq : query = IRStorageSlot.ofNat slot
    · subst hEq
      rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = some f := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) = some f from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
      rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot hresolved' haddr hnotDyn]
      simp [SourceSemantics.writeAddressSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Verity.wordToAddress, Verity.Core.Address.ofNat, Verity.Core.Uint256.val_ofNat,
        Verity.Core.Address.modulus, Compiler.Constants.addressMask]
      rw [Nat.mod_eq_of_lt hvalue]
      refine congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat ?_
      simpa [Compiler.Constants.addressMask, Verity.Core.Address.modulus] using
        (Nat.and_two_pow_sub_one_eq_mod (n := 160) value)
    · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      simp only [hEq, ↓reduceIte]
      rw [hstorage]
      symm
      refine congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat ?_
      have hneqNat := IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq
      have hneqNat' : query.toNat ≠ slot % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.wordNormalize] using hneqNat
      apply SourceSemantics.encodeStorageAt_congr
      · simp [SourceSemantics.writeAddressSlots]
      · simp [SourceSemantics.writeAddressSlots, SourceSemantics.wordNormalize, hneqNat']
      · simp [SourceSemantics.writeAddressSlots]

private theorem runtimeStateMatchesIR_writeUintSlots
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : ∀ slot ∈ slots, findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world slots value }
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [abstractStoreStorageOrMappingMany_eq]
  ·
      by_cases hmem : ∃ slot ∈ slots, query = IRStorageSlot.ofNat slot
      · simp only [hmem, ↓reduceIte]
        rcases hmem with ⟨slot, hslotMem, rfl⟩
        have hresolved' :
            findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = some f := by
          simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
            (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) = some f from
              by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved slot hslotMem)
        rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' hnotAddr hnotDyn]
        have hcontains :
              (slots.map SourceSemantics.wordNormalize).contains
                (SourceSemantics.wordNormalize slot) = true := by
            rw [List.contains_eq_mem]
            exact decide_eq_true (List.mem_map.mpr ⟨slot, hslotMem, rfl⟩)
        have hcontains' :
              (slots.map SourceSemantics.wordNormalize).contains
                (slot % Verity.Core.Uint256.modulus) = true := by
            simpa [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
              Verity.Core.UINT256_MODULUS, Verity.Core.Uint256.modulus] using hcontains
        simp only [SourceSemantics.writeUintSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
            SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
            Verity.Core.UINT256_MODULUS, hcontains',
            ↓reduceIte, Verity.Core.Uint256.val_ofNat]
        exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (Nat.mod_eq_of_lt hvalue).symm
      · simp only [hmem, ↓reduceIte]
        rw [hstorage]
        have hnotMem : query.toNat ∉ slots.map SourceSemantics.wordNormalize := by
          intro hq
          rcases List.mem_map.mp hq with ⟨slot, hslotMem, hslotEq⟩
          apply hmem
          exact ⟨slot, hslotMem, IRStorageSlot.eq_of_toNat_eq (by
            simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using hslotEq.symm)⟩
        exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
          (encodeStorageAt_writeUintSlots_other hnotMem).symm

private theorem runtimeStateMatchesIR_writeUintKeyedMappingSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot slot key)
  · subst hEq
    simp only [↓reduceIte]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
          Compiler.Proofs.abstractMappingSlot_eq_solidity,
          SourceSemantics.wordNormalize_idem] using
          (encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
            (fields := fields) (world := runtime.world) (slot := slot) (key := key)
            (value := value) hresolved hdyn hvalue).symm)
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key := key) (query := query.toNat) (value := value)
          (by simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using IRStorageSlot.toNat_lt_size query)
      (IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeTransientTarget
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {target value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeTransientTargets runtime.world [target] value }
      { state with
          transientStorage := fun slot =>
            if slot = SourceSemantics.wordNormalize target then value else state.transientStorage slot } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, ?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  · funext query
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorageAt_congr (by simp [SourceSemantics.writeTransientTargets])
        (by simp [SourceSemantics.writeTransientTargets])
        (by simp [SourceSemantics.writeTransientTargets]))
  · funext slot
    by_cases hslot : slot = SourceSemantics.wordNormalize target
    · subst hslot
      simp [SourceSemantics.writeTransientTargets]
      exact (Nat.mod_eq_of_lt (by
        simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
          Verity.Core.Uint256.modulus] using hvalue)).symm
    · simp [SourceSemantics.writeTransientTargets, hslot]
      have hslot' : slot ≠ target % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.wordNormalize] using hslot
      simp [hslot', congrFun htransient slot]

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot : Nat}
    {keys : List Nat}
    {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainSlots
            runtime.world [slot] keys value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (SourceSemantics.mappingSlotChain slot keys)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (SourceSemantics.mappingSlotChain slot keys)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (SourceSemantics.mappingSlotChain slot keys) =
        (runtime.world.storage (SourceSemantics.mappingSlotChain slot keys)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
          SourceSemantics.wordNormalize_idem] using
          (encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_eq_written
            (fields := fields) (world := runtime.world) (slot := slot) (keys := keys)
            (value := value) hresolved hdyn hvalue).symm)
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (keys := keys)
      (query := query.toNat) (value := value)
      (IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  -- writeAddressKeyedMappingSlots has the same storage/storageAddr/storageArray as writeUintKeyedMappingSlots
  -- so encodeStorageAt produces identical results; we bridge via encodeStorageAt_congr
  have hbridge : ∀ q, SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingSlots runtime.world [slot] key value) q =
      SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots runtime.world [slot] key value) q := by
    intro q
    apply SourceSemantics.encodeStorageAt_congr
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  rw [hbridge]
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot slot key)
  · subst hEq
    simp only [↓reduceIte]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
          Compiler.Proofs.abstractMappingSlot_eq_solidity,
          SourceSemantics.wordNormalize_idem] using
          (encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
            (fields := fields) (world := runtime.world) (slot := slot) (key := key)
            (value := value) hresolved hdyn hvalue).symm)
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key := key) (query := query.toNat) (value := value)
      (by simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using IRStorageSlot.toNat_lt_size query)
      (IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordSlots
            runtime.world [slot] key wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mappingWordTargetSlot slot key wordOffset)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) =
        (runtime.world.storage (mappingWordTargetSlot slot key wordOffset)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
          simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
            mappingWordTargetSlot, SourceSemantics.wordNormalize,
            SourceSemantics.wordNormalize_idem, Compiler.Constants.evmModulus,
            Verity.Core.UINT256_MODULUS] using
          (encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
            (fields := fields) (world := runtime.world) (slot := slot) (key := key)
            (wordOffset := wordOffset) (value := value) hresolved hdyn hvalue).symm)
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (key := key)
        (wordOffset := wordOffset) (query := query.toNat) (value := value)
        (by simpa [mappingWordTargetSlot] using
          IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {slot key wordOffset value : Nat} {packed : PackedBits}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingPackedWordSlots
            runtime.world [slot] key wordOffset packed value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mappingWordTargetSlot slot key wordOffset)
            (SourceSemantics.packedWordWrite
              (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
                (state.storage (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset))))
              value
              packed) } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  set tgt := mappingWordTargetSlot slot key wordOffset with htgt
  by_cases hEq : query = IRStorageSlot.ofNat tgt
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world tgt =
        (runtime.world.storage tgt).val := by
      rw [encodeStorageAt_eq_copy]; simp only [encodeStorageAtCopy, hresolved, hdyn]
    have htgtNorm : SourceSemantics.wordNormalize tgt = tgt := by
      rw [htgt]
      exact SourceSemantics.wordNormalize_idem _
    have htgtSlot : (IRStorageSlot.ofNat tgt).toNat = tgt := by
      rw [IRStorageSlot.toNat_ofNat_wordNormalize, htgtNorm]
    have htgtLt : tgt < Verity.Core.UINT256_MODULUS := by
      have h := SourceSemantics.wordNormalize_lt_evmModulus tgt
      rw [htgtNorm] at h
      simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using h
    have htgtLtLit :
        mappingWordTargetSlot slot key wordOffset <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      simpa [htgt, Verity.Core.UINT256_MODULUS] using htgtLt
    have hstorageLtLit :
        (runtime.world.storage (mappingWordTargetSlot slot key wordOffset)).val <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using
        (runtime.world.storage (mappingWordTargetSlot slot key wordOffset)).isLt
    have hencNorm : SourceSemantics.encodeStorageAt fields runtime.world
        (IRStorageSlot.ofNat tgt).toNat = (runtime.world.storage tgt).val := by
      simpa [htgtSlot] using henc
    simp only [hstorage, hencNorm]
    simp [IRStorageWord.toNat_ofNat, EvmYul.UInt256.size,
      Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt (runtime.world.storage tgt).isLt]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [htgt, Nat.mod_eq_of_lt htgtLtLit, Nat.mod_eq_of_lt hstorageLtLit] using
        (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
          (fields := fields) (world := runtime.world) (slot := slot) (key := key)
          (wordOffset := wordOffset) (packed := packed) (value := value) hresolved hdyn).symm)
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]; rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
        (fields := fields) (world := runtime.world) (slot := slot) (key := key)
          (wordOffset := wordOffset) (packed := packed) (query := query.toNat) (value := value)
          (by simpa [htgt, mappingWordTargetSlot] using
            IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key1 key2 value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2Slots runtime.world [slot] key1 key2 value }
      { state with
          storage :=
            Compiler.Proofs.abstractStoreMappingEntry
              state.storage
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2
              value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query =
      (IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2))
  · subst hEq
    simp only [↓reduceIte]
    rw [Compiler.Proofs.abstractMappingSlot_eq_solidity] at hresolved hdyn
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
          simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity,
            SourceSemantics.wordNormalize_idem] using
            (encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
                (fields := fields) (world := runtime.world)
                (slot := slot) (key1 := key1) (key2 := key2) (value := value)
                hresolved hdyn hvalue).symm)
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key1 := key1) (key2 := key2)
      (query := query.toNat) (value := value)
      (by simpa [Compiler.Constants.evmModulus, EvmYul.UInt256.size] using IRStorageSlot.toNat_lt_size query)
      (by simpa [IRStorageSlot.ofNat_toNat] using hEq)).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key1 key2 wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2WordSlots
            runtime.world [slot] key1 key2 wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mapping2WordTargetSlot slot key1 key2 wordOffset)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (mapping2WordTargetSlot slot key1 key2 wordOffset)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) =
        (runtime.world.storage (mapping2WordTargetSlot slot key1 key2 wordOffset)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
          simpa [IRStorageSlot.toNat_ofNat_wordNormalize,
            mapping2WordTargetSlot, SourceSemantics.wordNormalize,
            SourceSemantics.wordNormalize_idem, Compiler.Constants.evmModulus,
            Verity.Core.UINT256_MODULUS] using
          (encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
            (fields := fields) (world := runtime.world)
            (slot := slot) (key1 := key1) (key2 := key2) (wordOffset := wordOffset)
            (value := value) hresolved hdyn hvalue).symm)
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (key1 := key1)
        (key2 := key2) (wordOffset := wordOffset) (query := query.toNat) (value := value)
        (by simpa [mapping2WordTargetSlot] using
          IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  intro name hname
  simpa [IRState.getVar, Compiler.Proofs.abstractStoreStorageOrMapping_eq] using
    hexact name hname

private theorem bindingsExactlyMatchIRVarsOnScope_writeMappingSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot key value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  intro name hname
  simpa [IRState.getVar, Compiler.Proofs.abstractStoreMappingEntry_eq] using
    hexact name hname

private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlots
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  intro name hname
  simpa [IRState.getVar, abstractStoreStorageOrMappingMany_eq] using
    hexact name hname

private theorem execIRStmts_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (name : String)
    (value : Nat)
    (hvalue : IRState.getVar state name = value) :
    execIRStmts (slots.length + fuel + 1) state
      (slots.map (fun slot =>
        YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name]))) =
      .continue
        { state with
            storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  induction slots generalizing state fuel with
  | nil =>
      simp [execIRStmts, abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      let nextState :=
        { state with
            storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value }
      have hstmt :
          execIRStmt (rest.length + fuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name])) =
              .continue nextState := by
        apply execIRStmt_sstore_lit_expr_succ_of_eval
        simp only [evalIRExpr]; exact hvalue
      have hvalueNext : IRState.getVar nextState name = value := by
        simp only [nextState, IRState.getVar]; exact hvalue
      have htail :=
        ih (fuel := fuel) (state := nextState) hvalueNext
      simp only [execIRStmts, List.map, List.length_cons]
      have hfuel : rest.length + 1 + fuel = rest.length + fuel + 1 := by omega
      rw [hfuel, hstmt]
      simp only [abstractStoreStorageOrMappingMany]
      convert htail using 2

private theorem execIRStmts_let_then_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (tempName : String)
    (valueIR : YulExpr)
    (value : Nat)
    (hvalue : evalIRExpr state valueIR = some value) :
    execIRStmts (slots.length + fuel + 2) state
      (YulStmt.let_ tempName valueIR ::
        slots.map (fun slot =>
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident tempName]))) =
      .continue
        { state.setVar tempName value with
            storage :=
              abstractStoreStorageOrMappingMany
                (state.setVar tempName value).storage
                slots
                value } := by
  have hlet :
      execIRStmt (slots.length + fuel + 1) state
        (YulStmt.let_ tempName valueIR) =
          .continue (state.setVar tempName value) := by
    simp [execIRStmt, hvalue]
  have hslots :=
    execIRStmts_sstore_lit_ident_slots_continue
      fuel
      (state.setVar tempName value)
      slots
      tempName
      value
      (by simp [IRState.getVar, IRState.setVar])
  simpa [execIRStmts, hlet] using hslots

private theorem execIRStmts_single_block_of_continue
    (fuel : Nat)
    (state next : IRState)
    (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts (fuel + 2) state [YulStmt.block body] = .continue next := by
  have hblock :
      execIRStmt (fuel + 1) state (YulStmt.block body) = .continue next := by
    simpa [execIRStmt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbody
  simpa [execIRStmts, hblock]

private theorem singletonBlock_sizeOf_slack (body : List YulStmt) :
    sizeOf [YulStmt.block body] - [YulStmt.block body].length = sizeOf body + 2 := by
  simp [YulStmt.block.sizeOf_spec]
  omega

private theorem compatValue_not_mem_scope_of_reservedPrefix
    {scope : List String}
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope) :
    "__compat_value" ∉ scope := by
  exact hscopeReserved.1

private theorem compatScratch_startsWith_reserved
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__" = true := by
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_value".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_packed".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_word".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_cleared".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide

private theorem compatScratch_not_internalImmutable
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__immutable_" = false := by
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_value".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_packed".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_word".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_cleared".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3

private theorem validateIdentifierShapes_fieldName_ne_reservedScratch
    {spec : CompilationModel}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : name ∈ spec.fields.map (·.name)) :
    name ≠ "__compat_value" ∧
    name ≠ "__compat_packed" ∧
    name ≠ "__compat_slot_word" ∧
    name ≠ "__compat_slot_cleared" := by
  rcases List.mem_map.mp hmem with ⟨field, hfield, rfl⟩
  have hreserved :=
    CompilationModel.validateIdentifierShapes_field_avoidReservedCompilerPrefix hvalidate hfield
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_value".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inl rfl)
      have himm : "__compat_value".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_packed".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inl rfl)
      have himm : "__compat_packed".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_slot_word".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inr <| Or.inl rfl)
      have himm : "__compat_slot_word".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inr <| Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_slot_cleared".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inr <| Or.inr rfl)
      have himm : "__compat_slot_cleared".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inr <| Or.inr rfl)
      simpa [hEq, hprefix, himm])

private theorem scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {scope : List String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hscopeNames :
      ∀ name, name ∈ scope →
        name ∈
          (fn.params.map (·.name) ++
            collectStmtListBindNames fn.body ++
            collectStmtListAssignedNames fn.body ++
            spec.fields.map (·.name))) :
    scopeAvoidsReservedCompilerPrefix scope := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    have hname := hscopeNames "__compat_value" hmem
    have hname' :
        "__compat_value" ∈ fn.params.map (·.name) ∨
        "__compat_value" ∈ collectStmtListBindNames fn.body ∨
        "__compat_value" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_value" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inl rfl))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inl rfl))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inl rfl))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_packed" hmem
    have hname' :
        "__compat_packed" ∈ fn.params.map (·.name) ∨
        "__compat_packed" ∈ collectStmtListBindNames fn.body ∨
        "__compat_packed" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_packed" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_slot_word" hmem
    have hname' :
        "__compat_slot_word" ∈ fn.params.map (·.name) ∨
        "__compat_slot_word" ∈ collectStmtListBindNames fn.body ∨
        "__compat_slot_word" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_slot_word" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.2.1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_slot_cleared" hmem
    have hname' :
        "__compat_slot_cleared" ∈ fn.params.map (·.name) ∨
        "__compat_slot_cleared" ∈ collectStmtListBindNames fn.body ∨
        "__compat_slot_cleared" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_slot_cleared" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.2.2 rfl

private theorem findFieldWriteSlots_of_findFieldWithResolvedSlot
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    findFieldWriteSlots fields name = some (slot :: f.aliasSlots) := by
  rw [findFieldWriteSlots_eq_CopyFrom, findFieldWithResolvedSlot_eq_CopyFrom] at *
  revert h
  suffices ∀ idx,
      findFieldWithResolvedSlotCopyFrom fields idx name = some (f, slot) →
      findFieldWriteSlotsCopyFrom fields idx name = some (slot :: f.aliasSlots) by
    exact this 0
  intro idx h
  induction fields generalizing idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at h
  | cons hd tl ih =>
    unfold findFieldWithResolvedSlotCopyFrom at h
    unfold findFieldWriteSlotsCopyFrom
    by_cases hname : hd.name == name
    · rw [if_pos hname] at h ⊢
      simp at h
      rcases h with ⟨hf, hslot⟩
      rw [← hf, ← hslot]
    · rw [if_neg hname] at h ⊢
      exact ih (idx + 1) h

private theorem findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton
    {fields : List Field} {name : String} {slot : Nat}
    (h : findFieldWriteSlots fields name = some [slot]) :
    ∃ f, findFieldWithResolvedSlot fields name = some (f, slot) ∧ f.aliasSlots = [] := by
  rw [findFieldWriteSlots_eq_CopyFrom, findFieldWithResolvedSlot_eq_CopyFrom] at *
  revert h
  suffices ∀ idx,
      findFieldWriteSlotsCopyFrom fields idx name = some [slot] →
      ∃ f, findFieldWithResolvedSlotCopyFrom fields idx name = some (f, slot) ∧
        f.aliasSlots = [] by
    exact this 0
  intro idx h
  induction fields generalizing idx with
  | nil => simp [findFieldWriteSlotsCopyFrom] at h
  | cons hd tl ih =>
    unfold findFieldWriteSlotsCopyFrom at h
    unfold findFieldWithResolvedSlotCopyFrom
    by_cases hname : hd.name == name
    · rw [if_pos hname] at h ⊢
      simp at h
      rcases h with ⟨hslot, halias⟩
      exact ⟨hd, by simpa [hslot, halias]⟩
    · rw [if_neg hname] at h ⊢
      exact ih (idx + 1) h

private def fieldStoreBuiltin (fields : List Field) (fieldName : String) : String :=
  if SourceSemantics.fieldIsTransient fields fieldName then "tstore" else "sstore"

private def fieldLoadBuiltin (fields : List Field) (fieldName : String) : String :=
  if SourceSemantics.fieldIsTransient fields fieldName then "tload" else "sload"

theorem compiledStmtStep_setStorage_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (halias : f.aliasSlots = [])
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, halias, hunpacked, hnotTransient, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
    have hresolvedSlot :
        findResolvedFieldAtSlotCopy fields slot = some f :=
      findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
        hnoConflict hfind hwriteSlots hunpacked
    have hvalueSourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at hvalueSourceEval
    simp [Except.toOption] at hvalueSourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcore hexact hinScope hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeUintSlots runtime.world [slot] valueNat }
      have hfieldTransient :
          SourceSemantics.fieldIsTransient fields fieldName = false := by
        simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setStorage fieldName value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, SourceSemantics.writeUintFieldSlots,
          SourceSemantics.writeMappingTargets, hwriteSlots, hValueSrc, hfieldTransient, runtime']
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
              .continue state' :=
        execIRStmt_sstore_lit_expr_succ_of_eval
          extraFuel state slot valueIR valueNat hIRValue
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setStorage fieldName value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hv | hs
        · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
        · exact hs
      have hexact' := FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
        (bindingsExactlyMatchIRVarsOnScope_writeUintSlot (slot := slot) (value := valueNat) hexact)
        hincl
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨runtimeStateMatchesIR_writeUintSlot hruntime hresolvedSlot hnotAddr hnotDyn hvalueLt,
        hexact', hbounded, hscope'⟩

private theorem compiledStmtStep_setStorageAddr_singleSlot_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ runtime state extraFuel,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf
          [YulStmt.expr
            (YulExpr.call "sstore"
              [YulExpr.lit slot,
                YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [YulExpr.lit slot,
              YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setStorageAddr fieldName value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.lit slot,
                  YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.lit slot,
                  YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] =
          irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStorageAddr fieldName value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR :=
    [YulStmt.expr
      (YulExpr.call "sstore"
        [YulExpr.lit slot,
          YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])]
  have hresolvedSlot : findResolvedFieldAtSlotCopy fields slot =
      some { name := fieldName, ty := FieldType.address } :=
    findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind hwriteSlots (by rfl)
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcore hexact hinScope hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
      hruntime
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hvalueSourceEval
  rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
  · simp [hIRValue, Option.bind] at hvalueSourceEval
  · simp [hIRValue, Option.bind] at hvalueSourceEval
    have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
      hvalueSourceEval.symm
    have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hValueSrc] at hvalueLt
    simp at hvalueLt
    have hMaskedEvalRaw :
        evalIRExpr state
          (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
            some ((valueNat % Compiler.Constants.evmModulus) &&&
              (Compiler.Constants.addressMask % Compiler.Constants.evmModulus)) := by
      simpa using FunctionBody.evalIRExpr_and_of_eval
        (state := state)
        (lhs := valueIR)
        (rhs := YulExpr.hex Compiler.Constants.addressMask)
        (b := Compiler.Constants.addressMask)
        hIRValue
        (by simp [evalIRExpr, Compiler.Constants.addressMask])
    have hMaskedEval :
        evalIRExpr state
          (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
            some (valueNat &&& Compiler.Constants.addressMask) := by
      simpa [Nat.mod_eq_of_lt hvalueLt, Compiler.Constants.addressMask] using hMaskedEvalRaw
    set state' := { state with
        storage :=
          Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot
            (valueNat &&& Compiler.Constants.addressMask) }
    set runtime' := { runtime with
        world := SourceSemantics.writeAddressSlots runtime.world [slot] valueNat }
    have hfieldTransient :
        SourceSemantics.fieldIsTransient fields fieldName = false := by
      simp [SourceSemantics.fieldIsTransient, hfind]
    have hSrcExec : SourceSemantics.execStmt fields runtime
        (.setStorageAddr fieldName value) = .continue runtime' := by
      simp [SourceSemantics.execStmt, SourceSemantics.writeAddressFieldSlots,
        hwriteSlots, hValueSrc, hfieldTransient, runtime']
    have hExecStmt :
        execIRStmt (extraFuel + 1) state
          (YulStmt.expr
            (YulExpr.call "sstore"
              [YulExpr.lit slot,
                YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])) =
          .continue state' :=
      execIRStmt_sstore_lit_expr_succ_of_eval
        extraFuel state slot
        (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask])
        (valueNat &&& Compiler.Constants.addressMask)
        hMaskedEval
    have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
    have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
        .continue state' := by
      simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
    have hincl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.setStorageAddr fieldName value)) scope := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with hv | hs
      · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
      · exact hs
    have hexact' := FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (bindingsExactlyMatchIRVarsOnScope_writeUintSlot
        (state := state) (slot := slot)
        (value := valueNat &&& Compiler.Constants.addressMask) hexact)
      hincl
    have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
    refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
    simp [stmtStepMatchesIRExec]
    exact ⟨runtimeStateMatchesIR_writeAddressSlot hruntime hresolvedSlot (by rfl) (by rfl) hvalueLt,
      hexact', hbounded, hscope'⟩

theorem compiledStmtStep_setStorageAddr_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorageAddr fieldName value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.lit slot,
            YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] where
  compileOk := by
    have hNotMapping : isMapping fields fieldName = false :=
      isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, hwriteSlots, hvalueIR]
  preserves := compiledStmtStep_setStorageAddr_singleSlot_preserves
    hcore hinScope hfind hwriteSlots hnoConflict hvalueIR

private theorem compiledStmtStep_mstore_single_preserves
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] -
        [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.mstore offset value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.mstore offset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])]
  have hOffsetEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreOffset hexact hinScopeOffset hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
      hruntime
  have hValueEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hoffsetIR] at hOffsetEval
  rw [hvalueIR] at hValueEval
  simp [Except.toOption] at hOffsetEval hValueEval
  rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
  · simp [hIROffset, Option.bind] at hOffsetEval
  · simp [hIROffset, Option.bind] at hOffsetEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hValueEval
    · simp [hIRValue, Option.bind] at hValueEval
      have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
        hOffsetEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hValueEval.symm
      -- Source execution: mstore updates source-level memory
      set runtime' := {
        runtime with
        world := {
          runtime.world with
          memory := fun o =>
            if o = offsetNat then valueNat else runtime.world.memory o
        }
      }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.mstore offset value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc, runtime']
      -- IR execution: mstore updates IR-level memory
      set state' := { state with
          memory := fun o => if o = offsetNat then valueNat else state.memory o }
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion (same structure as tstore)
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.mstore offset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with ho | hv | hs
        · exact hinScopeOffset n (collectExprNames_mem_exprBoundNames_of_core hcoreOffset n ho)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Bindings: getVar only depends on vars, not memory
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.mstore offset value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope, state', runtime'] using hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.mstore offset value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
        simpa [runtime'] using hbounded
      have hValueLt : valueNat < Verity.Core.Uint256.modulus := by
        have := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue) hruntime
        rw [hValueSrc] at this; exact this
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' := by
        show FunctionBody.runtimeStateMatchesIR fields _ _
        exact FunctionBody.runtimeStateMatchesIR_setBothMemory hruntime offsetNat valueNat hValueLt
      exact ⟨_, _, hSrcExec, hIRExec,
        hruntime', hexact', hbounded', hscope'⟩

theorem compiledStmtStep_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.mstore offset value)
      [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_mstore_single_preserves
    hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

private theorem compiledStmtStep_tstore_single_preserves
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] -
        [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.tstore offset value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.tstore offset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])]
  have hOffsetEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreOffset hexact hinScopeOffset hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
      hruntime
  have hValueEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hoffsetIR] at hOffsetEval
  rw [hvalueIR] at hValueEval
  simp [Except.toOption] at hOffsetEval hValueEval
  rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
  · simp [hIROffset, Option.bind] at hOffsetEval
  · simp [hIROffset, Option.bind] at hOffsetEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hValueEval
    · simp [hIRValue, Option.bind] at hValueEval
      have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
        hOffsetEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hValueEval.symm
      -- Get the modulus bound on valueNat for runtimeStateMatchesIR_setTransientStorage
      have hValueLt : SourceSemantics.evalExpr fields runtime value < Compiler.Constants.evmModulus :=
        FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hValueLt
      simp at hValueLt
      -- Source execution: tstore updates transientStorage
      let offsetKey := offsetNat % Compiler.Constants.evmModulus
      set runtime' := {
        runtime with
        world := {
          runtime.world with
          transientStorage := fun o =>
            if o = offsetKey then valueNat else runtime.world.transientStorage o
        }
      }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.tstore offset value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc, runtime', offsetKey]
      -- IR execution: tstore updates transientStorage
      set state' := { state with
          transientStorage := fun o => if o = offsetKey then valueNat else state.transientStorage o }
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state', offsetKey]
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion for tstore (same structure as mstore)
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.tstore offset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with ho | hv | hs
        · exact hinScopeOffset n (collectExprNames_mem_exprBoundNames_of_core hcoreOffset n ho)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Bindings: getVar only depends on vars, not transientStorage
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.tstore offset value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope, state', runtime'] using hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.tstore offset value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
        simpa [runtime'] using hbounded
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setTransientStorage hruntime offsetKey valueNat hValueLt
      exact ⟨_, _, hSrcExec, hIRExec,
        hruntime', hexact', hbounded', hscope'⟩

theorem compiledStmtStep_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.tstore offset value)
      [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_tstore_single_preserves
    hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

private theorem compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingUint fieldName key value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingUint fieldName key value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call (fieldStoreBuiltin fields fieldName)
      [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  -- Case split on IR eval results to extract concrete Nat values
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingUint fieldName key value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingUint fieldName key value))
          runtime.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
      · let target := SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyNat)
        set state' := { state with
            transientStorage := fun o =>
              if o = SourceSemantics.wordNormalize target then valueNat else state.transientStorage o }
        set runtime' := { runtime with
            world := SourceSemantics.writeUintKeyedMappingFieldSlots
              fields fieldName runtime.world [slot] keyNat valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMappingUint fieldName key value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeUintKeyedMappingFieldSlots, htrans, target]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          have htargetMod :
              Compiler.Proofs.solidityMappingSlot slot keyNat %
                Compiler.Constants.evmModulus =
              Compiler.Proofs.solidityMappingSlot slot keyNat := by
            exact Nat.mod_eq_of_lt (by
              simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat))
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey, hIRValue,
            fieldStoreBuiltin, htrans, target, state', htargetMod,
            Compiler.Proofs.abstractMappingSlot_eq_solidity,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue state' := by
          simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMappingUint fieldName key value))
            runtime'.bindings state' := by
          exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMappingUint fieldName key value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨by
            simpa [runtime', state', SourceSemantics.writeUintKeyedMappingFieldSlots,
              htrans, target] using
              (runtimeStateMatchesIR_writeTransientTarget
                (target := target) hruntime hvalueLt),
          hexact', hbounded, hscopeRuntime'⟩
      · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
          cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreMappingEntry
                state.storage slot keyNat valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeUintKeyedMappingSlots
              runtime.world [slot] keyNat valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMappingUint fieldName key value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeUintKeyedMappingFieldSlots, htransFalse]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          simp [execIRStmt, evalIRExpr, hIRKey, hIRValue, fieldStoreBuiltin,
            htransFalse, Compiler.Proofs.abstractStoreMappingEntry_eq, state']
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue state' := by
          simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMappingUint fieldName key value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMappingUint fieldName key value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨runtimeStateMatchesIR_writeUintKeyedMappingSlot
            hruntime hresolvedNone hdynNone hvalueLt,
          hexact', hbounded, hscopeRuntime'⟩

theorem compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingUint fieldName key value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

theorem compileExprList_core_ok
    {fields : List Field}
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    ∃ exprIRs, CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs := by
  induction exprs with
  | nil =>
      exact ⟨[], rfl⟩
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
      rcases ih htail with ⟨restIR, hrestIR⟩
      exact ⟨exprIR :: restIR, by
        rw [CompilationModel.compileExprList, hexprIR, hrestIR]
        rfl
      ⟩

theorem compileStmt_emit_scalar_supported_ok
    {fields : List Field}
    {spec : CompilationModel}
    {scope : List String}
    {eventName : String}
    {args : List Expr}
    (hsupport : eventEmissionProofSupported spec.events eventName args = true)
    (hsurface : args.any exprTouchesUnsupportedContractSurface = false) :
    ∃ compiledIR,
      CompilationModel.compileStmt fields spec.events spec.errors .calldata
        [] false scope [] (Stmt.emit eventName args) = Except.ok compiledIR := by
  have hcore : ∀ expr ∈ args, FunctionBody.ExprCompileCore expr := by
    intro expr hmem
    have hnotTrue :
        ¬ exprTouchesUnsupportedContractSurface expr = true :=
      (List.any_eq_false.mp hsurface) expr hmem
    have hclosed : exprTouchesUnsupportedContractSurface expr = false := by
      cases h : exprTouchesUnsupportedContractSurface expr <;> simp [h] at hnotTrue ⊢
    exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
      hclosed
  rcases compileExprList_core_ok (fields := fields) hcore with
    ⟨argExprs, hargExprs⟩
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨eventDef, hfind, hscalar, hlen⟩
  have hindexed :
      ¬ (eventIndexedArgs (eventZippedWithSource eventDef args argExprs)).length > 3 := by
    exact Nat.not_lt.mpr
      (eventEmissionProofSupported_eventIndexedArgs_length_le_three
        argExprs hsupport hfind)
  have hindexedGuard :
      ¬ 3 < (eventIndexedArgs (eventZippedWithSource eventDef args argExprs)).length := by
    simpa [GT.gt] using hindexed
  have hscalarCompile :
      eventDefScalarCompileSupported eventDef = true := by
    simpa [eventDefScalarProofSupported] using hscalar
  refine ⟨compileScalarEmitFromCompiledArgs eventDef args argExprs, ?_⟩
  simp only [CompilationModel.compileStmt, CompilationModel.compileEmit]
  simp [hfind, hlen, hargExprs, hindexedGuard, hscalarCompile,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Fill the event-head compile obligation from the scalar `.emit` compile
shape theorem, leaving only the semantic source/IR bridge as proof input. -/
theorem eventHeadStepBridgeCatalog_of_semanticBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    (hsemantic :
      EventHeadStepSemanticBridgeCatalog runtimeContract spec fields) :
    EventHeadStepBridgeCatalog runtimeContract spec fields := by
  refine ⟨?_, ?_⟩
  · intro scope eventName args hsupport hsurface
    exact compileStmt_emit_scalar_supported_ok
      (fields := fields)
      (spec := spec)
      (scope := scope)
      (eventName := eventName)
      (args := args)
      hsupport
      hsurface
  · intro scope eventName args compiledIR hsupport hsurface hcompile hinScope hfresh hinternal
      runtime state helperFuel extraFuel hfuel hbindings hpresent hbounded hmatch
      hfuelIR
    exact hsemantic.bridge
      (scope := scope)
      (eventName := eventName)
      (args := args)
      (compiledIR := compiledIR)
      hsupport
      hsurface
      hcompile
      hinScope
      hfresh
      hinternal
      runtime
      state
      helperFuel
      extraFuel
      hfuel
      hbindings
      hpresent
      hbounded
      hmatch
      hfuelIR

theorem eval_compileExpr_core_some_of_scope
    {fields : List Field}
    {scope : List String}
    {expr : Expr}
    {exprIR : YulExpr}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hcompiled : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    ∃ value,
      SourceSemantics.evalExpr fields runtime expr = some value ∧
      evalIRExpr state exprIR = some value := by
  have hpresent : FunctionBody.exprBoundNamesPresent expr runtime.bindings :=
    FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
  have heval :
      evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr) := by
    have h :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded hpresent hruntime
    simpa [hcompiled] using h
  rcases he : SourceSemantics.evalExpr fields runtime expr with _ | value
  · cases hIR : evalIRExpr state exprIR <;> simp [hIR, he] at heval
  · have hIRsome : evalIRExpr state exprIR = some value := by
      cases hIR : evalIRExpr state exprIR with
      | none =>
          simp [hIR, he] at heval
      | some actual =>
          simp [hIR, he] at heval
          subst heval
          exact rfl
    exact ⟨value, rfl, hIRsome⟩

theorem eval_compileExprList_core_of_scope
    {fields : List Field}
    {scope : List String}
    {exprs : List Expr}
    {exprIRs : List YulExpr}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : ∀ expr ∈ exprs, FunctionBody.exprBoundNamesInScope expr scope)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hcompiled : CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs) :
    ∃ values,
      SourceSemantics.evalExprList fields runtime exprs = some values ∧
      List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) exprIRs values := by
  induction exprs generalizing exprIRs with
  | nil =>
      simp [CompilationModel.compileExprList] at hcompiled
      cases hcompiled
      exact ⟨[], rfl, .nil⟩
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail :
          ∀ expr' ∈ rest, FunctionBody.ExprCompileCore expr' := by
        intro expr' hexpr'
        exact hcore expr' (by simp [hexpr'])
      have htailScope :
          ∀ expr' ∈ rest, FunctionBody.exprBoundNamesInScope expr' scope := by
        intro expr' hexpr'
        exact hinScope expr' (by simp [hexpr'])
      rcases compileExprList_core_ok (fields := fields) htail with ⟨restIRs, hrestIRs⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
      rw [CompilationModel.compileExprList, hexprIR, hrestIRs] at hcompiled
      injection hcompiled with hcompiledTail
      subst hcompiledTail
      rcases eval_compileExpr_core_some_of_scope
          (expr := expr) (exprIR := exprIR) hhead hexact (hinScope expr (by simp))
          hbounded hscope hruntime hexprIR with
        ⟨headVal, hheadVal, hheadEval⟩
      rcases ih htail htailScope hrestIRs with
        ⟨restVals, hrestVals, hrestEval⟩
      refine ⟨headVal :: restVals, ?_, ?_⟩
      · simp [SourceSemantics.evalExprList, hheadVal, hrestVals]
      · exact .cons hheadEval hrestEval

private theorem evalIRExpr_mappingSlotChain
    {state : IRState}
    {baseSlot : Nat}
    {keyIRs : List YulExpr}
    {keyVals : List Nat}
    (hkeys : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) keyIRs keyVals) :
    evalIRExpr state
      (keyIRs.foldl
        (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
        (YulExpr.lit baseSlot)) =
      some (SourceSemantics.mappingSlotChain baseSlot keyVals) := by
  have hgeneral :
      ∀ {startExpr : YulExpr} {startSlot : Nat},
        evalIRExpr state startExpr = some startSlot →
        evalIRExpr state
            (keyIRs.foldl
              (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
              startExpr) =
          some (List.foldl Compiler.Proofs.abstractMappingSlot startSlot keyVals) := by
    induction hkeys with
    | nil =>
        intro startExpr startSlot hstart
        simpa using hstart
    | @cons exprIR value keyIRs keyVals hexpr hrest ih =>
        intro startExpr startSlot hstart
        have hnext :
            evalIRExpr state (YulExpr.call "mappingSlot" [startExpr, exprIR]) =
              some (Compiler.Proofs.abstractMappingSlot startSlot value) := by
          simp [evalIRExpr, evalIRCall, evalIRExprs, hstart, hexpr,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
        simpa [List.foldl] using
          ih (startExpr := YulExpr.call "mappingSlot" [startExpr, exprIR])
            (startSlot := Compiler.Proofs.abstractMappingSlot startSlot value) hnext
  simpa [SourceSemantics.mappingSlotChain] using
    hgeneral (startExpr := YulExpr.lit baseSlot) (startSlot := baseSlot) (by simp [evalIRExpr])

private theorem execIRStmt_sstore_of_eval
    {state : IRState}
    {slotExpr valueExpr : Compiler.Yul.YulExpr}
    {slotVal valueVal : Nat}
    {fuel : Nat}
    (hslot : evalIRExpr state slotExpr = some slotVal)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
        [slotExpr, valueExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
          slotVal valueVal } := by
  cases slotExpr with
  | lit n => simp [execIRStmt, evalIRExpr, hvalue, hslot]
  | hex n => simp [execIRStmt, evalIRExpr, hvalue, hslot]
  | str s => simp [evalIRExpr] at hslot
  | ident name => simp [execIRStmt, hslot, hvalue]
  | call fname args =>
    cases args with
    | nil => simp [execIRStmt, hslot, hvalue]
    | cons arg rest =>
      cases rest with
      | nil => simp [execIRStmt, hslot, hvalue]
      | cons arg2 rest =>
        cases rest with
        | nil =>
          by_cases hfunc : fname = "mappingSlot"
          · subst hfunc
            simp only [evalIRExpr, evalIRCall, evalIRExprs,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean] at hslot
            cases hb : evalIRExpr state arg with
            | none => simp [hb] at hslot
            | some bv =>
              cases hk : evalIRExpr state arg2 with
              | none => simp [hb, hk] at hslot
              | some kv =>
                simp [hb, hk] at hslot
                simp [execIRStmt, hb, hk, hvalue,
                  Compiler.Proofs.abstractStoreMappingEntry_eq,
                  Compiler.Proofs.abstractStoreStorageOrMapping_eq,
                  Compiler.Proofs.abstractMappingSlot_eq_solidity, ← hslot]
          · simp [execIRStmt, hslot, hvalue, hfunc]
        | cons arg3 rest => simp [execIRStmt, hslot, hvalue]

private theorem execIRStmt_tstore_of_eval
    {state : IRState}
    {slotExpr valueExpr : Compiler.Yul.YulExpr}
    {slotVal valueVal : Nat}
    {fuel : Nat}
    (hslot : evalIRExpr state slotExpr = some slotVal)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "tstore"
        [slotExpr, valueExpr])) =
      .continue { state with
        transientStorage := fun slot =>
          if slot = slotVal % Compiler.Constants.evmModulus then valueVal
          else state.transientStorage slot } := by
    simp [execIRStmt, hslot, hvalue]

private theorem evalIRExpr_mappingWordTarget_of_eval
    {state : IRState} {slot keyNat wordOffset : Nat} {keyIR : YulExpr}
    (hkey : evalIRExpr state keyIR = some keyNat) :
    evalIRExpr state
      (let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
       if wordOffset == 0 then mappingBase
       else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]) =
      some (mappingWordTargetSlot slot keyNat wordOffset) := by
  have hMappingBaseEval :
      evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
        some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
    simpa using
      (evalIRExpr_mappingSlotChain
        (state := state)
        (baseSlot := slot)
        (keyIRs := [keyIR])
        (keyVals := [keyNat])
        (by simp [hkey] : List.Forall₂
          (fun exprIR value => evalIRExpr state exprIR = some value)
          [keyIR] [keyNat]))
  by_cases hzero : wordOffset = 0
  · subst hzero
    have hlt :
        Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
      simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
        (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
    simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot,
      SourceSemantics.wordNormalize, Compiler.Proofs.abstractMappingSlot_eq_solidity,
      Nat.mod_eq_of_lt hlt] using hMappingBaseEval
  · have hAddEval :=
      FunctionBody.evalIRExpr_add_of_eval
        (state := state)
        (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
        (rhs := YulExpr.lit wordOffset)
        (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
        (b := wordOffset)
        hMappingBaseEval
        (by simp [evalIRExpr])
    have hAddEval' :
        evalIRExpr state
          (YulExpr.call "add"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
          some ((Verity.Core.Uint256.ofNat wordOffset +
            Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
      rw [uint256_add_val_eq_mod]
      simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAddEval
    simpa [hzero, mappingWordTargetSlot_eq_uint256_add] using hAddEval'

private theorem evalIRExpr_mappingSlot2_of_eval
    {state : IRState} {slot key1Nat key2Nat : Nat}
    {key1IR key2IR : YulExpr}
    (hkey1 : evalIRExpr state key1IR = some key1Nat)
    (hkey2 : evalIRExpr state key2IR = some key2Nat) :
    evalIRExpr state
      (YulExpr.call "mappingSlot"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR]) =
      some (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat) := by
  simpa using
    (evalIRExpr_mappingSlotChain
      (state := state)
      (baseSlot := slot)
      (keyIRs := [key1IR, key2IR])
      (keyVals := [key1Nat, key2Nat])
      (by simp [hkey1, hkey2] : List.Forall₂
        (fun exprIR value => evalIRExpr state exprIR = some value)
        [key1IR, key2IR] [key1Nat, key2Nat]))

private theorem evalIRExpr_mappingSlot2_add_of_eval
    {state : IRState} {slot key1Nat key2Nat wordOffset : Nat}
    {key1IR key2IR : YulExpr}
    (hMappingSlot2Eval :
      evalIRExpr state
        (YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR]) =
      some (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)) :
    evalIRExpr state
      (YulExpr.call "add"
        [YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR],
         YulExpr.lit wordOffset]) =
      some ((Verity.Core.Uint256.ofNat wordOffset +
        Verity.Core.Uint256.ofNat
          (Compiler.Proofs.solidityMappingSlot
            (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val) := by
  have hAddEval :=
    FunctionBody.evalIRExpr_add_of_eval
      (state := state)
      (lhs := YulExpr.call "mappingSlot"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR])
      (rhs := YulExpr.lit wordOffset)
      (a := Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
      (b := wordOffset)
      hMappingSlot2Eval
      (by simp [evalIRExpr])
  rw [uint256_add_val_eq_mod]
  simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hAddEval

private theorem evalIRExpr_mapping2WordTarget_of_eval
    {state : IRState} {slot key1Nat key2Nat wordOffset : Nat}
    {key1IR key2IR : YulExpr}
    (hkey1 : evalIRExpr state key1IR = some key1Nat)
    (hkey2 : evalIRExpr state key2IR = some key2Nat) :
    evalIRExpr state
      (let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
       let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
       if wordOffset == 0 then mappingSlot2
       else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset]) =
      some (mapping2WordTargetSlot slot key1Nat key2Nat wordOffset) := by
  have hMappingSlot2Eval :
      evalIRExpr state
        (YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR]) =
      some (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat) :=
    evalIRExpr_mappingSlot2_of_eval hkey1 hkey2
  by_cases hzero : wordOffset = 0
  · subst hzero
    have hlt :
        Compiler.Proofs.solidityMappingSlot
          (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat <
          Compiler.Constants.evmModulus := by
      simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
        (Compiler.Proofs.abstractMappingSlot_lt_evmModulus
          (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
    simpa [mapping2WordTargetSlot, SourceSemantics.wordNormalize,
      Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.mod_eq_of_lt hlt] using
      hMappingSlot2Eval
  · have hAddEval' :=
      evalIRExpr_mappingSlot2_add_of_eval
        (wordOffset := wordOffset)
        hMappingSlot2Eval
    simpa [hzero, mapping2WordTargetSlot_eq_uint256_add] using hAddEval'

private theorem execIRStmt_sstore_foldl_mappingSlot
    {state : IRState}
    {baseSlot : Nat}
    {keyIRs : List Compiler.Yul.YulExpr}
    {keyVals : List Nat}
    {valueExpr : Compiler.Yul.YulExpr}
    {valueVal : Nat}
    {fuel : Nat}
    (hkeys : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) keyIRs keyVals)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
        [keyIRs.foldl
          (fun slotExpr keyExpr => Compiler.Yul.YulExpr.call "mappingSlot" [slotExpr, keyExpr])
          (Compiler.Yul.YulExpr.lit baseSlot), valueExpr])) =
        .continue { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
            (SourceSemantics.mappingSlotChain baseSlot keyVals) valueVal } := by
  suffices h : ∀ (startExpr : Compiler.Yul.YulExpr) (startSlot : Nat)
      (kIRs : List Compiler.Yul.YulExpr) (kVals : List Nat),
      List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) kIRs kVals →
      evalIRExpr state startExpr = some startSlot →
      execIRStmt (Nat.succ fuel) state
        (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
          [kIRs.foldl
            (fun slotExpr keyExpr => Compiler.Yul.YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            startExpr, valueExpr])) =
        .continue { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
            (kVals.foldl Compiler.Proofs.abstractMappingSlot startSlot) valueVal } by
    simpa [SourceSemantics.mappingSlotChain] using
      h (Compiler.Yul.YulExpr.lit baseSlot) baseSlot keyIRs keyVals hkeys (by simp [evalIRExpr])
  intro startExpr startSlot kIRs kVals hf hstart
  induction hf generalizing startExpr startSlot with
  | nil =>
    simp only [List.foldl]
    exact execIRStmt_sstore_of_eval hstart hvalue
  | @cons exprIR keyVal kIRs' kVals' hexpr _ ih =>
    simp only [List.foldl]
    have hnext : evalIRExpr state
        (Compiler.Yul.YulExpr.call "mappingSlot" [startExpr, exprIR]) =
          some (Compiler.Proofs.abstractMappingSlot startSlot keyVal) := by
      simp [evalIRExpr, evalIRCall, evalIRExprs, hstart, hexpr,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
    exact ih (Compiler.Yul.YulExpr.call "mappingSlot" [startExpr, exprIR])
      (Compiler.Proofs.abstractMappingSlot startSlot keyVal) hnext

private theorem compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    {keyIRs : List YulExpr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
    (hkeyIRs : CompilationModel.compileExprList fields .calldata keys = Except.ok keyIRs)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [keyIRs.foldl
              (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
              (YulExpr.lit slot), valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingChain fieldName keys value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [keyIRs.foldl
                  (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
                  (YulExpr.lit slot), valueIR])].length + extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [keyIRs.foldl
                  (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
                  (YulExpr.lit slot), valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let writeSlotExpr :=
    keyIRs.foldl
      (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
      (YulExpr.lit slot)
  let compiledIR := [YulStmt.expr
    (YulExpr.call (fieldStoreBuiltin fields fieldName) [writeSlotExpr, valueIR])]
  -- Evaluate value expression
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hvalueSourceEval
  rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
  · simp [hIRValue, Option.bind] at hvalueSourceEval
  · simp [hIRValue, Option.bind] at hvalueSourceEval
    have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
      hvalueSourceEval.symm
    -- Evaluate key list expressions
    rcases eval_compileExprList_core_of_scope
        hcoreKeys hexact hinScopeKeys hbounded hscope hruntime hkeyIRs with
      ⟨resolvedKeys, hkeysEval, hkeyIRVals⟩
    -- Slot safety
    rcases hslotSafety runtime resolvedKeys hkeysEval with
      ⟨hresolvedNone, hdynNone⟩
    -- Compute the foldl slot expression
    have hWriteSlotEval :
        evalIRExpr state writeSlotExpr =
          some (SourceSemantics.mappingSlotChain slot resolvedKeys) :=
      evalIRExpr_mappingSlotChain hkeyIRVals
    -- Value boundedness
    have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
        hcoreValue hexact hinScopeValue hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
        hruntime
    rw [hValueSrc] at hvalueLt
    simp at hvalueLt
    -- Scope inclusion
    have hincl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.setMappingChain fieldName keys value)) scope := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with hk | hv | hs
      · -- name from collectExprListNames keys — prove ∃ expr ∈ keys with name ∈ collectExprNames expr
        suffices ∀ (ks : List Expr),
            (∀ e, e ∈ ks → FunctionBody.ExprCompileCore e) →
            (∀ e, e ∈ ks → FunctionBody.exprBoundNamesInScope e scope) →
            n ∈ collectExprListNames ks → n ∈ scope from
          this keys hcoreKeys hinScopeKeys hk
        intro ks hcore' hscope' hmem
        induction ks with
        | nil => simp [collectExprListNames] at hmem
        | cons hd tl ih =>
          simp [collectExprListNames] at hmem
          rcases hmem with hhd | htl
          · exact hscope' hd (by simp) n
              (collectExprNames_mem_exprBoundNames_of_core (hcore' hd (by simp)) n hhd)
          · exact ih (fun e he => hcore' e (by simp [he]))
              (fun e he => hscope' e (by simp [he])) htl
      · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
      · exact hs
    have hscope' : FunctionBody.scopeNamesPresent
        (stmtNextScope scope (.setMappingChain fieldName keys value))
        runtime.bindings :=
      FunctionBody.scopeNamesPresent_of_included hscope hincl
    by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
    · let target := SourceSemantics.wordNormalize
        (SourceSemantics.mappingSlotChain slot resolvedKeys)
      set state' := { state with
          transientStorage := fun o =>
            if o = target then valueNat else state.transientStorage o }
      set runtime' := { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainFieldSlots
            fields fieldName runtime.world [slot] resolvedKeys valueNat }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingChain fieldName keys value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hkeysEval, hValueSrc, runtime',
          SourceSemantics.writeAddressKeyedMappingChainFieldSlots, htrans, target,
          SourceSemantics.mappingSlotChain]
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName) [writeSlotExpr, valueIR])) =
              .continue state' := by
        have h := execIRStmt_tstore_of_eval
          (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
          (fuel := extraFuel) hWriteSlotEval hIRValue
        simpa [fieldStoreBuiltin, htrans, state', target, SourceSemantics.wordNormalize,
          SourceSemantics.mappingSlotChain] using h
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          runtime'.bindings state' := by
        exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
          hincl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
        simpa [runtime'] using hbounded
      have hscopeRuntime' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          runtime'.bindings := by
        simpa [runtime'] using hscope'
      refine ⟨_, _, hSrcExec, hIRExec, ?_⟩
      exact ⟨by
          simpa [runtime', state', SourceSemantics.writeAddressKeyedMappingChainFieldSlots,
            htrans, target, SourceSemantics.mappingSlotChain] using
            (runtimeStateMatchesIR_writeTransientTarget
              (target := target) hruntime hvalueLt),
        hexact', hbounded', hscopeRuntime'⟩
    · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
        cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreStorageOrMapping
              state.storage
              (SourceSemantics.mappingSlotChain slot resolvedKeys)
              valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainSlots
            runtime.world [slot] resolvedKeys valueNat }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingChain fieldName keys value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hkeysEval, hValueSrc, runtime',
          SourceSemantics.writeAddressKeyedMappingChainFieldSlots, htransFalse]
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName) [writeSlotExpr, valueIR])) =
              .continue state' := by
        simpa [fieldStoreBuiltin, htransFalse, state'] using
          (execIRStmt_sstore_foldl_mappingSlot
            (state := state) (baseSlot := slot) (keyIRs := keyIRs)
            (keyVals := resolvedKeys) (valueExpr := valueIR)
            (valueVal := valueNat) (fuel := extraFuel) hkeyIRVals hIRValue)
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
          hincl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
        simpa [runtime'] using hbounded
      have hscopeRuntime' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          runtime'.bindings := by
        simpa [runtime'] using hscope'
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot
          hruntime hresolvedNone hdynNone hvalueLt
      exact ⟨_, _, hSrcExec, hIRExec,
        hruntime', hexact', hbounded', hscopeRuntime'⟩

theorem compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    {keyIRs : List YulExpr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
    (hkeyIRs : CompilationModel.compileExprList fields .calldata keys = Except.ok keyIRs)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingChain fieldName keys value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetMappingChain,
      hmapping, hwriteSlots, hkeyIRs, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves
    hcoreKeys hinScopeKeys hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIRs hvalueIR

private theorem compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping fieldName key value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping fieldName key value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call (fieldStoreBuiltin fields fieldName)
      [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  -- Case split on IR eval results to extract concrete Nat values
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMapping fieldName key value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMapping fieldName key value))
          runtime.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
      · let target := SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyNat)
        set state' := { state with
            transientStorage := fun o =>
              if o = SourceSemantics.wordNormalize target then valueNat else state.transientStorage o }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMappingFieldSlots
              fields fieldName runtime.world [slot] keyNat valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMapping fieldName key value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeAddressKeyedMappingFieldSlots, htrans, target]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          have htargetMod :
              Compiler.Proofs.solidityMappingSlot slot keyNat %
                Compiler.Constants.evmModulus =
              Compiler.Proofs.solidityMappingSlot slot keyNat := by
            exact Nat.mod_eq_of_lt (by
              simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat))
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey, hIRValue,
            fieldStoreBuiltin, htrans, target, state', htargetMod,
            Compiler.Proofs.abstractMappingSlot_eq_solidity,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue state' := by
          simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMapping fieldName key value))
            runtime'.bindings state' := by
          exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping fieldName key value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨by
            simpa [runtime', state', SourceSemantics.writeAddressKeyedMappingFieldSlots,
              htrans, target] using
              (runtimeStateMatchesIR_writeTransientTarget
                (target := target) hruntime hvalueLt),
          hexact', hbounded, hscopeRuntime'⟩
      · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
          cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreMappingEntry
                state.storage slot keyNat valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMappingSlots
              runtime.world [slot] keyNat valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMapping fieldName key value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeAddressKeyedMappingFieldSlots, htransFalse]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          simp [execIRStmt, evalIRExpr, hIRKey, hIRValue, fieldStoreBuiltin,
            htransFalse, Compiler.Proofs.abstractStoreMappingEntry_eq, state']
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue state' := by
          simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMapping fieldName key value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping fieldName key value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingSlot
            hruntime hresolvedNone hdynNone hvalueLt,
          hexact', hbounded, hscopeRuntime'⟩

theorem compiledStmtStep_setMapping_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping fieldName key value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

private theorem compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
             if wordOffset == 0 then mappingBase
             else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] -
          [YulStmt.expr
            (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingWord fieldName key wordOffset value) = sourceResult ∧
        execIRStmts
              ([YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                   if wordOffset == 0 then mappingBase
                   else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
              [YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                   if wordOffset == 0 then mappingBase
                   else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      set targetSlot := mappingWordTargetSlot slot keyNat wordOffset
      let writeSlotExpr :=
        let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
        if wordOffset == 0 then mappingBase
        else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
      have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
        simpa [writeSlotExpr, targetSlot] using
          (evalIRExpr_mappingWordTarget_of_eval
            (state := state) (slot := slot) (wordOffset := wordOffset) hIRKey)
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hTargetMod :
          (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
            Compiler.Constants.evmModulus = targetSlot := by
        rw [show targetSlot =
          (Verity.Core.Uint256.ofNat wordOffset +
            Verity.Core.Uint256.ofNat
              (Compiler.Proofs.solidityMappingSlot slot keyNat)).val by
            simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset]
        simpa [Nat.add_comm] using
          (uint256_add_val_eq_mod wordOffset
            (Compiler.Proofs.solidityMappingSlot slot keyNat)).symm
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
          runtime.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
      · let target :=
          (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
            Compiler.Constants.evmModulus
        set state' := { state with
            transientStorage := fun o =>
              if o = SourceSemantics.wordNormalize target then valueNat else state.transientStorage o }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMappingWordFieldSlots
              fields fieldName runtime.world [slot] keyNat wordOffset valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMappingWord fieldName key wordOffset value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeAddressKeyedMappingWordFieldSlots,
            SourceSemantics.writeMappingTargets, htrans, target, targetSlot, hTargetMod]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [writeSlotExpr, valueIR])) = .continue state' := by
            simpa [fieldStoreBuiltin, htrans, state', target, hTargetMod] using
            (execIRStmt_tstore_of_eval
              (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
              (slotVal := targetSlot) (valueVal := valueNat) (fuel := extraFuel)
              hWriteSlotEval hIRValue)
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName) [writeSlotExpr, valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
            runtime'.bindings state' := by
          exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, ?_, ?_⟩
        · simpa [writeSlotExpr] using hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨by
                simpa [runtime', state', SourceSemantics.writeAddressKeyedMappingWordFieldSlots,
                  SourceSemantics.writeMappingTargets, htrans, target, targetSlot, hTargetMod] using
                (runtimeStateMatchesIR_writeTransientTarget
                  (target := target) hruntime hvalueLt),
            hexact', hbounded, hscopeRuntime'⟩
      · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
          cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
        have htargetSlotNorm :
            targetSlot % Compiler.Constants.evmModulus = targetSlot := by
          exact Nat.mod_eq_of_lt (SourceSemantics.wordNormalize_lt_evmModulus _)
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage targetSlot valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMappingWordSlots
              runtime.world [slot] keyNat wordOffset valueNat }
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMappingWord fieldName key wordOffset value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime',
            SourceSemantics.writeAddressKeyedMappingWordFieldSlots,
            SourceSemantics.writeMappingTargets, SourceSemantics.writeAddressKeyedMappingWordSlots,
            htransFalse, hTargetMod, htargetSlotNorm]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [writeSlotExpr, valueIR])) = .continue state' := by
          simpa [fieldStoreBuiltin, htransFalse, state'] using
            (execIRStmt_sstore_of_eval
              (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
              (slotVal := targetSlot) (valueVal := valueNat) (fuel := extraFuel)
              hWriteSlotEval hIRValue)
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName) [writeSlotExpr, valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
            hincl
        have hscopeRuntime' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
            runtime'.bindings := by
          simpa [runtime'] using hscope'
        refine ⟨.continue runtime', .continue state', hSrcExec, ?_, ?_⟩
        · simpa [writeSlotExpr] using hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscopeRuntime'⟩

theorem compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingWord fieldName key wordOffset value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

private theorem uint256_and_val_eq_land_mod (a b : Nat) :
    (Verity.Core.Uint256.and a b).val =
      ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  simp only [Verity.Core.Uint256.and, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
  have hlt : Nat.land (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) <
      Compiler.Constants.evmModulus := by
    have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
      exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
    have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
      exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    exact Nat.and_lt_two_pow (a % Compiler.Constants.evmModulus)
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using hb)
  exact Nat.mod_eq_of_lt hlt

private theorem uint256_or_val_eq_lor_mod (a b : Nat) :
    (Verity.Core.Uint256.or a b).val =
      ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  simp only [Verity.Core.Uint256.or, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have hlt : Nat.lor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) <
      Compiler.Constants.evmModulus := by
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    exact Nat.or_lt_two_pow
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using ha)
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using hb)
  exact Nat.mod_eq_of_lt hlt

private theorem uint256_not_val_eq_xor_allOnes_mod (a : Nat) :
    (Verity.Core.Uint256.not a).val =
      Nat.xor (a % Compiler.Constants.evmModulus) (Compiler.Constants.evmModulus - 1) := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have ha256 : a % Compiler.Constants.evmModulus < 2 ^ 256 := by
    simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using ha
  have hxor_eq : Nat.xor (a % Compiler.Constants.evmModulus) (2 ^ 256 - 1) =
      2 ^ 256 - 1 - (a % Compiler.Constants.evmModulus) := by
    have key :
        (BitVec.ofNat 256 (a % Compiler.Constants.evmModulus) ^^^ BitVec.allOnes 256).toNat =
          2 ^ 256 - 1 - (a % Compiler.Constants.evmModulus) := by
      rw [BitVec.xor_allOnes]
      simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha256]
    have lhs_eq :
        Nat.xor (a % Compiler.Constants.evmModulus) (2 ^ 256 - 1) =
          (BitVec.ofNat 256 (a % Compiler.Constants.evmModulus) ^^^ BitVec.allOnes 256).toNat := by
      simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha256, BitVec.toNat_allOnes]
      rfl
    rw [lhs_eq, key]
  rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
  simp only [Verity.Core.Uint256.not, Verity.Core.Uint256.val_ofNat, Verity.Core.MAX_UINT256,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  rw [hxor_eq, Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 - (a % 2 ^ 256) < 2 ^ 256)]

private theorem uint256_shl_val_eq_mul_pow_mod
    (shift value : Nat)
    (hshift : shift < 256) :
    (Verity.Core.Uint256.shl shift value).val =
      ((value % Compiler.Constants.evmModulus) * 2 ^ shift) % Compiler.Constants.evmModulus := by
  have hshiftLt : shift < Compiler.Constants.evmModulus := by
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    omega
  simp only [Verity.Core.Uint256.shl, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt hshiftLt]
  rw [Nat.shiftLeft_eq]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.block
        [ YulStmt.let_ "__compat_value" valueIR
        , YulStmt.let_ "__compat_packed"
            (YulExpr.call "and" [YulExpr.ident "__compat_value",
              YulExpr.lit (packedMaskNat packed)])
        , YulStmt.let_ "__compat_slot_word"
            (YulExpr.call (fieldLoadBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
        , YulStmt.let_ "__compat_slot_cleared"
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
        , YulStmt.expr
            (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
               YulExpr.call "or"
                 [YulExpr.ident "__compat_slot_cleared",
                   YulExpr.call "shl"
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] -
        [YulStmt.block
          [ YulStmt.let_ "__compat_value" valueIR
          , YulStmt.let_ "__compat_packed"
              (YulExpr.call "and" [YulExpr.ident "__compat_value",
                YulExpr.lit (packedMaskNat packed)])
          , YulStmt.let_ "__compat_slot_word"
              (YulExpr.call (fieldLoadBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
          , YulStmt.let_ "__compat_slot_cleared"
              (YulExpr.call "and"
                [YulExpr.ident "__compat_slot_word",
                  YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
          , YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                 YulExpr.call "or"
                   [YulExpr.ident "__compat_slot_cleared",
                     YulExpr.call "shl"
                       [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime
          (.setMappingPackedWord fieldName key wordOffset packed value) = sourceResult ∧
        execIRStmts
            ([YulStmt.block
              [ YulStmt.let_ "__compat_value" valueIR
              , YulStmt.let_ "__compat_packed"
                  (YulExpr.call "and" [YulExpr.ident "__compat_value",
                    YulExpr.lit (packedMaskNat packed)])
              , YulStmt.let_ "__compat_slot_word"
                  (YulExpr.call (fieldLoadBuiltin fields fieldName)
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
              , YulStmt.let_ "__compat_slot_cleared"
                  (YulExpr.call "and"
                    [YulExpr.ident "__compat_slot_word",
                      YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
              , YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                     YulExpr.call "or"
                       [YulExpr.ident "__compat_slot_cleared",
                         YulExpr.call "shl"
                           [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]].length +
              extraFuel + 1)
            state
            [YulStmt.block
              [ YulStmt.let_ "__compat_value" valueIR
              , YulStmt.let_ "__compat_packed"
                  (YulExpr.call "and" [YulExpr.ident "__compat_value",
                    YulExpr.lit (packedMaskNat packed)])
              , YulStmt.let_ "__compat_slot_word"
                  (YulExpr.call (fieldLoadBuiltin fields fieldName)
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
              , YulStmt.let_ "__compat_slot_cleared"
                  (YulExpr.call "and"
                    [YulExpr.ident "__compat_slot_word",
                      YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
              , YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                     YulExpr.call "or"
                       [YulExpr.ident "__compat_slot_cleared",
                         YulExpr.call "shl"
                           [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let writeSlotExpr :=
    let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
    if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
  let blockBody :=
    [ YulStmt.let_ "__compat_value" valueIR
    , YulStmt.let_ "__compat_packed"
        (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])
    , YulStmt.let_ "__compat_slot_word" (YulExpr.call (fieldLoadBuiltin fields fieldName) [writeSlotExpr])
    , YulStmt.let_ "__compat_slot_cleared"
        (YulExpr.call "and"
          [YulExpr.ident "__compat_slot_word",
            YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
    , YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [writeSlotExpr,
            YulExpr.call "or"
              [YulExpr.ident "__compat_slot_cleared",
                YulExpr.call "shl"
                  [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]]) ]
  let compiledIR := [YulStmt.block blockBody]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      set targetSlot := mappingWordTargetSlot slot keyNat wordOffset
      set oldWordNat :=
        if SourceSemantics.fieldIsTransient fields fieldName then
          state.transientStorage (SourceSemantics.wordNormalize targetSlot)
        else
          Compiler.Proofs.IRGeneration.IRStorageWord.toNat
            (state.storage (IRStorageSlot.ofNat targetSlot))
      set storedWordNat := SourceSemantics.packedWordWrite oldWordNat valueNat packed
      have hMappingBaseEval :
          evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKey] : List.Forall₂
              (fun exprIR value => evalIRExpr state exprIR = some value)
              [keyIR] [keyNat]))
      have hpackedOffsetLt : packed.offset < 256 := by
        have hvalid := hpacked
        simp [CompilationModel.packedBitsValid] at hvalid
        omega
      have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      set state1 := state.setVar "__compat_value" valueNat
      have hCompatValue :
          ∀ fuel, execIRStmt (fuel + 1) state (YulStmt.let_ "__compat_value" valueIR) =
            .continue state1 := by
        intro fuel
        simp [state1, execIRStmt, hIRValue]
      have hPackedEval :
          evalIRExpr state1
            (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)]) =
              some (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val := by
        simpa [uint256_and_val_eq_land_mod] using
          FunctionBody.evalIRExpr_and_of_eval
            (state := state1)
            (lhs := YulExpr.ident "__compat_value")
            (rhs := YulExpr.lit (packedMaskNat packed))
            (a := valueNat)
            (b := packedMaskNat packed)
            (by simp [evalIRExpr, state1, IRState.getVar, IRState.setVar])
            (by simp [evalIRExpr])
      set state2 := state1.setVar "__compat_packed" (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val
      have hCompatPacked :
          ∀ fuel, execIRStmt (fuel + 1) state1
            (YulStmt.let_ "__compat_packed"
              (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])) =
            .continue state2 := by
        intro fuel
        simp [state2, execIRStmt, hPackedEval]
      have hexact_state1 :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state1 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (value := valueNat) hexact hcompatValue
      have hexact_state2 :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state2 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hexact_state1 hcompatPacked
      have hruntimeCompat1 : FunctionBody.runtimeStateMatchesIR fields runtime state1 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_value") (value := valueNat) hruntime
      have hruntimeCompat2 : FunctionBody.runtimeStateMatchesIR fields runtime state2 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hruntimeCompat1
      have hIRKeyState2 : evalIRExpr state2 keyIR = some keyNat := by
        have h := FunctionBody.eval_compileExpr_core_of_scope
            hcoreKey hexact_state2 hinScopeKey hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
            hruntimeCompat2
        rw [hkeyIR] at h
        simp [Except.toOption, hKeySrc] at h
        cases h' : evalIRExpr state2 keyIR <;> simp [h'] at h
        simpa using congrArg some h
      have hMappingBaseEval2 :
          evalIRExpr state2 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state2)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKeyState2] : List.Forall₂
              (fun exprIR value => evalIRExpr state2 exprIR = some value)
              [keyIR] [keyNat]))
      have hWriteSlotEval2 : evalIRExpr state2 writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state2 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval2)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state2)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval2
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state2
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      have hSlotWordEval :
          evalIRExpr state2 (YulExpr.call (fieldLoadBuiltin fields fieldName) [writeSlotExpr]) = some oldWordNat := by
        by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
        · simpa [evalIRExpr, evalIRCall, evalIRExprs,
            fieldLoadBuiltin, htrans, oldWordNat, state2, state1,
            SourceSemantics.wordNormalize,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean] using
            congrArg
              (fun r => r.bind (fun a =>
                some (state.transientStorage (a % Compiler.Constants.evmModulus))))
              hWriteSlotEval2
        · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
            cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
          simpa [evalIRExpr, evalIRCall, evalIRExprs,
            fieldLoadBuiltin, htransFalse, oldWordNat, state2, state1,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean] using
            congrArg
              (fun r => r.bind (fun a =>
                some (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
                  (state.storage (IRStorageSlot.ofNat a)))))
              hWriteSlotEval2
      set state3 := state2.setVar "__compat_slot_word" oldWordNat
      have hexact_state3 : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state3 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact_state2 hcompatSlotWord
      have hruntimeCompat3 : FunctionBody.runtimeStateMatchesIR fields runtime state3 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntimeCompat2
      have hCompatSlotWord :
          ∀ fuel, execIRStmt (fuel + 1) state2
            (YulStmt.let_ "__compat_slot_word" (YulExpr.call (fieldLoadBuiltin fields fieldName) [writeSlotExpr])) =
            .continue state3 := by
        intro fuel
        simp [state3, execIRStmt, hSlotWordEval]
      have hSlotClearedEval :
          evalIRExpr state3
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]]) =
              some (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
        have hNotEval :
            evalIRExpr state3
              (YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]) =
                some (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val := by
          simpa [uint256_not_val_eq_xor_allOnes_mod] using
            (FunctionBody.evalIRExpr_not_of_eval
              (state := state3)
              (expr := YulExpr.lit (packedShiftedMaskNat packed))
              (value := packedShiftedMaskNat packed)
              (by simp [evalIRExpr]))
        have hAndEval :=
          FunctionBody.evalIRExpr_and_of_eval
            (state := state3)
            (lhs := YulExpr.ident "__compat_slot_word")
            (rhs := YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)])
            (a := oldWordNat)
            (b := (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val)
            (by simp [evalIRExpr, state3, state2, state1, IRState.getVar, IRState.setVar])
            hNotEval
        have hAndBridge :
            ((oldWordNat % Compiler.Constants.evmModulus) &&&
                ((Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val %
                  Compiler.Constants.evmModulus)) =
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
          have hNotLt :
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).isLt
          have hNotOfNat :
              Verity.Core.Uint256.ofNat ((Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val) =
                Verity.Core.Uint256.not (packedShiftedMaskNat packed) := by
            ext
            simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hNotLt]
          simpa [Nat.mod_eq_of_lt hNotLt, hNotOfNat] using
            (uint256_and_val_eq_land_mod oldWordNat
              ((Verity.Core.Uint256.ofNat (packedShiftedMaskNat packed)).not.val)).symm
        simpa [hAndBridge] using hAndEval
      set state4 := state3.setVar "__compat_slot_cleared"
        (Verity.Core.Uint256.and oldWordNat
          (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val
      have hexact_state4 : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state4 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact_state3 hcompatSlotCleared
      have hruntimeCompat4 : FunctionBody.runtimeStateMatchesIR fields runtime state4 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntimeCompat3
      have hCompatSlotCleared :
          ∀ fuel, execIRStmt (fuel + 1) state3
            (YulStmt.let_ "__compat_slot_cleared"
              (YulExpr.call "and"
                [YulExpr.ident "__compat_slot_word",
                  YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])) =
            .continue state4 := by
        intro fuel
        simp [state4, execIRStmt, hSlotClearedEval]
      have hStoredEval :
          evalIRExpr state4
            (YulExpr.call "or"
              [YulExpr.ident "__compat_slot_cleared",
                YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]) =
              some storedWordNat := by
        have hpackedOffsetLtMod : packed.offset < Compiler.Constants.evmModulus := by
          have hevmmodGt256 : 256 < Compiler.Constants.evmModulus := by
            decide
          exact lt_trans hpackedOffsetLt hevmmodGt256
        have hShlEval :
            evalIRExpr state4
              (YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]) =
                some (Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val := by
          simpa [Nat.mod_eq_of_lt hpackedOffsetLtMod, uint256_shl_val_eq_mul_pow_mod, hpackedOffsetLt] using
            (FunctionBody.evalIRExpr_shl_of_eval
              (state := state4)
              (shiftExpr := YulExpr.lit packed.offset)
              (valueExpr := YulExpr.ident "__compat_packed")
              (shift := packed.offset)
              (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
              (by simp [evalIRExpr])
              (by simp [evalIRExpr, state4, state3, state2, state1, IRState.getVar, IRState.setVar]))
        have hOrEval :=
          FunctionBody.evalIRExpr_or_of_eval
            (state := state4)
            (lhs := YulExpr.ident "__compat_slot_cleared")
            (rhs := YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"])
            (a := (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
            (b := (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val)
            (by simp [evalIRExpr, state4, state3, state2, state1, IRState.getVar, IRState.setVar])
            hShlEval
        have hClearedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.and oldWordNat
                  (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) =
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))) := by
          have hClearedLt :
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hClearedLt]
        have hShiftedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val) =
              (Verity.Core.Uint256.shl packed.offset
                (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) := by
          have hShiftedLt :
              (Verity.Core.Uint256.shl packed.offset
                (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hShiftedLt]
        have hPackedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) =
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)) := by
          have hPackedLt :
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hPackedLt]
        have hClearedLt :
            (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val <
              Compiler.Constants.evmModulus :=
          (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).isLt
        have hShiftedLt :
            (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val <
              Compiler.Constants.evmModulus :=
          (Verity.Core.Uint256.shl packed.offset
            (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).isLt
        have hOrBridge :
            ((((Verity.Core.Uint256.and oldWordNat
                    (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val %
                  Compiler.Constants.evmModulus) |||
                ((Verity.Core.Uint256.shl packed.offset
                      (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val %
                  Compiler.Constants.evmModulus))) =
              (((Verity.Core.Uint256.ofNat
                      ((Verity.Core.Uint256.and oldWordNat
                        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)).or
                  (Verity.Core.Uint256.ofNat
                    ((Verity.Core.Uint256.shl packed.offset
                      (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val))).val) := by
          simpa [uint256_or_val_eq_lor_mod, Nat.mod_eq_of_lt hClearedLt, Nat.mod_eq_of_lt hShiftedLt]
            using
              (uint256_or_val_eq_lor_mod
                ((Verity.Core.Uint256.and oldWordNat
                  (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
                ((Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val)).symm
        rw [hOrBridge] at hOrEval
        rw [hShiftedOfNat] at hOrEval
        simpa [storedWordNat, SourceSemantics.packedWordWrite, hClearedOfNat, hPackedOfNat]
          using hOrEval
      set state' :=
        if SourceSemantics.fieldIsTransient fields fieldName then
          { state4 with
            transientStorage := fun o =>
              if o = SourceSemantics.wordNormalize targetSlot then
                storedWordNat
              else
                state4.transientStorage o }
        else
          { state4 with
            storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot storedWordNat }
      have hIRKeyState4 : evalIRExpr state4 keyIR = some keyNat := by
        have h :=
          FunctionBody.eval_compileExpr_core_of_scope
            hcoreKey hexact_state4 hinScopeKey hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
            hruntimeCompat4
        rw [hkeyIR] at h
        simp [Except.toOption, hKeySrc] at h
        cases h' : evalIRExpr state4 keyIR <;> simp [h'] at h
        simpa using congrArg some h
      have hMappingBaseEval4 :
          evalIRExpr state4 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state4)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKeyState4] : List.Forall₂
              (fun exprIR value => evalIRExpr state4 exprIR = some value)
              [keyIR] [keyNat]))
      have hWriteSlotEval4 : evalIRExpr state4 writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state4 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval4)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state4)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval4
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state4
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      have hSstore :
          ∀ fuel, execIRStmt (fuel + 1) state4
            (YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [writeSlotExpr,
                YulExpr.call "or"
                    [YulExpr.ident "__compat_slot_cleared",
                      YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])) =
            .continue state' := by
        intro fuel
        by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
        · simpa [fieldStoreBuiltin, htrans, state', state4, state3, state2, state1,
            SourceSemantics.wordNormalize] using
            (execIRStmt_tstore_of_eval
              (state := state4)
              (slotExpr := writeSlotExpr)
              (valueExpr := YulExpr.call "or"
                [YulExpr.ident "__compat_slot_cleared",
                  YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]])
              (slotVal := targetSlot)
              (valueVal := storedWordNat)
              (fuel := fuel)
              hWriteSlotEval4
              hStoredEval)
        · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
            cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
          simpa [fieldStoreBuiltin, htransFalse, state', state4, state3, state2, state1] using
            (execIRStmt_sstore_of_eval
              (state := state4)
              (slotExpr := writeSlotExpr)
              (valueExpr := YulExpr.call "or"
                [YulExpr.ident "__compat_slot_cleared",
                  YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]])
              (slotVal := targetSlot)
              (valueVal := storedWordNat)
              (fuel := fuel)
              hWriteSlotEval4
              hStoredEval)
      have hSizeOfListBound : ∀ (l : List YulStmt), l.length + 1 ≤ sizeOf l := by
        intro l
        induction l with
        | nil => simp
        | cons h t ih =>
            show t.length + 1 + 1 ≤ 1 + sizeOf h + sizeOf t
            omega
      have hbodyFuelLe : 6 ≤ extraFuel := by
        have hBodyLen : blockBody.length = 5 := by
          simp [blockBody]
        have hBodyBound := hSizeOfListBound blockBody
        have hBlockSizeOf : 6 ≤ sizeOf [YulStmt.block blockBody] - [YulStmt.block blockBody].length := by
          rw [singletonBlock_sizeOf_slack]
          omega
        exact le_trans hBlockSizeOf hslack
      let bodyExtraFuel := extraFuel - 6
      have hbodyFuelEq : bodyExtraFuel + 6 = extraFuel := by
        dsimp [bodyExtraFuel]
        omega
      have hBody :
          execIRStmts extraFuel state blockBody = .continue state' := by
        rw [← hbodyFuelEq]
        simp [execIRStmts, blockBody, bodyExtraFuel,
          hCompatValue (bodyExtraFuel + 4),
          hCompatPacked (bodyExtraFuel + 3),
          hCompatSlotWord (bodyExtraFuel + 2),
          hCompatSlotCleared (bodyExtraFuel + 1),
          hSstore bodyExtraFuel]
      have hWhole :
          execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = .continue state' := by
        have hblock := execIRStmts_single_block_of_continue
          extraFuel state state' blockBody hBody
        simpa [compiledIR, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hblock
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingPackedWord fieldName key wordOffset packed value) =
            .continue
              { runtime with
                  world := SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
                    fields fieldName runtime.world [slot] keyNat wordOffset packed valueNat } := by
        simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, hpacked,
          SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots]
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hruntime1 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_value") (value := valueNat) hruntime
      have hruntime2 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hruntime1
      have hruntime3 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_slot_word") (value := oldWordNat) hruntime2
      have hruntime4 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_slot_cleared")
          (value := (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
          hruntime3
      have hruntime' :
          FunctionBody.runtimeStateMatchesIR fields
            { runtime with
                world := SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
                  fields fieldName runtime.world [slot] keyNat wordOffset packed valueNat }
            state' := by
        have hstoredLt : storedWordNat < Compiler.Constants.evmModulus := by
          dsimp [storedWordNat, SourceSemantics.packedWordWrite]
          exact ((Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
            (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)))).isLt
        by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
        · have hmatch :
              FunctionBody.runtimeStateMatchesIR fields
                { runtime with
                    world := SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
                      fields fieldName runtime.world [slot] keyNat wordOffset packed valueNat }
                { state4 with
                  transientStorage := fun o =>
                    if o = SourceSemantics.wordNormalize targetSlot then storedWordNat
                    else state4.transientStorage o } := by
            rcases hruntime4 with
              ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain,
                hret, hevents⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · funext query
              rw [hstorage]
              exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
                (SourceSemantics.encodeStorageAt_congr
                  (by simp [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans])
                  (by simp [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans])
                  (by simp [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans]))
            · funext query
              have htargetNorm : SourceSemantics.wordNormalize targetSlot = targetSlot := by
                simpa [targetSlot, mappingWordTargetSlot] using
                  SourceSemantics.wordNormalize_idem
                    (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset)
              by_cases hquery : query = targetSlot
              · subst hquery
                have hTargetMod :
                    (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
                      Compiler.Constants.evmModulus = targetSlot := by
                  rw [show targetSlot =
                    (Verity.Core.Uint256.ofNat wordOffset +
                      Verity.Core.Uint256.ofNat
                        (Compiler.Proofs.solidityMappingSlot slot keyNat)).val by
                      simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset]
                  simpa [Nat.add_comm] using
                    (uint256_add_val_eq_mod wordOffset
                      (Compiler.Proofs.solidityMappingSlot slot keyNat)).symm
                have htargetModSelf : targetSlot % Compiler.Constants.evmModulus = targetSlot := by
                  exact Nat.mod_eq_of_lt (SourceSemantics.wordNormalize_lt_evmModulus _)
                simp [oldWordNat, storedWordNat,
                  SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans,
                  htargetNorm, htargetModSelf, hTargetMod, htransient, Nat.mod_eq_of_lt hstoredLt]
                have hstateTransient :
                    state.transientStorage targetSlot =
                      (runtime.world.transientStorage targetSlot).val := by
                  have hstate4Transient :
                      state4.transientStorage targetSlot =
                        state.transientStorage targetSlot := by
                    simp [state4, state3, state2, state1, IRState.setVar]
                  rw [← hstate4Transient]
                  exact congrFun htransient targetSlot
                rw [hstateTransient]
                exact (Nat.mod_eq_of_lt (by
                  dsimp [SourceSemantics.packedWordWrite]
                  exact ((Verity.Core.Uint256.and (runtime.world.transientStorage targetSlot).val
                      (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
                    (Verity.Core.Uint256.shl packed.offset
                      (Verity.Core.Uint256.and valueNat (packedMaskNat packed)))).isLt)).symm
              · have hbeq : (targetSlot == query) = false := by
                  have hqueryRev : ¬ targetSlot = query := by
                    intro h
                    exact hquery h.symm
                  simp [BEq.beq, hqueryRev]
                have hTargetMod :
                    (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
                      Compiler.Constants.evmModulus = targetSlot := by
                  rw [show targetSlot =
                    (Verity.Core.Uint256.ofNat wordOffset +
                      Verity.Core.Uint256.ofNat
                        (Compiler.Proofs.solidityMappingSlot slot keyNat)).val by
                      simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset]
                  simpa [Nat.add_comm] using
                    (uint256_add_val_eq_mod wordOffset
                      (Compiler.Proofs.solidityMappingSlot slot keyNat)).symm
                have htargetModSelf : targetSlot % Compiler.Constants.evmModulus = targetSlot := by
                  exact Nat.mod_eq_of_lt (SourceSemantics.wordNormalize_lt_evmModulus _)
                have hqueryTarget :
                    ¬ (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
                        Compiler.Constants.evmModulus = query := by
                  have hqueryRev : ¬ targetSlot = query := by
                    intro h
                    exact hquery h.symm
                  simpa [hTargetMod] using hqueryRev
                simp [oldWordNat, storedWordNat,
                  SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans,
                  htargetNorm, htargetModSelf, hquery, hbeq, hqueryTarget, htransient]
                exact congrFun htransient query
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hsender
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hmsgValue
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hthis
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using htimestamp
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hblock
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hchain
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hret
            · simpa [SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htrans] using hevents
          simpa [state', htrans] using hmatch
        · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
            cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
          simpa [state', targetSlot, oldWordNat, storedWordNat,
            SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots, htransFalse] using
            runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
              (runtime := runtime)
              (state := state4)
              (slot := slot) (key := keyNat) (wordOffset := wordOffset) (packed := packed)
              (value := valueNat) hruntime4 hresolvedNone hdynNone
      have hexact1 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_value") (value := valueNat) hexact hcompatValue
      have hexact2 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hexact1 hcompatPacked
      have hexact3 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_slot_word") (value := oldWordNat)
          hexact2 hcompatSlotWord
      have hexact4 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_slot_cleared")
          (value := (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
          hexact3 hcompatSlotCleared
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value))
          runtime.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by
            intro name hname
            by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
            · simpa [IRState.getVar, state', htrans] using hexact4 name hname
            · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
                cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
              simpa [IRState.getVar, state', htransFalse] using hexact4 name hname)
          hincl
      refine ⟨_, _, hSrcExec, hWhole, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨hruntime', hexact', hbounded, hscope'⟩

theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingPackedWord fieldName key wordOffset packed value)
      [YulStmt.block
        [ YulStmt.let_ "__compat_value" valueIR
        , YulStmt.let_ "__compat_packed"
            (YulExpr.call "and" [YulExpr.ident "__compat_value",
              YulExpr.lit (packedMaskNat packed)])
        , YulStmt.let_ "__compat_slot_word"
            (YulExpr.call (fieldLoadBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
        , YulStmt.let_ "__compat_slot_cleared"
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
        , YulStmt.expr
            (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
               YulExpr.call "or"
                 [YulExpr.ident "__compat_slot_cleared",
                   YulExpr.call "shl"
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingPackedSlotWrite,
      hmapping, hpacked, hwriteSlots, hkeyIR, hvalueIR, Bool.not_true, bne_self_eq_false,
      ite_false, ite_true, pure, Except.pure, bind, Except.bind]
    simp [hfind, fieldLoadBuiltin, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue
    hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared
    hpacked hwriteSlots hslotSafety hkeyIR hvalueIR

private theorem compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
             if wordOffset == 0 then mappingBase
             else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setStructMember fieldName key memberName value) =
          sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStructMember fieldName key memberName value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨sourceResult, irExec, hSrcMappingWord, hIRExec, hmatch⟩ :=
    compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
      hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety
      hkeyIR hvalueIR runtime state extraFuel hexact hscope hbounded hruntime hslack
  refine ⟨sourceResult, irExec, ?_, hIRExec, ?_⟩
  · rw [← hSrcMappingWord]
    simp only [SourceSemantics.execStmt, hwriteSlots, hmembers]
    cases SourceSemantics.evalExpr fields runtime key <;>
      cases SourceSemantics.evalExpr fields runtime value <;>
      simp [hmember]
  · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames]
      using hmatch

theorem compiledStmtStep_setStructMember_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hnotMapping2 : isMapping2 fields fieldName = false)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember fieldName key memberName value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetStructMember,
      CompilationModel.compileMappingSlotWrite, hmapping, hnotMapping2, hmembers, hmember,
      hwriteSlots, hkeyIR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hmembers hmember hwriteSlots
    hslotSafety hkeyIR hvalueIR

private theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] -
          [YulStmt.expr
            (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [YulExpr.call "mappingSlot"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping2 fieldName key1 key2 value) = sourceResult ∧
        execIRStmts
              ([YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot"
                    [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])].length +
              extraFuel + 1)
            state
              [YulStmt.expr
                (YulExpr.call (fieldStoreBuiltin fields fieldName)
                  [YulExpr.call "mappingSlot"
                    [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call (fieldStoreBuiltin fields fieldName)
      [YulExpr.call "mappingSlot"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])]
  -- Evaluate key1 expression
  have hkey1SourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey1 hexact hinScopeKey1 hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
      hruntime
  rw [hkey1IR] at hkey1SourceEval
  simp [Except.toOption] at hkey1SourceEval
  rcases hIRKey1 : evalIRExpr state key1IR with _ | key1Nat
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
    -- Evaluate key2 expression
    have hkey2SourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcoreKey2 hexact hinScopeKey2 hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
        hruntime
    rw [hkey2IR] at hkey2SourceEval
    simp [Except.toOption] at hkey2SourceEval
    rcases hIRKey2 : evalIRExpr state key2IR with _ | key2Nat
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
      -- Evaluate value expression
      have hvalueSourceEval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hvalueIR] at hvalueSourceEval
      simp [Except.toOption] at hvalueSourceEval
      rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
      · simp [hIRValue, Option.bind] at hvalueSourceEval
      · simp [hIRValue, Option.bind] at hvalueSourceEval
        have hKey1Src : SourceSemantics.evalExpr fields runtime key1 = some key1Nat :=
          hkey1SourceEval.symm
        have hKey2Src : SourceSemantics.evalExpr fields runtime key2 = some key2Nat :=
          hkey2SourceEval.symm
        have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          hvalueSourceEval.symm
        rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
        -- Get boundedness of valueNat
        have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
            hcoreValue hexact hinScopeValue hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
            hruntime
        rw [hValueSrc] at hvalueLt
        simp at hvalueLt
        -- Scope inclusion
        have hincl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.setMapping2 fieldName key1 key2 value)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hk1 | hk2 | hv | hs
          · exact hinScopeKey1 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey1 n hk1)
          · exact hinScopeKey2 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey2 n hk2)
          · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
          · exact hs
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
            runtime.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hincl
        by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
        · let target := SourceSemantics.wordNormalize
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
          set state' := { state with
              transientStorage := fun o =>
                if o = SourceSemantics.wordNormalize target then valueNat else state.transientStorage o }
          set runtime' := { runtime with
              world := SourceSemantics.writeAddressKeyedMapping2FieldSlots
                fields fieldName runtime.world [slot] key1Nat key2Nat valueNat }
          have hSrcExec : SourceSemantics.execStmt fields runtime
              (.setMapping2 fieldName key1 key2 value) = .continue runtime' := by
            simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime',
              SourceSemantics.writeAddressKeyedMapping2FieldSlots, htrans, target]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [YulExpr.call "mappingSlot"
                      [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
                  .continue state' := by
            have htargetMod :
                Compiler.Proofs.solidityMappingSlot
                    (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat %
                  Compiler.Constants.evmModulus =
                Compiler.Proofs.solidityMappingSlot
                    (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat := by
              exact Nat.mod_eq_of_lt (by
                simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  (Compiler.Proofs.abstractMappingSlot_lt_evmModulus
                    (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat))
            simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey1, hIRKey2, hIRValue,
              fieldStoreBuiltin, htrans, target, state', htargetMod,
              Compiler.Proofs.abstractMappingSlot_eq_solidity,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
          have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
              (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
              runtime'.bindings state' := by
            exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
              (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
              hincl
          have hscopeRuntime' : FunctionBody.scopeNamesPresent
              (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
              runtime'.bindings := by
            simpa [runtime'] using hscope'
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨by
              simpa [runtime', state', SourceSemantics.writeAddressKeyedMapping2FieldSlots,
                htrans, target] using
                (runtimeStateMatchesIR_writeTransientTarget
                  (target := target) hruntime hvalueLt),
            hexact', hbounded, hscopeRuntime'⟩
        · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
            cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
          set state' := { state with
              storage :=
                Compiler.Proofs.abstractStoreMappingEntry
                  state.storage
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                  key2Nat
                  valueNat }
          set runtime' := { runtime with
              world := SourceSemantics.writeAddressKeyedMapping2Slots
                runtime.world [slot] key1Nat key2Nat valueNat }
          have hSrcExec : SourceSemantics.execStmt fields runtime
              (.setMapping2 fieldName key1 key2 value) = .continue runtime' := by
            simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime',
              SourceSemantics.writeAddressKeyedMapping2FieldSlots, htransFalse]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [YulExpr.call "mappingSlot"
                      [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
                  .continue state' := by
            simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey1, hIRKey2, hIRValue,
              fieldStoreBuiltin, htransFalse,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
              Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
              Compiler.Proofs.abstractStoreMappingEntry_eq, state']
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
          have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
              (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
              runtime'.bindings state' :=
            FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
              (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
              hincl
          have hscopeRuntime' : FunctionBody.scopeNamesPresent
              (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
              runtime'.bindings := by
            simpa [runtime'] using hscope'
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscopeRuntime'⟩

theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping2 fieldName key1 key2 value)
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] where
  compileOk := by
      rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
        ⟨f, hfind, _⟩
      simp only [CompilationModel.compileStmt, CompilationModel.compileSetMapping2,
        hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
      simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
        Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

private theorem compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
             let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
             if wordOffset == 0 then mappingSlot2
             else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping2Word fieldName key1 key2 wordOffset value) =
          sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call (fieldStoreBuiltin fields fieldName)
      [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
       let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
       if wordOffset == 0 then mappingSlot2
       else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])]
  -- Evaluate key1 expression
  have hkey1SourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey1 hexact hinScopeKey1 hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
      hruntime
  rw [hkey1IR] at hkey1SourceEval
  simp [Except.toOption] at hkey1SourceEval
  rcases hIRKey1 : evalIRExpr state key1IR with _ | key1Nat
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
    -- Evaluate key2 expression
    have hkey2SourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcoreKey2 hexact hinScopeKey2 hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
        hruntime
    rw [hkey2IR] at hkey2SourceEval
    simp [Except.toOption] at hkey2SourceEval
    rcases hIRKey2 : evalIRExpr state key2IR with _ | key2Nat
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
      -- Evaluate value expression
      have hvalueSourceEval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hvalueIR] at hvalueSourceEval
      simp [Except.toOption] at hvalueSourceEval
      rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
      · simp [hIRValue, Option.bind] at hvalueSourceEval
      · simp [hIRValue, Option.bind] at hvalueSourceEval
        have hKey1Src : SourceSemantics.evalExpr fields runtime key1 = some key1Nat :=
          hkey1SourceEval.symm
        have hKey2Src : SourceSemantics.evalExpr fields runtime key2 = some key2Nat :=
          hkey2SourceEval.symm
        have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          hvalueSourceEval.symm
        rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
        -- Get boundedness of valueNat
        have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
            hcoreValue hexact hinScopeValue hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
            hruntime
        rw [hValueSrc] at hvalueLt
        simp at hvalueLt
        set targetSlot := mapping2WordTargetSlot slot key1Nat key2Nat wordOffset
        let writeSlotExpr :=
          let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
          let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
          if wordOffset == 0 then mappingSlot2
          else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset]
        have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
          simpa [writeSlotExpr, targetSlot] using
            (evalIRExpr_mapping2WordTarget_of_eval
              (state := state) (slot := slot) (wordOffset := wordOffset) hIRKey1 hIRKey2)
        have hTargetAdd :
            targetSlot =
              (Verity.Core.Uint256.ofNat wordOffset +
                Verity.Core.Uint256.ofNat
                  (Compiler.Proofs.solidityMappingSlot
                    (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val := by
          simpa [targetSlot] using
            mapping2WordTargetSlot_eq_uint256_add slot key1Nat key2Nat wordOffset
        have hTargetMod :
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat + wordOffset) %
              Compiler.Constants.evmModulus = targetSlot := by
          rw [hTargetAdd]
          simpa [Nat.add_comm] using
            (uint256_add_val_eq_mod wordOffset
              (Compiler.Proofs.solidityMappingSlot
                (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).symm
        -- Scope inclusion
        have hincl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hk1 | hk2 | hv | hs
          · exact hinScopeKey1 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey1 n hk1)
          · exact hinScopeKey2 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey2 n hk2)
          · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
          · exact hs
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
            runtime.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hincl
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        by_cases htrans : SourceSemantics.fieldIsTransient fields fieldName = true
        · let target :=
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat + wordOffset) %
              Compiler.Constants.evmModulus
          set state' := { state with
              transientStorage := fun o =>
                if o = SourceSemantics.wordNormalize target then valueNat else state.transientStorage o }
          set runtime' := { runtime with
              world := SourceSemantics.writeAddressKeyedMapping2WordFieldSlots
                fields fieldName runtime.world [slot] key1Nat key2Nat wordOffset valueNat }
          have hSrcExec : SourceSemantics.execStmt fields runtime
              (.setMapping2Word fieldName key1 key2 wordOffset value) = .continue runtime' := by
            simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime',
              SourceSemantics.writeAddressKeyedMapping2WordFieldSlots,
              SourceSemantics.writeMappingTargets, htrans, target, targetSlot, hTargetMod]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [writeSlotExpr, valueIR])) = .continue state' := by
            simpa [fieldStoreBuiltin, htrans, state', target, hTargetMod] using
              (execIRStmt_tstore_of_eval
                (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
                (slotVal := targetSlot) (valueVal := valueNat) (fuel := extraFuel)
                hWriteSlotEval hIRValue)
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            change execIRStmts (1 + extraFuel + 1) state
              [YulStmt.expr (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [writeSlotExpr, valueIR])] = .continue state'
            simp [execIRStmts, hfuelEq, hExecStmt]
          have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
              (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
              runtime'.bindings state' := by
            exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
              (by intro name hname; simpa [IRState.getVar, state', runtime'] using hexact name hname)
              hincl
          have hscopeRuntime' : FunctionBody.scopeNamesPresent
              (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
              runtime'.bindings := by
            simpa [runtime'] using hscope'
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨by
                simpa [runtime', state', SourceSemantics.writeAddressKeyedMapping2WordFieldSlots,
                  SourceSemantics.writeMappingTargets, htrans, target, targetSlot, hTargetMod] using
                (runtimeStateMatchesIR_writeTransientTarget
                  (target := target) hruntime hvalueLt),
            hexact', hbounded, hscopeRuntime'⟩
        · have htransFalse : SourceSemantics.fieldIsTransient fields fieldName = false := by
            cases h : SourceSemantics.fieldIsTransient fields fieldName <;> simp [h] at htrans ⊢
          have htargetSlotNorm :
              targetSlot % Compiler.Constants.evmModulus = targetSlot := by
            exact Nat.mod_eq_of_lt (SourceSemantics.wordNormalize_lt_evmModulus _)
          set state' := { state with
              storage :=
                Compiler.Proofs.abstractStoreStorageOrMapping
                  state.storage targetSlot valueNat }
          set runtime' := { runtime with
              world := SourceSemantics.writeAddressKeyedMapping2WordSlots
                runtime.world [slot] key1Nat key2Nat wordOffset valueNat }
          have hSrcExec : SourceSemantics.execStmt fields runtime
              (.setMapping2Word fieldName key1 key2 wordOffset value) = .continue runtime' := by
            simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime',
              SourceSemantics.writeAddressKeyedMapping2WordFieldSlots,
              SourceSemantics.writeMappingTargets, SourceSemantics.writeAddressKeyedMapping2WordSlots,
              htransFalse, hTargetMod, htargetSlotNorm]
          have hStoreEq :
              Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat =
                fun s =>
                  if s =
                      IRStorageSlot.ofNat
                        ((Verity.Core.Uint256.ofNat wordOffset +
                          Verity.Core.Uint256.ofNat
                            (Compiler.Proofs.solidityMappingSlot
                              (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val) then
                    Compiler.Proofs.IRGeneration.IRStorageWord.ofNat valueNat
                  else
                    state.storage s := by
            funext s
            rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hTargetAdd]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call (fieldStoreBuiltin fields fieldName)
                    [writeSlotExpr, valueIR])) = .continue state' := by
            simpa [fieldStoreBuiltin, htransFalse, state'] using
              (execIRStmt_sstore_of_eval
                (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
                (slotVal := targetSlot) (valueVal := valueNat) (fuel := extraFuel)
                hWriteSlotEval hIRValue)
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            change execIRStmts (1 + extraFuel + 1) state
              [YulStmt.expr (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [writeSlotExpr, valueIR])] = .continue state'
            simp [execIRStmts, hfuelEq, hExecStmt]
          have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
              (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
              runtime'.bindings state' :=
            FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
              (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
              hincl
          have hscopeRuntime' : FunctionBody.scopeNamesPresent
              (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
              runtime'.bindings := by
            simpa [runtime'] using hscope'
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscopeRuntime'⟩

theorem compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping2Word fieldName key1 key2 wordOffset value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetMapping2Word,
      hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

private theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
             let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
             if wordOffset == 0 then mappingSlot2
             else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime
          (.setStructMember2 fieldName key1 key2 memberName value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call (fieldStoreBuiltin fields fieldName)
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStructMember2 fieldName key1 key2 memberName value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨sourceResult, irExec, hSrcMappingWord, hIRExec, hmatch⟩ :=
    compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
      hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
      hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR
      runtime state extraFuel hexact hscope hbounded hruntime hslack
  refine ⟨sourceResult, irExec, ?_, hIRExec, ?_⟩
  · rw [← hSrcMappingWord]
    simp only [SourceSemantics.execStmt, hwriteSlots, hmembers]
    cases SourceSemantics.evalExpr fields runtime key1 <;>
      cases SourceSemantics.evalExpr fields runtime key2 <;>
      cases SourceSemantics.evalExpr fields runtime value <;>
      simp [hmember]
  · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames]
      using hmatch

theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember2 fieldName key1 key2 memberName value)
      [YulStmt.expr
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetStructMember2,
      hmapping2, hmembers, hmember, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hmembers hmember hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

theorem compiledStmtStep_setStorage_aliasSlots
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some (slot :: f.aliasSlots))
    (halias : f.aliasSlots ≠ [])
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope)
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.block
        ([YulStmt.let_ "__compat_value" valueIR] ++
          (slot :: f.aliasSlots).map (fun writeSlot =>
            YulStmt.expr
              (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] where
  compileOk := by
    cases hty : f.ty with
    | adt name maxFields =>
        exact False.elim (hNotAdt name maxFields hty)
    | uint256 | address | dynamicArray | mappingTyped | mappingStruct | mappingStruct2 =>
        simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
          hNotMapping, hfind, hwriteSlots, halias, hunpacked, hnotTransient, hvalueIR, hty,
          pure, Except.pure, Bind.bind, Except.bind]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slots := slot :: f.aliasSlots
    let blockBody :=
      [YulStmt.let_ "__compat_value" valueIR] ++
        slots.map (fun writeSlot =>
          YulStmt.expr
            (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
    let compiledIR := [YulStmt.block blockBody]
    have heval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at heval
    · simp [hIRValue, Option.bind] at heval
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        heval.symm
      have hvalueEval : evalIRExpr state valueIR = some valueNat := hIRValue
      -- Prove sizeOf of any YulStmt list ≥ length + 1
      have hSizeOfListBound : ∀ (l : List YulStmt), l.length + 1 ≤ sizeOf l := by
        intro l
        induction l with
        | nil => simp
        | cons h t ih =>
          show t.length + 1 + 1 ≤ 1 + sizeOf h + sizeOf t
          omega
      have hbodyFuelLe : slots.length + 2 ≤ extraFuel := by
        have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
          simpa [compiledIR] using hslack
        have hlen : compiledIR.length = 1 := by simp [compiledIR]
        -- blockBody.length = 1 + slots.length (let_ + map)
        have hBodyLen : blockBody.length = 1 + slots.length := by
          simp [blockBody, slots]; omega
        have hBodyBound := hSizeOfListBound blockBody
        -- sizeOf compiledIR = 1 + sizeOf (YulStmt.block blockBody) + 1
        have hCompSizeOf : sizeOf compiledIR = 1 + sizeOf (YulStmt.block blockBody) + 1 := by
          dsimp only [compiledIR]; rfl
        -- sizeOf (YulStmt.block body) ≥ 1 + sizeOf body
        have hBlockSizeOf : 1 + sizeOf blockBody ≤ sizeOf (YulStmt.block blockBody) := by
          simp [YulStmt.block.sizeOf_spec]
        omega
      let bodyExtraFuel := extraFuel - (slots.length + 2)
      have hbodyFuelEq : slots.length + bodyExtraFuel + 2 = extraFuel := by
        dsimp [bodyExtraFuel]
        omega
      have hresolvedSlots :
          ∀ writeSlot ∈ slots, findResolvedFieldAtSlotCopy fields writeSlot = some f := by
        intro writeSlot hmem
        exact
          findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
            hnoConflict hfind hwriteSlots hmem hunpacked
      have hbody :
          execIRStmts extraFuel state blockBody =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                      (state.setVar "__compat_value" valueNat).storage
                      slots
                      valueNat } := by
        have := execIRStmts_let_then_sstore_lit_ident_slots_continue
          bodyExtraFuel state slots "__compat_value" valueIR valueNat hvalueEval
        rw [hbodyFuelEq] at this
        simpa [blockBody, slots] using this
      have hwhole :
          execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                    (state.setVar "__compat_value" valueNat).storage
                    slots
                    valueNat } := by
        have hblock := execIRStmts_single_block_of_continue
          extraFuel state
          { state.setVar "__compat_value" valueNat with
              storage :=
                abstractStoreStorageOrMappingMany
                  (state.setVar "__compat_value" valueNat).storage
                  slots
                  valueNat }
          blockBody
          hbody
        convert hblock using 2
        simp [compiledIR]; omega
      -- Prove value bound
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcore hexact hinScope hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Source execution
      have hfieldTransient :
          SourceSemantics.fieldIsTransient fields fieldName = false := by
        simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setStorage fieldName value) = .continue
            { runtime with
                world := SourceSemantics.writeUintSlots runtime.world (slot :: f.aliasSlots) valueNat } := by
        simp [SourceSemantics.execStmt, SourceSemantics.writeUintFieldSlots,
          SourceSemantics.writeMappingTargets, hwriteSlots, hValueSrc, hfieldTransient, slots]
      -- Scope inclusion
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setStorage fieldName value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hv | hs
        · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
        · exact hs
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      -- Runtime state match
      have hruntimeSet :
          FunctionBody.runtimeStateMatchesIR fields runtime (state.setVar "__compat_value" valueNat) :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields
          { runtime with world := SourceSemantics.writeUintSlots runtime.world slots valueNat }
          { (state.setVar "__compat_value" valueNat) with
              storage := abstractStoreStorageOrMappingMany
                (state.setVar "__compat_value" valueNat).storage slots valueNat } :=
        runtimeStateMatchesIR_writeUintSlots hruntimeSet hresolvedSlots hnotAddr hnotDyn hvalueLt
      -- Bindings match
      have hexactSet :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
            (state.setVar "__compat_value" valueNat) :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          hexact (compatValue_not_mem_scope_of_reservedPrefix hscopeReserved)
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setStorage fieldName value)) runtime.bindings
          { (state.setVar "__compat_value" valueNat) with
              storage := abstractStoreStorageOrMappingMany
                (state.setVar "__compat_value" valueNat).storage slots valueNat } :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlots hexactSet) hincl
      refine ⟨_, _, hSrcExec, hwhole, ?_⟩
      simp [stmtStepMatchesIRExec, slots]
      exact ⟨hruntime', hexact', hbounded, hscope'⟩

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hscopeNames :
      ∀ name, name ∈ scope →
        name ∈
          (fn.params.map (·.name) ++
            collectStmtListBindNames fn.body ++
            collectStmtListAssignedNames fn.body ++
            spec.fields.map (·.name)))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR, CompiledStmtStep spec.fields scope (.setStorage fieldName value) compiledIR := by
  by_cases halias : f.aliasSlots = []
  · refine ⟨[YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])], ?_⟩
    apply compiledStmtStep_setStorage_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := ?_)
      (halias := halias)
      (hunpacked := hunpacked)
      (hnoConflict := hnoConflict)
      (hnotAddr := hnotAddr)
      (hnotDyn := hnotDyn)
      (hnotTransient := hnotTransient)
      (hNotMapping := hNotMapping)
      (hNotAdt := hNotAdt)
      (hvalueIR := hvalueIR)
    simpa [halias] using hwriteSlots
  · refine
      ⟨[YulStmt.block
          ([YulStmt.let_ "__compat_value" valueIR] ++
            (slot :: f.aliasSlots).map (fun writeSlot =>
              YulStmt.expr
                (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))],
        ?_⟩
    apply compiledStmtStep_setStorage_aliasSlots
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := hwriteSlots)
      (halias := halias)
      (hscopeReserved := scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes
        hvalidate hfn hscopeNames)
      (hunpacked := hunpacked)
      (hnoConflict := hnoConflict)
      (hnotAddr := hnotAddr)
      (hnotDyn := hnotDyn)
      (hnotTransient := hnotTransient)
      (hNotMapping := hNotMapping)
      (hNotAdt := hNotAdt)
      (hvalueIR := hvalueIR)

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {«prefix» «suffix» : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hprefix :
      StmtListScopeDiscipline
        (spec.fields.map (·.name))
        (fn.params.map (·.name))
        «prefix»)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes
    (scope := List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
    (hvalidate := hvalidate)
    (hfn := hfn)
    (hscopeNames := ?_)
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hnotTransient := hnotTransient)
    (hNotMapping := hNotMapping)
    (hNotAdt := hNotAdt)
    (hvalueIR := hvalueIR)
  intro name hmem
  have hscopeNames := stmtListScopeDiscipline_scope_names hprefix name hmem
  have collectStmtListBindNames_prefix_subset :
      ∀ (a b : List Stmt), ∀ x, x ∈ collectStmtListBindNames a →
        x ∈ collectStmtListBindNames (a ++ b) := by
    intro a b x hx
    induction a with
    | nil => simp [collectStmtListBindNames] at hx
    | cons s rest ih =>
        simp only [collectStmtListBindNames, List.mem_append, List.cons_append] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ih h)
  have collectStmtListAssignedNames_prefix_subset :
      ∀ (a b : List Stmt), ∀ x, x ∈ collectStmtListAssignedNames a →
        x ∈ collectStmtListAssignedNames (a ++ b) := by
    intro a b x hx
    induction a with
    | nil => simp [collectStmtListAssignedNames] at hx
    | cons s rest ih =>
        simp only [collectStmtListAssignedNames, List.mem_append, List.cons_append] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ih h)
  simp only [List.mem_append] at hscopeNames ⊢
  rcases hscopeNames with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr
      (by rw [hbody]; exact collectStmtListBindNames_prefix_subset _ _ _ h)))
  · exact Or.inl (Or.inr
      (by rw [hbody]; exact collectStmtListAssignedNames_prefix_subset _ _ _ h))
  · exact Or.inr h

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {«prefix» «suffix» : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) «prefix»)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    (hvalidate := hvalidateShapes)
    (hfn := hfn)
    (hprefix := stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
      hprefixCore hvalidateRefs hparamScope
      (by simpa [List.append_assoc] using hbody))
    (hbody := hbody)
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hnotTransient := hnotTransient)
    (hNotMapping := hNotMapping)
    (hNotAdt := hNotAdt)
    (hvalueIR := hvalueIR)

-- NOTE: The _of_compileStmtList intermediate was superseded by _of_bodySurface below.
-- Its TYPESIG_SORRY signature had a bug (missing hNotMapping parameter) and was bypassed.

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {«prefix» «suffix» : List Stmt}
    {bodyIR : List YulStmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hbodyCompile :
      CompilationModel.compileStmtList
        spec.fields [] [] .calldata [] false (fn.params.map (·.name)) [] fn.body =
          Except.ok bodyIR)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hnotTransient : f.isTransient = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
        (.setStorage fieldName value)
        compiledIR := by
  have hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) «prefix» :=
    stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
      (by simpa [hbody] using hbodySurface) (by simpa [hbody] using hbodyCompile)
  have hstmtSurface :
      stmtTouchesUnsupportedContractSurface (.setStorage fieldName value) = false :=
    stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
      (by simpa [hbody] using hbodySurface)
  have hvalueCore : FunctionBody.ExprCompileCore value :=
    exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
      (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)
  have hinScope := exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
    hprefixCore hvalueCore hvalidateRefs hparamScope hbody
  have hNotMapping : isMapping spec.fields fieldName = false := by
    rcases compileStmt_ok_of_compileStmtList_append_cons
      (by simpa [hbody] using hbodyCompile) with ⟨stmtIR, hstmt⟩
    exact isMapping_false_of_compileStmt_setStorage_ok hstmt
  have hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields := by
    intro name maxFields hty
    rcases compileStmt_ok_of_compileStmtList_append_cons
      (by simpa [hbody] using hbodyCompile) with ⟨stmtIR, hstmt⟩
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, hty, hvalueIR, pure, Pure.pure, Except.pure,
      Bind.bind, Except.bind] at hstmt
  exact compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    hvalidateShapes hvalidateRefs hfn hparamScope hprefixCore hbody hvalueCore hinScope
    hfind hwriteSlots hunpacked hnoConflict hnotAddr hnotDyn hnotTransient
    hNotMapping hNotAdt hvalueIR

private theorem terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec)
    (hnotContinue : ∀ next, sourceResult ≠ .continue next) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExec, FunctionBody.stmtResultMatchesIRExec] at hmatch ⊢
  · exact False.elim (hnotContinue _ rfl)
  · exact hmatch
  · exact hmatch

theorem compiledStmtStep_ite
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields) (scope := scope) (inScopeNames := scope) (stmts := thenBranch)
      hthen with ⟨thenIR, hthenIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields) (scope := scope) (inScopeNames := scope) (stmts := elseBranch)
      helse with ⟨elseIR, helseIR⟩
  have helseNonempty : elseBranch.isEmpty = false := by
    cases elseBranch with
    | nil => exfalso; exact FunctionBody.stmtListTerminalCore_ne_nil helse rfl
    | cons => simp
  let tempName :=
    CompilationModel.pickFreshName "__ite_cond"
      (scope ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
  let compiledIR :=
    [YulStmt.block
      [ YulStmt.let_ tempName condIR
      , YulStmt.if_ (YulExpr.ident tempName) thenIR
      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]
  refine ⟨compiledIR, ?_⟩
  refine
    { compileOk := ?_
      preserves := ?_ }
  · show CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.ite cond thenBranch elseBranch) = Except.ok compiledIR
    unfold CompilationModel.compileStmt
    simp only [hcondIR, hthenIR, helseIR, Except.bind, helseNonempty, ↓reduceIte]
    rfl
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hsizeOf_eq : sizeOf compiledIR = 1 + sizeOf (YulStmt.block
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) + 1 := by
      rfl
    have hlength_eq : compiledIR.length = 1 := by rfl
    have hwholeFuel :
        compiledIR.length + extraFuel + 1 =
          sizeOf compiledIR + wholeExtraFuel + 1 := by
      rw [hWF, hsizeOf_eq, hlength_eq]
      have : sizeOf compiledIR - compiledIR.length ≤ extraFuel := hslack
      rw [hsizeOf_eq, hlength_eq] at this
      omega
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    -- Extract the Nat condition value via the eval bridge
    have heval := FunctionBody.eval_compileExpr_core_of_scope
        hcond hexact hinScope hbounded hpresent hruntime
    rw [hcondIR] at heval; simp [Except.toOption] at heval
    rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
    · simp [hCondIRVal, Option.bind] at heval
    · simp [hCondIRVal, Option.bind] at heval
      have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
        heval.symm
      have hcondEval : evalIRExpr state condIR = some condVal := hCondIRVal
      by_cases hcondZero : condVal = 0
      · -- Condition is zero → take else branch
        have hBindIte :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope) (inScopeNames := scope)
            (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch)
            (value := condVal) hexact FunctionBody.scopeNamesIncluded_refl
        have hRuntimeIte :=
          FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
            (name := tempName) (value := condVal) hruntime
        have hElse6 : sizeOf elseIR + 6 ≤ sizeOf compiledIR := by
          change sizeOf elseIR + 6 ≤ sizeOf compiledIR
          simp_wf
          omega
        let branchExtraFuel :=
          sizeOf compiledIR - (sizeOf elseIR + 5) + wholeExtraFuel - 1
        rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
            (fields := fields) (runtime := runtime)
            (state := state.setVar tempName condVal) (scope := scope)
            (inScopeNames := scope) (stmts := elseBranch)
            (extraFuel := branchExtraFuel)
            helse
            FunctionBody.scopeNamesIncluded_refl
            hscope hBindIte hbounded hRuntimeIte with
          ⟨elseIR', helseIR', helseSem⟩
        rw [helseIR] at helseIR'
        have helseEq : elseIR' = elseIR := (Except.ok.inj helseIR').symm
        rw [show elseIR' = elseIR from helseEq] at helseSem
        -- Fuel alignment: convert helseSem fuel to the form _ite_else expects
        have hfuelAlign : sizeOf elseIR + branchExtraFuel + 1 =
            sizeOf elseIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
              (sizeOf elseIR + 5) + wholeExtraFuel) := by
          simp only [List.append_nil, branchExtraFuel]
          have := hElse6
          omega
        have helseSem' :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime elseBranch)
              (execIRStmts (sizeOf elseIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
                  (sizeOf elseIR + 5) + wholeExtraFuel))
                (state.setVar tempName condVal) elseIR) := by
          rw [← hfuelAlign]; exact helseSem
        -- Apply _ite_else to get match for the whole ITE statement list
        have hiteMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime
                [Stmt.ite cond thenBranch elseBranch])
              (execIRStmts (sizeOf compiledIR + wholeExtraFuel + 1)
                state compiledIR) := by
          have := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
              (fields := fields) (runtime := runtime) (state := state)
              (scope := scope) (cond := cond)
              (thenBranch := thenBranch) (elseBranch := elseBranch) (rest := [])
              (extraFuel := wholeExtraFuel) (tempName := tempName)
              (condIR := condIR) (thenIR := thenIR) (elseIR := elseIR)
              (tailIR := []) (condValue := condVal)
              (sourceCondValue := condVal)
              helse helseSem' hCondSrc
              (by simp [hcondZero])
              hcondEval hcondZero rfl
          simp only [List.append_nil] at this
          exact this
        -- execStmt (.ite ...) = execStmtList elseBranch (by source semantics)
        have hexecStmtElse : SourceSemantics.execStmt fields runtime
            (Stmt.ite cond thenBranch elseBranch) =
            SourceSemantics.execStmtList fields runtime elseBranch := by
          simp [SourceSemantics.execStmt, hCondSrc, hcondZero]
        -- execStmtList [.ite ...] = execStmtList elseBranch (by terminal_ite_else_eq)
        have hsourceEq :=
          FunctionBody.execStmtList_terminal_core_ite_else_eq
            (fields := fields) (runtime := runtime) (scope := scope)
            (cond := cond) (thenBranch := thenBranch)
            (elseBranch := elseBranch) (rest := [])
            (condValue := condVal) helse hCondSrc
            (by simp [hcondZero])
        -- Rewrite hiteMatch source from execStmtList [.ite ...] to execStmtList elseBranch
        rw [hsourceEq] at hiteMatch
        -- Now hiteMatch : stmtResultMatchesIRExec fields
        --   (execStmtList fields runtime elseBranch) (execIRStmts ... state compiledIR)
        -- Convert to stmtResultMatchesIRExec about execStmt
        have hbodyMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmt fields runtime
                (Stmt.ite cond thenBranch elseBranch))
              (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
          rw [hexecStmtElse, hwholeFuel]; exact hiteMatch
        refine ⟨_, _, rfl, rfl, ?_⟩
        exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
            hbodyMatch
            (by rw [hexecStmtElse]
                exact FunctionBody.execStmtList_terminal_core_not_continue
                  (fields := fields) (runtime := runtime) (scope := scope)
                  (stmts := elseBranch) helse)
      · -- Condition is nonzero → take then branch
        have hBindIte :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope) (inScopeNames := scope)
            (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch)
            (value := condVal) hexact FunctionBody.scopeNamesIncluded_refl
        have hRuntimeIte :=
          FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
            (name := tempName) (value := condVal) hruntime
        have hThen5 : sizeOf thenIR + 5 ≤ sizeOf compiledIR := by
          change sizeOf thenIR + 5 ≤ sizeOf compiledIR
          simp_wf
          omega
        let branchExtraFuel :=
          sizeOf compiledIR - (sizeOf thenIR + 5) + wholeExtraFuel
        rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
            (fields := fields) (runtime := runtime)
            (state := state.setVar tempName condVal) (scope := scope)
            (inScopeNames := scope) (stmts := thenBranch)
            (extraFuel := branchExtraFuel)
            hthen
            FunctionBody.scopeNamesIncluded_refl
            hscope hBindIte hbounded hRuntimeIte with
          ⟨thenIR', hthenIR', hthenSem⟩
        rw [hthenIR] at hthenIR'
        have hthenEq : thenIR' = thenIR := (Except.ok.inj hthenIR').symm
        rw [show thenIR' = thenIR from hthenEq] at hthenSem
        -- Fuel alignment for then branch (has +1 on both sides, so direct)
        have hthenSem' :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime thenBranch)
              (execIRStmts (sizeOf thenIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
                  (sizeOf thenIR + 5) + wholeExtraFuel) + 1)
                (state.setVar tempName condVal) thenIR) := by
          simp only [List.append_nil, branchExtraFuel] at hthenSem ⊢
          exact hthenSem
        -- Apply _ite_then to get match for the whole ITE statement list
        have hiteMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime
                [Stmt.ite cond thenBranch elseBranch])
              (execIRStmts (sizeOf compiledIR + wholeExtraFuel + 1)
                state compiledIR) := by
          have := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
              (fields := fields) (runtime := runtime) (state := state)
              (scope := scope) (cond := cond)
              (thenBranch := thenBranch) (elseBranch := elseBranch) (rest := [])
              (extraFuel := wholeExtraFuel) (tempName := tempName)
              (condIR := condIR) (thenIR := thenIR) (elseIR := elseIR)
              (tailIR := []) (condValue := condVal)
              (sourceCondValue := condVal)
              hthen hthenSem' hCondSrc
              (by simp [hcondZero])
              hcondEval
              (by intro hzero; exact hcondZero hzero) rfl
          simp only [List.append_nil] at this
          exact this
        -- execStmt (.ite ...) = execStmtList thenBranch (by source semantics)
        have hexecStmtThen : SourceSemantics.execStmt fields runtime
            (Stmt.ite cond thenBranch elseBranch) =
            SourceSemantics.execStmtList fields runtime thenBranch := by
          simp [SourceSemantics.execStmt, hCondSrc, hcondZero]
        -- execStmtList [.ite ...] = execStmtList thenBranch
        have hsourceEq :=
          FunctionBody.execStmtList_terminal_core_ite_then_eq
            (fields := fields) (runtime := runtime) (scope := scope)
            (cond := cond) (thenBranch := thenBranch)
            (elseBranch := elseBranch) (rest := [])
            (condValue := condVal) hthen hCondSrc
            (by simp [hcondZero])
        rw [hsourceEq] at hiteMatch
        have hbodyMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmt fields runtime
                (Stmt.ite cond thenBranch elseBranch))
              (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
          rw [hexecStmtThen, hwholeFuel]; exact hiteMatch
        refine ⟨_, _, rfl, rfl, ?_⟩
        exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
            hbodyMatch
            (by rw [hexecStmtThen]
                exact FunctionBody.execStmtList_terminal_core_not_continue
                  (fields := fields) (runtime := runtime) (scope := scope)
                  (stmts := thenBranch) hthen)

theorem stmtListTouchesUnsupportedContractSurface_append
    {«prefix» «suffix» : List Stmt} :
    stmtListTouchesUnsupportedContractSurface («prefix» ++ «suffix») =
      (stmtListTouchesUnsupportedContractSurface «prefix» ||
        stmtListTouchesUnsupportedContractSurface «suffix») := by
  induction «prefix» with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest ih =>
      cases stmt <;> simp [stmtListTouchesUnsupportedContractSurface, ih, Bool.or_assoc]

theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_append
    {«prefix» «suffix» : List Stmt} :
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites («prefix» ++ «suffix») =
      (stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «prefix» ||
        stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «suffix») := by
  induction «prefix» with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites, ih, Bool.or_assoc]

private theorem stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_contractSurface
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface] at hsurface ⊢
  all_goals assumption

theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_contractSurface
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_contractSurface hsplit.1,
        ih hsplit.2]

set_option maxHeartbeats 800000 in
private theorem compiledStmtStep_letStorageField
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.letVar tmp (Expr.storage fieldName))
      [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileExpr, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hEvalSrc : SourceSemantics.evalExpr fields runtime (.storage fieldName) =
        some (runtime.world.storage (SourceSemantics.wordNormalize slot)).val := by
      change (match findFieldWithResolvedSlot fields fieldName with
        | some (field, s) => some (SourceSemantics.readFieldWord runtime.world field s).val
        | none => none) = _
      rw [hfind]
      rfl
    have hresolved := findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind
      (by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind) (by rfl)
    have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
    have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat =
            some { name := fieldName, ty := FieldType.uint256 } := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
              some { name := fieldName, ty := FieldType.uint256 } from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
    rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' (by rfl) (by rfl)] at hIR
    set v := (runtime.world.storage (SourceSemantics.wordNormalize slot)).val
    set state' := state.setVar tmp v
    set runtime' := { runtime with bindings := SourceSemantics.bindValue runtime.bindings tmp v }
    have hNextScopeIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.letVar tmp (Expr.storage fieldName))) (tmp :: scope) := by
      intro n hn; simp [stmtNextScope, collectStmtNames, collectExprNames] at hn
      rcases hn with rfl | rfl | hn <;>
        [simp; exact List.mem_cons_of_mem _ hfieldInScope; exact List.mem_cons_of_mem _ hn]
    refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
    · show (match SourceSemantics.evalExpr fields runtime (.storage fieldName) with
        | some r => SourceSemantics.StmtResult.continue { runtime with
            bindings := SourceSemantics.bindValue runtime.bindings tmp r }
        | none => SourceSemantics.StmtResult.revert) = _; rw [hEvalSrc]
    · have : [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])].length +
          extraFuel + 1 = Nat.succ (Nat.succ extraFuel) := by simp [List.length]; omega
      rw [this]; simp [execIRStmts, execIRStmt, hIR, state', v,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      apply congrArg (state.setVar tmp)
      exact Nat.mod_eq_of_lt (by
        simpa [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS] using
          (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt)
    · simp only [stmtStepMatchesIRExec]
      exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime tmp v,
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hNextScopeIncl,
          FunctionBody.bindingsBounded_bindValue hbounded tmp v
            (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt,
        FunctionBody.scopeNamesPresent_of_included
          (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hNextScopeIncl⟩

theorem stmtListGenericCore_singleton_letStorageField
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.letVar tmp (Expr.storage fieldName)] :=
  StmtListGenericCore.cons
    (compiledStmtStep_letStorageField hnoConflict hfind hfieldInScope)
    StmtListGenericCore.nil

set_option maxHeartbeats 800000 in
private theorem compiledStmtStep_letStorageAddrField
    {fields : List Field} {scope : List String} {tmp fieldName : String} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.letVar tmp (Expr.storageAddr fieldName))
      [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileExpr, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hEvalSrc : SourceSemantics.evalExpr fields runtime (.storageAddr fieldName) =
        some (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val := by
      change (match findFieldWithResolvedSlot fields fieldName with
        | some (field, s) =>
            if field.isTransient then
              some (runtime.world.transientStorage (SourceSemantics.wordNormalize s)).val
            else
              some (runtime.world.storageAddr (SourceSemantics.wordNormalize s)).val
        | none => none) = _
      rw [hfind]
      rfl
    have hresolved := findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind
      (by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind) (by rfl)
    have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
    have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat =
            some { name := fieldName, ty := FieldType.address } := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
              some { name := fieldName, ty := FieldType.address } from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
    rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot hresolved' (by rfl) (by rfl)] at hIR
    set v := (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val
    set state' := state.setVar tmp v
    set runtime' := { runtime with bindings := SourceSemantics.bindValue runtime.bindings tmp v }
    have hAddrLt : v < Verity.Core.UINT256_MODULUS :=
      Nat.lt_trans (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).isLt (by decide)
    have hNextScopeIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.letVar tmp (Expr.storageAddr fieldName))) (tmp :: scope) := by
      intro n hn; simp [stmtNextScope, collectStmtNames, collectExprNames] at hn
      rcases hn with rfl | rfl | hn <;>
        [simp; exact List.mem_cons_of_mem _ hfieldInScope; exact List.mem_cons_of_mem _ hn]
    refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
    · show (match SourceSemantics.evalExpr fields runtime (.storageAddr fieldName) with
        | some r => SourceSemantics.StmtResult.continue { runtime with
            bindings := SourceSemantics.bindValue runtime.bindings tmp r }
        | none => SourceSemantics.StmtResult.revert) = _; rw [hEvalSrc]
    · have : [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])].length +
          extraFuel + 1 = Nat.succ (Nat.succ extraFuel) := by simp [List.length]; omega
      rw [this]; simp [execIRStmts, execIRStmt, hIR, state', v,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      apply congrArg (state.setVar tmp)
      exact Nat.mod_eq_of_lt (by
        simpa [Verity.Core.UINT256_MODULUS] using hAddrLt)
    · simp only [stmtStepMatchesIRExec]
      exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime tmp v,
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hNextScopeIncl,
        FunctionBody.bindingsBounded_bindValue hbounded tmp v hAddrLt,
        FunctionBody.scopeNamesPresent_of_included
          (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hNextScopeIncl⟩

theorem stmtListGenericCore_singleton_letStorageAddrField
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.letVar tmp (Expr.storageAddr fieldName)] :=
  StmtListGenericCore.cons
    (compiledStmtStep_letStorageAddrField hnoConflict hfind hfieldInScope)
    StmtListGenericCore.nil

private theorem compiledStmtStep_assignStorageField
    {fields : List Field}
    {scope : List String}
    {name fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.assignVar name (Expr.storage fieldName))
      [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileExpr, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hEvalSrc : SourceSemantics.evalExpr fields runtime (.storage fieldName) =
        some (runtime.world.storage (SourceSemantics.wordNormalize slot)).val := by
      change (match findFieldWithResolvedSlot fields fieldName with
        | some (field, s) => some (SourceSemantics.readFieldWord runtime.world field s).val
        | none => none) = _
      rw [hfind]
      rfl
    have hresolved := findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind
      (by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind) (by rfl)
    have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
    have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat =
            some { name := fieldName, ty := FieldType.uint256 } := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
              some { name := fieldName, ty := FieldType.uint256 } from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
    rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' (by rfl) (by rfl)] at hIR
    set v := (runtime.world.storage (SourceSemantics.wordNormalize slot)).val
    set state' := state.setVar name v
    set runtime' := { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
    have hNextScopeIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.assignVar name (Expr.storage fieldName))) (name :: scope) := by
      intro n hn; simp [stmtNextScope, collectStmtNames, collectExprNames] at hn
      rcases hn with rfl | rfl | hn <;>
        [simp; exact List.mem_cons_of_mem _ hfieldInScope; exact List.mem_cons_of_mem _ hn]
    refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
    · show (match SourceSemantics.evalExpr fields runtime (.storage fieldName) with
        | some r => SourceSemantics.StmtResult.continue { runtime with
            bindings := SourceSemantics.bindValue runtime.bindings name r }
        | none => SourceSemantics.StmtResult.revert) = _; rw [hEvalSrc]
    · have : [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])].length +
          extraFuel + 1 = Nat.succ (Nat.succ extraFuel) := by simp [List.length]; omega
      rw [this]; simp [execIRStmts, execIRStmt, hIR, state', v,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      apply congrArg (state.setVar name)
      exact Nat.mod_eq_of_lt (by
        simpa [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS] using
          (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt)
    · simp only [stmtStepMatchesIRExec]
      exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v,
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hNextScopeIncl,
          FunctionBody.bindingsBounded_bindValue hbounded name v
            (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt,
        FunctionBody.scopeNamesPresent_of_included
          (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hNextScopeIncl⟩

theorem stmtListGenericCore_singleton_assignStorageField
    {fields : List Field}
    {scope : List String}
    {name fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.assignVar name (Expr.storage fieldName)] :=
  StmtListGenericCore.cons
    (compiledStmtStep_assignStorageField hnoConflict hfind hfieldInScope)
    StmtListGenericCore.nil

set_option maxHeartbeats 800000 in
private theorem compiledStmtStep_assignStorageAddrField
    {fields : List Field} {scope : List String} {name fieldName : String} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.assignVar name (Expr.storageAddr fieldName))
      [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileExpr, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hEvalSrc : SourceSemantics.evalExpr fields runtime (.storageAddr fieldName) =
        some (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val := by
      change (match findFieldWithResolvedSlot fields fieldName with
        | some (field, s) =>
            if field.isTransient then
              some (runtime.world.transientStorage (SourceSemantics.wordNormalize s)).val
            else
              some (runtime.world.storageAddr (SourceSemantics.wordNormalize s)).val
        | none => none) = _
      rw [hfind]
      rfl
    have hresolved := findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind
      (by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind) (by rfl)
    have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
    have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat =
            some { name := fieldName, ty := FieldType.address } := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
              some { name := fieldName, ty := FieldType.address } from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
    rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot hresolved' (by rfl) (by rfl)] at hIR
    set v := (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val
    set state' := state.setVar name v
    set runtime' := { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
    have hAddrLt : v < Verity.Core.UINT256_MODULUS :=
      Nat.lt_trans (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).isLt (by decide)
    have hNextScopeIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.assignVar name (Expr.storageAddr fieldName))) (name :: scope) := by
      intro n hn; simp [stmtNextScope, collectStmtNames, collectExprNames] at hn
      rcases hn with rfl | rfl | hn <;>
        [simp; exact List.mem_cons_of_mem _ hfieldInScope; exact List.mem_cons_of_mem _ hn]
    refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
    · show (match SourceSemantics.evalExpr fields runtime (.storageAddr fieldName) with
        | some r => SourceSemantics.StmtResult.continue { runtime with
            bindings := SourceSemantics.bindValue runtime.bindings name r }
        | none => SourceSemantics.StmtResult.revert) = _; rw [hEvalSrc]
    · have : [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])].length +
          extraFuel + 1 = Nat.succ (Nat.succ extraFuel) := by simp [List.length]; omega
      rw [this]; simp [execIRStmts, execIRStmt, hIR, state', v,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      apply congrArg (state.setVar name)
      exact Nat.mod_eq_of_lt (by
        simpa [Verity.Core.UINT256_MODULUS] using hAddrLt)
    · simp only [stmtStepMatchesIRExec]
      exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v,
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hNextScopeIncl,
        FunctionBody.bindingsBounded_bindValue hbounded name v hAddrLt,
        FunctionBody.scopeNamesPresent_of_included
          (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hNextScopeIncl⟩

theorem stmtListGenericCore_singleton_assignStorageAddrField
    {fields : List Field}
    {scope : List String}
    {name fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.assignVar name (Expr.storageAddr fieldName)] :=
  StmtListGenericCore.cons
    (compiledStmtStep_assignStorageAddrField hnoConflict hfind hfieldInScope)
    StmtListGenericCore.nil

theorem stmtListGenericCore_singleton_iteTerminal
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    StmtListGenericCore fields scope [Stmt.ite cond thenBranch elseBranch] := by
  rcases compiledStmtStep_ite (fields := fields)
      hcond hinScope hthen helse with ⟨compiledIR, hstep⟩
  exact StmtListGenericCore.cons hstep StmtListGenericCore.nil

theorem stmtListGenericCore_singleton_setStorage_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {value : Expr}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStorage_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind)
      (halias := by rfl)
      (hunpacked := by rfl)
      (hnoConflict := hnoConflict)
      (hnotAddr := by rfl)
      (hnotDyn := by rfl)
      (hnotTransient := by rfl)
      (hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl)
      (hNotAdt := by
        intro name maxFields hty
        cases hty)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setStorageAddr_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {value : Expr}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStorageAddr_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind)
      (hnoConflict := hnoConflict)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
    ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_mstore_single
      (hcoreOffset := hcoreOffset)
      (hinScopeOffset := hinScopeOffset)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hoffsetIR := hoffsetIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
    ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_tstore_single
      (hcoreOffset := hcoreOffset)
      (hinScopeOffset := hinScopeOffset)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hoffsetIR := hoffsetIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

theorem stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] :=
  stmtListGenericCore_singleton_setStorage_singleSlot
    (fields := fields)
    (scope := scope)
    (hnoConflict := hnoConflict)
    (hfind := hfind)
    (hcore := hcore)
    (hinScope := hinScope)

theorem stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] :=
  stmtListGenericCore_singleton_setStorageAddr_singleSlot
    (fields := fields)
    (scope := scope)
    (hnoConflict := hnoConflict)
    (hfind := hfind)
    (hcore := hcore)
    (hinScope := hinScope)

theorem stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] :=
  stmtListGenericCore_singleton_mstore_single
    (fields := fields)
    (scope := scope)
    (hcoreOffset := hcoreOffset)
    (hinScopeOffset := hinScopeOffset)
    (hcoreValue := hcoreValue)
    (hinScopeValue := hinScopeValue)

theorem stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] :=
  stmtListGenericCore_singleton_tstore_single
    (fields := fields)
    (scope := scope)
    (hcoreOffset := hcoreOffset)
    (hinScopeOffset := hinScopeOffset)
    (hcoreValue := hcoreValue)
    (hinScopeValue := hinScopeValue)


end Compiler.Proofs.IRGeneration
