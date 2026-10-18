import Compiler.Proofs.IRGeneration.GenericInduction.ExprStmt
import Compiler.Proofs.IRGeneration.EmptyRevert
import Compiler.CompilationModel.ReservedScratchNames

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

attribute [local simp] CompilationModel.compileExprWithInternals_nil_eq

private theorem singleton_contains_false {x y : Nat} (h : y ≠ x) :
    [x].contains y = false :=
  Bool.eq_false_iff.2 fun hcont =>
    h (List.mem_singleton.mp ((List.contains_iff_mem).mp hcont))

private theorem singleton_contains_true (x : Nat) : [x].contains x = true :=
  (List.contains_iff_mem).mpr (List.mem_singleton.mpr rfl)

private theorem compileExprWithInternals_nil_ok
    {fields : List Field} {dynamicSource : DynamicDataSource} {expr : Expr} {exprIR : YulExpr}
    (h : CompilationModel.compileExpr fields dynamicSource expr = Except.ok exprIR) :
    CompilationModel.compileExprWithInternals fields dynamicSource [] expr = Except.ok exprIR := by
  simpa [CompilationModel.compileExprWithInternals_nil_eq] using h

private theorem compileExprListWithInternals_nil_ok
    {fields : List Field} {dynamicSource : DynamicDataSource} {exprs : List Expr}
    {exprIRs : List YulExpr}
    (h : CompilationModel.compileExprList fields dynamicSource exprs = Except.ok exprIRs) :
    CompilationModel.compileExprListWithInternals fields dynamicSource [] exprs =
      Except.ok exprIRs := by
  simpa [CompilationModel.compileExprListWithInternals_nil_eq] using h

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
    simp [SourceSemantics.writeUintSlots, SourceSemantics.wordNormalize]
    have hfalse : [slot % Compiler.Constants.evmModulus].contains query = false :=
      singleton_contains_false hneq'
    exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _ hfalse
  · simp [SourceSemantics.writeUintSlots, Verity.ContractState.storageAddr_writePhysicalSlots]
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
    have hfalse : (slots.map SourceSemantics.wordNormalize).contains query = false := by
      simpa [List.contains_iff_mem] using hnotMem
    exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _ hfalse
  · simp [SourceSemantics.writeUintSlots, Verity.ContractState.storageAddr_writePhysicalSlots]
  · simp [SourceSemantics.writeUintSlots]

/-- A singleton uint-keyed mapping write leaves every other in-range slot's word. -/
private theorem storage_writeUintKeyedMappingSlots_singleton_of_ne
    {world : Verity.ContractState} {slot key query value : Nat}
    (hquery : query < Compiler.Constants.evmModulus)
    (hneq : query ≠ SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key)) :
    (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value).storage query =
      world.storage query := by
  simp only [SourceSemantics.writeUintKeyedMappingSlots, List.foldl_cons, List.foldl_nil]
  have hneq' :
      query ≠ Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus := by
    simpa [SourceSemantics.wordNormalize, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
      hneq
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
  · exact storage_writeUintKeyedMappingSlots_singleton_of_ne hquery hneq
  · simp [SourceSemantics.writeUintKeyedMappingSlots,
      Verity.ContractState.storageAddr_writeMapUint,
      Verity.ContractState.storageAddr_withStorageChannel]
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
      SourceSemantics.wordNormalize]
    have hfalse :
        [SourceSemantics.mappingSlotChain slot keys % Compiler.Constants.evmModulus].contains query =
          false :=
      singleton_contains_false hneq'
    exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _ hfalse
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots,
      Verity.ContractState.storageAddr_writePhysicalSlots]
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
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS] using h

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

private theorem mapping2WordTargetSlot_eq_mod (slot key1 key2 wordOffset : Nat) :
    mapping2WordTargetSlot slot key1 key2 wordOffset =
      (Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
        Compiler.Constants.evmModulus := by
  rw [mapping2WordTargetSlot_eq_uint256_add, uint256_add_val_eq_mod, Nat.add_comm]

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
      have hfalse :
          [(Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus].contains query = false :=
        singleton_contains_false hEq
      exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _ hfalse
  · simp [SourceSemantics.writeAddressKeyedMappingWordSlots,
      Verity.ContractState.storageAddr_writePhysicalSlots]
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
      have hfalse :
          [(Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus].contains query = false :=
        singleton_contains_false hEq
      exact Verity.ContractState.storage_modifyPhysicalSlots_not_mem _ _ _ hfalse
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots,
      Verity.ContractState.storageAddr_modifyPhysicalSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]

def findResolvedFieldAtSlotCopy (fields : List Field) (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if field.isTransient == false &&
            (SourceSemantics.wordNormalize resolvedSlot = SourceSemantics.wordNormalize slot ||
            (field.aliasSlots.map SourceSemantics.wordNormalize).contains
              (SourceSemantics.wordNormalize slot)) then
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
      if field.isTransient == false &&
          (SourceSemantics.wordNormalize resolvedSlot = SourceSemantics.wordNormalize slot ||
          (field.aliasSlots.map SourceSemantics.wordNormalize).contains
            (SourceSemantics.wordNormalize slot)) then
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
    SourceSemantics.findResolvedFieldAtStorageSlot.go false slot remaining idx =
      findResolvedFieldAtSlotCopy.go slot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
    simp only [SourceSemantics.findResolvedFieldAtStorageSlot.go, findResolvedFieldAtSlotCopy.go]
    split <;> simp_all

theorem findResolvedFieldAtSlotCopy_eq
    (fields : List Field) (slot : Nat) :
    SourceSemantics.findResolvedFieldAtSlot fields slot =
      findResolvedFieldAtSlotCopy fields slot := by
  simp only [SourceSemantics.findResolvedFieldAtSlot,
    SourceSemantics.findResolvedFieldAtStorageSlot, findResolvedFieldAtSlotCopy]
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
    (SourceSemantics.wordNormalize (field.slot.getD idx), field.isTransient) ∈
      (fieldWriteEntriesAt idx field).map
        (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
  obtain ⟨name, ty, isTransient, slotOpt, packedBits, aliasSlots⟩ := field
  cases isTransient <;>
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
    (SourceSemantics.wordNormalize slot, field.isTransient) ∈
      (fieldWriteEntriesAt idx field).map
        (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
    obtain ⟨name, ty, isTransient, slotOpt, packedBits, aliasSlots⟩ := field
    obtain ⟨aliasIdx, halias⟩ : ∃ i, (slot, i) ∈ aliasSlots.zipIdx :=
      exists_mem_zipIdx_of_mem hmem
    cases isTransient <;> cases ty with
    | uint256 | int256 =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | address =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | fixedArrayUint128 size =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize, halias]
        aesop
    | adt _ maxFields =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, 0, by simp, by simp [SourceSemantics.wordNormalize]⟩
    | dynamicArray _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | mappingTyped _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | mappingStruct _ _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | mappingStruct2 _ _ _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩
    | mappingFixedArray _ _ =>
        simp [fieldWriteEntriesAt, firstFieldWriteSlotConflict.fieldOccupiedSlots,
          SourceSemantics.wordNormalize]
        exact Or.inr ⟨slot, ⟨aliasIdx, halias⟩, by simp [SourceSemantics.wordNormalize]⟩

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
      match seen.find? (fun entry => entry.1 == slot &&
          storageOwnersSameSpace entry.2.1 ownerName && packedSlotsConflict entry.2.2 packed) with
      | some (_, prevName, _) =>
          some (slot, storageOwnerDisplay prevName, storageOwnerDisplay ownerName)
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
    {slot : Nat} {ownerName : String}
    (hmem : (slot, storageOwnerIsTransient ownerName) ∈ seen.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1))) :
    (seen.find? (fun entry => entry.1 == slot &&
        storageOwnersSameSpace entry.2.1 ownerName &&
        packedSlotsConflict entry.2.2 none)) ≠ none := by
  obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hmem
  intro hnone
  have hfalse := List.find?_eq_none.mp hnone entry hentry
  obtain ⟨entrySlot, entryOwner, entryPacked⟩ := entry
  simp only [Prod.fst, Prod.snd] at hkey hfalse
  have hs : entrySlot = slot := congrArg Prod.fst hkey
  have ht : storageOwnerIsTransient entryOwner =
      storageOwnerIsTransient ownerName := congrArg Prod.snd hkey
  apply hfalse
  cases entryPacked <;> simp [hs, storageOwnersSameSpace, ht, packedSlotsConflict]

private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat} {isTransient : Bool}
    (hseen : (slot, isTransient) ∈ seen.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)))
    (hcurrent : (slot, isTransient) ∈ current.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by
  induction current generalizing seen with
  | nil => simp at hcurrent
  | cons entry rest ih =>
      have hpnone : entry.2.2 = none := hunpacked entry.2.2 (by simp)
      have hunpackedRest :
          ∀ packed ∈ rest.map (fun restEntry => restEntry.2.2), packed = none := by
        intro packed hmem
        exact hunpacked packed (by simp [hmem])
      obtain ⟨e1, e21, e22⟩ := entry
      simp at hpnone
      subst hpnone
      simp only [List.map_cons, List.mem_cons] at hcurrent
      rcases hcurrent with hcurrent | hrest
      · have hs : slot = e1 := congrArg Prod.fst hcurrent
        have ht : isTransient = storageOwnerIsTransient e21 := congrArg Prod.snd hcurrent
        subst slot
        subst isTransient
        have hfindSeen := list_findSlotPackedNone_ne_none (ownerName := e21) hseen
        simp only [firstInFieldConflictCopy]
        cases hf : seen.find? (fun seenEntry => seenEntry.1 == e1 &&
            storageOwnersSameSpace seenEntry.2.1 e21 && packedSlotsConflict seenEntry.2.2 none)
        · exact absurd hf hfindSeen
        · simp
      ·
        intro hnone
        simp only [firstInFieldConflictCopy] at hnone
        cases hfind : seen.find? (fun seenEntry => seenEntry.1 == e1 &&
            storageOwnersSameSpace seenEntry.2.1 e21 && packedSlotsConflict seenEntry.2.2 none)
        · rw [hfind] at hnone
          simp at hnone
          have hseen' :
              (slot, isTransient) ∈ (((e1, e21, none) :: seen).map
                (fun seenEntry => (seenEntry.1,
                  storageOwnerIsTransient seenEntry.2.1))) := by
            simp [hseen]
          exact (ih hseen' hrest hunpackedRest) hnone
        · rw [hfind] at hnone; simp at hnone

private theorem firstInFieldConflictCopy_fieldWriteEntriesAt_ne_none
    {seen : List (Nat × String × Option PackedBits)} {idx targetSlot : Nat} {field : Field}
    (hseen : (SourceSemantics.wordNormalize targetSlot, field.isTransient) ∈ seen.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)))
    (hslot : targetSlot ∈ field.slot.getD idx :: field.aliasSlots)
    (hunpacked : field.packedBits = none) :
    firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) ≠ none := by
  have htarget :
      (SourceSemantics.wordNormalize targetSlot, field.isTransient) ∈
        (fieldWriteEntriesAt idx field).map
          (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
    rcases List.mem_cons.mp hslot with hslot | halias
    · subst targetSlot
      exact fieldWriteEntriesAt_base_mem idx field
    · exact fieldWriteEntriesAt_alias_mem halias
  exact firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked hseen htarget
    (fun _ hmem => fieldWriteEntriesAt_packed_none_of_unpacked hunpacked hmem)

private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    (hseen : (SourceSemantics.wordNormalize targetSlot, f.isTransient) ∈ seen.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)))
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
      · simp [hname] at hfind hwrite
        obtain ⟨rfl, rfl⟩ := hfind
        subst hwrite
        have hconflict :=
          firstInFieldConflictCopy_fieldWriteEntriesAt_ne_none hseen hslot hunpacked
        cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
        | none => exact absurd hc hconflict
        | some _ => simp
      · simp [hname] at hfind hwrite
        have hseen' :
              (SourceSemantics.wordNormalize targetSlot, f.isTransient) ∈
                ((fieldWriteEntriesAt idx field).reverse ++ seen).map
                (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
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
    (hseen : (SourceSemantics.wordNormalize slot, f.isTransient) ∈ seen.map
      (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
  exact
    firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
      hseen hfind hwrite (by simp) hunpacked

private theorem findResolvedFieldAtSlotCopyFrom_cons_self
    {field : Field} {rest : List Field} {idx targetSlot : Nat}
    (hslot : targetSlot ∈ field.slot.getD idx :: field.aliasSlots)
    (hpersistent : field.isTransient = false) :
    findResolvedFieldAtSlotCopyFrom (field :: rest) idx targetSlot = some field := by
  simp only [findResolvedFieldAtSlotCopyFrom]
  rcases List.mem_cons.mp hslot with rfl | hmem
  · simp [hpersistent]
  · rw [show
      (List.map SourceSemantics.wordNormalize field.aliasSlots).contains
        (SourceSemantics.wordNormalize targetSlot) = true by
        rw [List.contains_eq_mem]
        exact decide_eq_true (List.mem_map.mpr ⟨targetSlot, hmem, rfl⟩)]
    simp [hpersistent]

private theorem findResolvedFieldAtSlotCopyFrom_cons_of_not_capture
    {field : Field} {rest : List Field} {idx targetSlot : Nat}
    (hcapture : ¬(SourceSemantics.wordNormalize (field.slot.getD idx) =
        SourceSemantics.wordNormalize targetSlot ∨
      ∃ a ∈ field.aliasSlots,
        SourceSemantics.wordNormalize a = SourceSemantics.wordNormalize targetSlot)) :
    findResolvedFieldAtSlotCopyFrom (field :: rest) idx targetSlot =
      findResolvedFieldAtSlotCopyFrom rest (idx + 1) targetSlot := by
  push Not at hcapture
  have hmiss :
      (decide (SourceSemantics.wordNormalize (field.slot.getD idx) =
        SourceSemantics.wordNormalize targetSlot) ||
      (List.map SourceSemantics.wordNormalize field.aliasSlots).contains
        (SourceSemantics.wordNormalize targetSlot)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not,
      List.contains_eq_mem, List.mem_map]
    exact ⟨hcapture.1, fun ⟨a, haMem, haEq⟩ => hcapture.2 a haMem haEq⟩
  simp only [findResolvedFieldAtSlotCopyFrom, hmiss, Bool.and_false, Bool.false_eq_true,
    if_false]

private theorem findResolvedFieldAtSlotCopyFrom_cons_of_transient
    {field : Field} {rest : List Field} {idx targetSlot : Nat}
    (htransient : field.isTransient = true) :
    findResolvedFieldAtSlotCopyFrom (field :: rest) idx targetSlot =
      findResolvedFieldAtSlotCopyFrom rest (idx + 1) targetSlot := by
  simp [findResolvedFieldAtSlotCopyFrom, htransient]

private theorem fieldWriteEntriesAt_mem_of_capture
    {idx targetSlot : Nat} {field : Field}
    (hcapture : SourceSemantics.wordNormalize (field.slot.getD idx) =
        SourceSemantics.wordNormalize targetSlot ∨
      ∃ a ∈ field.aliasSlots,
        SourceSemantics.wordNormalize a = SourceSemantics.wordNormalize targetSlot) :
    (SourceSemantics.wordNormalize targetSlot, field.isTransient) ∈
      (fieldWriteEntriesAt idx field).map
        (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
  rcases hcapture with hbase | ⟨a, haMem, haEq⟩
  · have hb := fieldWriteEntriesAt_base_mem idx field
    rw [hbase] at hb
    exact hb
  · have haIn := fieldWriteEntriesAt_alias_mem (idx := idx) (field := field) haMem
    rw [haEq] at haIn
    exact haIn

private theorem firstFieldWriteSlotConflictCopyFrom_ne_none_of_capture
    {seen : List (Nat × String × Option PackedBits)} {field f : Field} {rest : List Field}
    {idx slot targetSlot : Nat} {fieldName : String} {writeSlots : List Nat}
    (hcapture : SourceSemantics.wordNormalize (field.slot.getD idx) =
        SourceSemantics.wordNormalize targetSlot ∨
      ∃ a ∈ field.aliasSlots,
        SourceSemantics.wordNormalize a = SourceSemantics.wordNormalize targetSlot)
    (hspace : field.isTransient = f.isTransient)
    (hfind : findFieldWithResolvedSlotCopyFrom rest (idx + 1) fieldName = some (f, slot))
    (hwrite : findFieldWriteSlotsCopyFrom rest (idx + 1) fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom ((fieldWriteEntriesAt idx field).reverse ++ seen)
      (idx + 1) rest ≠ none := by
  have hseen :
      (SourceSemantics.wordNormalize targetSlot, field.isTransient) ∈
        ((fieldWriteEntriesAt idx field).reverse ++ seen).map
          (fun entry => (entry.1, storageOwnerIsTransient entry.2.1)) := by
    rw [List.map_append, List.mem_append, List.map_reverse]
    exact Or.inl (List.mem_reverse.mpr (fieldWriteEntriesAt_mem_of_capture hcapture))
  rw [hspace] at hseen
  exact firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
    hseen hfind hwrite hslot hunpacked

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
    (hpersistent : f.isTransient = false)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopyFrom fields idx targetSlot = some f := by
  induction fields generalizing seen idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at hfind
  | cons field rest ih =>
    simp only [findFieldWithResolvedSlotCopyFrom] at hfind
    simp only [findFieldWriteSlotsCopyFrom] at hwrite
    simp only [firstFieldWriteSlotConflictCopyFrom] at hnoConflict
    by_cases hname : field.name == fieldName
    · simp [hname] at hfind hwrite
      obtain ⟨rfl, rfl⟩ := hfind
      subst writeSlots
      exact findResolvedFieldAtSlotCopyFrom_cons_self hslot hpersistent
    · simp [hname] at hfind hwrite
      cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
      | some conflict => rw [hc] at hnoConflict; simp at hnoConflict
      | none =>
        rw [hc] at hnoConflict
        have hrest := ih hnoConflict hfind hwrite
        cases hspace : field.isTransient
        · by_cases hcapture :
            SourceSemantics.wordNormalize (field.slot.getD idx) =
              SourceSemantics.wordNormalize targetSlot ∨
            ∃ a ∈ field.aliasSlots,
              SourceSemantics.wordNormalize a = SourceSemantics.wordNormalize targetSlot
          · exact absurd hnoConflict (firstFieldWriteSlotConflictCopyFrom_ne_none_of_capture
              hcapture (hspace.trans hpersistent.symm) hfind hwrite hslot hunpacked)
          · rw [findResolvedFieldAtSlotCopyFrom_cons_of_not_capture hcapture]
            exact hrest
        · rw [findResolvedFieldAtSlotCopyFrom_cons_of_transient hspace]
          exact hrest

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
    cases seen.find? (fun entry => entry.1 == slot &&
        storageOwnersSameSpace entry.2.1 ownerName && packedSlotsConflict entry.2.2 packed) with
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
    (hpersistent : f.isTransient = false)
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
    hnoConflictCopy hfindCopy hwriteCopy hslot hpersistent hunpacked

theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some [slot])
    (hpersistent : f.isTransient = false)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields slot = some f := by
  exact
    findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
      hnoConflict hfind hwrite (by simp) hpersistent hunpacked

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
  simp only [SourceSemantics.writeUintKeyedMappingSlots]
  rw [Verity.ContractState.storage_writeMapUint,
    Verity.ContractState.storage_withStorageChannel]
  simp only [List.foldl_cons, List.foldl_nil]
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
  simp only [SourceSemantics.writeAddressKeyedMappingChainSlots, List.map_cons, List.map_nil]
  rw [Verity.ContractState.storage_writePhysicalSlots_mem _ _ _
    (singleton_contains_true _)]
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

private theorem encodeStorageAt_eq_storage_of_unowned
    {fields : List Field} {world world' : Verity.ContractState} {query : Nat}
    (hresolved : findResolvedFieldAtSlotCopy fields query = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields world query = none)
    (harray : world'.storageArray = world.storageArray) :
    SourceSemantics.encodeStorageAt fields world' query = (world'.storage query).val := by
  have hdyn' : findDynamicArrayElementAtSlotCopy fields world' query = none := by
    rw [← findDynamicArrayElementAtSlotCopy_eq,
      SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
      findDynamicArrayElementAtSlotCopy_eq, hdyn]
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved, hdyn']

private theorem encodeStorageAt_wordNormalize_eq_storage_of_unowned
    {fields : List Field} {world world' : Verity.ContractState} {query : Nat}
    (hresolved : findResolvedFieldAtSlotCopy fields query = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields world query = none)
    (harray : world'.storageArray = world.storageArray) :
    SourceSemantics.encodeStorageAt fields world' (SourceSemantics.wordNormalize query) =
      (world'.storage (SourceSemantics.wordNormalize query)).val :=
  encodeStorageAt_eq_storage_of_unowned
    (by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
    (by rw [findDynamicArrayElementAtSlotCopy_wordNormalize]; exact hdyn) harray

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
  rw [encodeStorageAt_eq_storage_of_unowned hresolved hdyn
    (by simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots])]
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
  rw [encodeStorageAt_wordNormalize_eq_storage_of_unowned hresolved hdyn
    (by simp [SourceSemantics.writeAddressKeyedMapping2Slots])]
  simp only [SourceSemantics.writeAddressKeyedMapping2Slots]
  rw [Verity.ContractState.storage_writeMap2,
    Verity.ContractState.storage_withStorageChannel]
  simp only [List.foldl_cons, List.foldl_nil]
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
    · exact (hneq (hEq.trans (mapping2WordTargetSlot_eq_mod slot key1 key2 wordOffset).symm)).elim
    · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots, List.map_cons, List.map_nil]
      exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _
        (singleton_contains_false hEq)
  · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots,
      Verity.ContractState.storageAddr_writePhysicalSlots]
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
  rw [encodeStorageAt_wordNormalize_eq_storage_of_unowned hresolved hdyn
    (by simp [SourceSemantics.writeAddressKeyedMapping2WordSlots])]
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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  ·
    by_cases hEq : query = IRStorageSlot.ofNat slot
    · subst hEq
      rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = some f := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) = some f from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
      rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' hnotAddr hnotDyn]
      simp [SourceSemantics.writeUintSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (Nat.mod_eq_of_lt hvalue).symm
    · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      simp only [hEq, ↓reduceIte]
      rw [hstorage]
      exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (encodeStorageAt_writeUintSlots_singleton_other
          (IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem encodeStorageAt_writeStorageWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ slot % Compiler.Constants.evmModulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeStorageWordSlots world [slot] 0 value) query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp [SourceSemantics.writeStorageWordSlots, SourceSemantics.wordNormalize]
    exact Verity.ContractState.storage_writePhysicalSlots_not_mem _ _ _
      (singleton_contains_false hneq)
  · simp [SourceSemantics.writeStorageWordSlots, SourceSemantics.wordNormalize]
    rw [Verity.ContractState.storageAddr_writeAddrSlots_not_mem _ _ _
      (singleton_contains_false hneq)]
    rw [Verity.ContractState.storageAddr_writePhysicalSlots]
  · simp [SourceSemantics.writeStorageWordSlots]

private theorem runtimeStateMatchesIR_writeStorageWordSlot_zeroOffset
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
      { runtime with world := SourceSemantics.writeStorageWordSlots runtime.world [slot] 0 value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  ·
    by_cases hEq : query = IRStorageSlot.ofNat slot
    · subst hEq
      rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      have hresolved' :
          findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = some f := by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS] using
          (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) = some f from
            by rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)
      rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved' hnotAddr hnotDyn]
      simp [SourceSemantics.writeStorageWordSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (Nat.mod_eq_of_lt hvalue).symm
    · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      simp only [hEq, ↓reduceIte]
      rw [hstorage]
      symm
      refine congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat ?_
      have hneqNat' : query.toNat ≠ slot % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.wordNormalize] using
          IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq
      exact encodeStorageAt_writeStorageWordSlots_singleton_other hneqNat'

private theorem findResolvedFieldAtSlotCopy_ofNat_toNat
    {fields : List Field} {slot : Nat} {result : Option Field}
    (h : findResolvedFieldAtSlotCopy fields slot = result) :
    findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat = result := by
  rw [IRStorageSlot.toNat_ofNat_wordNormalize, findResolvedFieldAtSlotCopy_wordNormalize]
  exact h

private theorem encodeStorageAt_writeAddressSlots_singleton_other
    {fields : List Field} {world : Verity.ContractState} {slot query value : Nat}
    (hneq : query ≠ slot % Compiler.Constants.evmModulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressSlots world [slot] value) query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp [SourceSemantics.writeAddressSlots]
  · simp [SourceSemantics.writeAddressSlots, SourceSemantics.wordNormalize]
    exact Verity.ContractState.storageAddr_writeAddrSlots_not_mem _ _ _
      (singleton_contains_false hneq)
  · simp [SourceSemantics.writeAddressSlots]

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
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
    refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
    funext query
    by_cases hEq : query = IRStorageSlot.ofNat slot
    · subst hEq
      rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot
        (findResolvedFieldAtSlotCopy_ofNat_toNat hresolved) haddr hnotDyn]
      simp [SourceSemantics.writeAddressSlots, IRStorageSlot.toNat_ofNat_wordNormalize,
        SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Verity.wordToAddress, Verity.Core.Address.ofNat, Verity.Core.Uint256.val_ofNat,
        Verity.Core.Address.modulus, Compiler.Constants.addressMask]
      refine congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat ?_
      simpa [Compiler.Constants.addressMask, Verity.Core.Address.modulus,
        Verity.Core.ADDRESS_MODULUS, Nat.mod_eq_of_lt hvalue] using
        (Nat.and_two_pow_sub_one_eq_mod (n := 160) value)
    · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      simp only [hEq, ↓reduceIte]
      rw [hstorage]
      symm
      refine congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat ?_
      exact encodeStorageAt_writeAddressSlots_singleton_other (by
        simpa [SourceSemantics.wordNormalize] using
          IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)

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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  simp only [abstractStoreStorageOrMappingMany_eq]
  ·
      by_cases hmem : ∃ slot ∈ slots, query = IRStorageSlot.ofNat slot
      · simp only [hmem, ↓reduceIte]
        rcases hmem with ⟨slot, hslotMem, rfl⟩
        rw [encodeStorageAt_eq_storage_of_resolvedSlot
          (findResolvedFieldAtSlotCopy_ofNat_toNat (hresolved slot hslotMem)) hnotAddr hnotDyn]
        have hcontains :
              (slots.map SourceSemantics.wordNormalize).contains
                (SourceSemantics.wordNormalize slot) = true := by
            rw [List.contains_eq_mem]
            exact decide_eq_true (List.mem_map.mpr ⟨slot, hslotMem, rfl⟩)
        simp only [SourceSemantics.writeUintSlots, IRStorageSlot.toNat_ofNat_wordNormalize]
        rw [Verity.ContractState.storage_writePhysicalSlots_mem _ _ _ hcontains]
        simp only [Verity.Core.Uint256.val_ofNat]
        exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (Nat.mod_eq_of_lt hvalue).symm
      · simp only [hmem, ↓reduceIte]
        rw [hstorage]
        have hnotMem : query.toNat ∉ slots.map SourceSemantics.wordNormalize := by
          intro hq
          rcases List.mem_map.mp hq with ⟨slot, hslotMem, hslotEq⟩
          apply hmem
          exact ⟨slot, hslotMem, IRStorageSlot.eq_of_toNat_eq (by
            simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
              Verity.Core.UINT256_MODULUS] using hslotEq.symm)⟩
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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot slot key)
  · subst hEq
    simp only [↓reduceIte]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS,
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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, ?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  · funext query
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorageAt_congr
        (by simp [SourceSemantics.writeTransientTargets])
        (by simp [SourceSemantics.writeTransientTargets])
        (by simp [SourceSemantics.writeTransientTargets]))
  · funext slot
    by_cases hslot : slot = SourceSemantics.wordNormalize target
    · subst hslot
      simp [SourceSemantics.writeTransientTargets]
      exact (Nat.mod_eq_of_lt (by
        simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
          Verity.Core.Uint256.modulus] using hvalue)).symm
    · have hslot' : slot ≠ target % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.wordNormalize] using hslot
      simp [SourceSemantics.writeTransientTargets, hslot, hslot']
      exact congrFun htransient slot

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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (SourceSemantics.mappingSlotChain slot keys)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hstorage, encodeStorageAt_eq_storage_of_unowned hresolved hdyn rfl]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS,
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

/-- `writeAddressKeyedMappingSlots` has the same storage/storageAddr/storageArray as
`writeUintKeyedMappingSlots`, so `encodeStorageAt` agrees on both. -/
private theorem encodeStorageAt_writeAddressKeyedMappingSlots_eq_uint
    {fields : List Field} {world : Verity.ContractState} {slot key value q : Nat} :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingSlots world [slot] key value) q =
      SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value) q := by
  apply SourceSemantics.encodeStorageAt_congr <;>
    simp [SourceSemantics.writeAddressKeyedMappingSlots,
      SourceSemantics.writeUintKeyedMappingSlots]

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
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  rw [encodeStorageAt_writeAddressKeyedMappingSlots_eq_uint]
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot slot key)
  · subst hEq
    simp only [↓reduceIte]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
        simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS,
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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hstorage, encodeStorageAt_eq_storage_of_unowned hresolved hdyn rfl]
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

private theorem mappingWordTargetSlot_lt_lit (slot key wordOffset : Nat) :
    mappingWordTargetSlot slot key wordOffset <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  simpa [mappingWordTargetSlot, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
    using SourceSemantics.wordNormalize_lt_evmModulus
      (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)

private theorem uint256_val_lt_lit (x : Verity.Core.Uint256) :
    x.val < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using x.isLt

private theorem IRStorageSlot.toNat_ofNat_mappingWordTargetSlot (slot key wordOffset : Nat) :
    (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)).toNat =
      mappingWordTargetSlot slot key wordOffset := by
  rw [IRStorageSlot.toNat_ofNat_wordNormalize]
  exact SourceSemantics.wordNormalize_idem _

private theorem abstractStoreStorageOrMapping_packedWord_hit
    {fields : List Field} {world : Verity.ContractState}
    {storage : IRStorageSlot → IRStorageWord}
    {slot key wordOffset value : Nat} {packed : PackedBits}
    (hstorage : storage = fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorageAt fields world s.toNat))
    (hresolved :
      findResolvedFieldAtSlotCopy fields (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mappingWordTargetSlot slot key wordOffset) = none) :
    Compiler.Proofs.abstractStoreStorageOrMapping storage
      (mappingWordTargetSlot slot key wordOffset)
      (SourceSemantics.packedWordWrite
        (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
          (storage (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset))))
        value packed)
      (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)) =
    Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
          world [slot] key wordOffset packed value)
        (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)).toNat) := by
  rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
  have hencNorm : SourceSemantics.encodeStorageAt fields world
      (IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)).toNat =
        (world.storage (mappingWordTargetSlot slot key wordOffset)).val := by
    rw [IRStorageSlot.toNat_ofNat_mappingWordTargetSlot]
    exact encodeStorageAt_eq_storage_of_unowned hresolved hdyn rfl
  simp only [hstorage, hencNorm]
  simp [IRStorageWord.toNat_ofNat, EvmYul.UInt256.size, Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt (world.storage (mappingWordTargetSlot slot key wordOffset)).isLt]
  exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (by
    simpa [Nat.mod_eq_of_lt (mappingWordTargetSlot_lt_lit slot key wordOffset),
      Nat.mod_eq_of_lt (uint256_val_lt_lit _)] using
      (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
        (packed := packed) (value := value) hresolved hdyn).symm)

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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (mappingWordTargetSlot slot key wordOffset)
  · subst hEq
    exact abstractStoreStorageOrMapping_packedWord_hit hstorage hresolved hdyn
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]; rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
        (fields := fields) (world := runtime.world) (slot := slot) (key := key)
          (wordOffset := wordOffset) (packed := packed) (query := query.toNat) (value := value)
          (by simpa [mappingWordTargetSlot] using
            IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq)).symm

private theorem encodeStorageAt_writeAddressKeyedMapping2Slots_ofNat_eq_written
    {fields : List Field} {world : Verity.ContractState} {slot key1 key2 value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1) key2) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1) key2) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    value = SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2)).toNat := by
  rw [Compiler.Proofs.abstractMappingSlot_eq_solidity] at hresolved hdyn
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS, Compiler.Proofs.abstractMappingSlot_eq_solidity,
    SourceSemantics.wordNormalize_idem] using
    (encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
      (slot := slot) (key1 := key1) (key2 := key2) hresolved hdyn hvalue).symm

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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query =
      (IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2))
  · subst hEq
    simp only [↓reduceIte]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (encodeStorageAt_writeAddressKeyedMapping2Slots_ofNat_eq_written hresolved hdyn hvalue)
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
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat (mapping2WordTargetSlot slot key1 key2 wordOffset)
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hstorage, encodeStorageAt_eq_storage_of_unowned hresolved hdyn rfl]
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
        YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name]))) =
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
            (YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name])) =
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
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident tempName]))) =
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

/-- A compiled core expression has a word-bounded source value that its IR evaluates to. -/
private theorem exists_eval_of_compileExpr_core_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {expr : Expr} {exprIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hIR : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    ∃ n, SourceSemantics.evalExpr fields runtime expr = some n ∧
      evalIRExpr state exprIR = some n ∧ n < Compiler.Constants.evmModulus := by
  have h := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope hbounded
    (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rw [hIR] at h
  cases hir : evalIRExpr state exprIR with
  | none => simp [Except.toOption, hir] at h
  | some n =>
    have hsrc : SourceSemantics.evalExpr fields runtime expr = some n := by
      simpa [Except.toOption, hir] using h.symm
    have hlt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hsrc] at hlt
    exact ⟨n, hsrc, rfl, by simpa using hlt⟩

private theorem reservedScratch_not_mem_scope_of_validateIdentifierShapes
    {spec : CompilationModel} {fn : FunctionSpec} {scope : List String} {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hscopeNames :
      ∀ name, name ∈ scope →
        name ∈
          (fn.params.map (·.name) ++
            collectStmtListBindNames fn.body ++
            collectStmtListAssignedNames fn.body ++
            spec.fields.map (·.name)))
    (hreserved :
      name = "__compat_value" ∨ name = "__compat_packed" ∨
        name = "__compat_slot_word" ∨ name = "__compat_slot_cleared") :
    name ∉ scope := by
  intro hmem
  have hname :
      name ∈ fn.params.map (·.name) ∨ name ∈ collectStmtListBindNames fn.body ∨
        name ∈ collectStmtListAssignedNames fn.body ∨ name ∈ spec.fields.map (·.name) := by
    simpa [List.mem_append, or_assoc] using hscopeNames name hmem
  have hprefix := compatScratch_startsWith_reserved hreserved
  rcases hname with hparam | hlocal | hassign | hfield
  · exact (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
      hvalidate hfn hparam) hprefix
  · exact (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
      hvalidate hfn hlocal) hprefix
  · exact
      (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
        hvalidate hfn hassign) hprefix
  · have hne := validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield
    rcases hreserved with rfl | rfl | rfl | rfl
    · exact hne.1 rfl
    · exact hne.2.1 rfl
    · exact hne.2.2.1 rfl
    · exact hne.2.2.2 rfl

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
    scopeAvoidsReservedCompilerPrefix scope :=
  ⟨reservedScratch_not_mem_scope_of_validateIdentifierShapes hvalidate hfn hscopeNames
      (Or.inl rfl),
    reservedScratch_not_mem_scope_of_validateIdentifierShapes hvalidate hfn hscopeNames
      (Or.inr (Or.inl rfl)),
    reservedScratch_not_mem_scope_of_validateIdentifierShapes hvalidate hfn hscopeNames
      (Or.inr (Or.inr (Or.inl rfl))),
    reservedScratch_not_mem_scope_of_validateIdentifierShapes hvalidate hfn hscopeNames
      (Or.inr (Or.inr (Or.inr rfl)))⟩

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

/-- A single `sstore` of an evaluated expression to a literal slot continues with that
slot overwritten. -/
private theorem execIRStmts_sstore_lit_single
    {state : IRState} {slot extraFuel valueNat : Nat} {valueIR : YulExpr}
    (hIRValue : evalIRExpr state valueIR = some valueNat) :
    execIRStmts ([YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])].length +
        extraFuel + 1) state
      [YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot valueNat } := by
  have hExecStmt :=
    execIRStmt_sstore_lit_expr_succ_of_eval extraFuel state slot valueIR valueNat hIRValue
  have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
  simp [execIRStmts, hfuelEq, hExecStmt]

/-- Close a compiled step whose source and IR sides both continue without touching the
source bindings or the IR variables, once the post-states are known to match. -/
private theorem stmtStep_continue_of_vars_eq
    {fields : List Field} {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt}
    {runtime runtime' : SourceSemantics.RuntimeState} {state state' : IRState} {fuel : Nat}
    (hSrc : SourceSemantics.execStmt fields runtime stmt = .continue runtime')
    (hIR : execIRStmts fuel state compiledIR = .continue state')
    (hbindings : runtime'.bindings = runtime.bindings)
    (hvars : state'.vars = state.vars)
    (hincl : FunctionBody.scopeNamesIncluded (stmtNextScope scope stmt) scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime' state') :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
      execIRStmts fuel state compiledIR = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec := by
  refine ⟨.continue runtime', .continue state', hSrc, hIR, ?_⟩
  have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime'.bindings state' := by
    intro name hname
    simpa [IRState.getVar, hvars, hbindings] using hexact name hname
  refine ⟨hmatch, FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact' hincl,
    ?_, ?_⟩
  · rw [hbindings]
    exact hbounded
  · rw [hbindings]
    exact FunctionBody.scopeNamesPresent_of_included hscope hincl

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
      [YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetStorage,
      hNotMapping, hfind, halias, hunpacked, hnotTransient, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ := by
    obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ :=
      exists_eval_of_compileExpr_core_of_scope hcore hinScope hexact hscope hbounded hruntime
        hvalueIR
    have hfieldTransient : SourceSemantics.fieldIsTransient fields fieldName = false := by
      simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
    have hSrcExec : SourceSemantics.execStmt fields runtime (.setStorage fieldName value) =
        .continue { runtime with
          world := SourceSemantics.writeUintSlots runtime.world [slot] valueNat } := by
      simp [SourceSemantics.execStmt, SourceSemantics.writeUintFieldSlots,
        SourceSemantics.writeMappingTargets, hwriteSlots, hValueSrc, hfieldTransient,
        hfind, hunpacked, hnotTransient]
    exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_sstore_lit_single hIRValue) rfl rfl
      (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
      hexact hscope hbounded
      (runtimeStateMatchesIR_writeUintSlot hruntime
        (findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
          hnoConflict hfind hwriteSlots hnotTransient hunpacked)
        hnotAddr hnotDyn hvalueLt)

theorem compiledStmtStep_setStorageWord_singleSlot_zeroOffset
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
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorageWord fieldName 0 value)
      [YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hfind, halias, hnotTransient, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ := by
    obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ :=
      exists_eval_of_compileExpr_core_of_scope hcore hinScope hexact hscope hbounded hruntime
        hvalueIR
    have hfieldTransient : SourceSemantics.fieldIsTransient fields fieldName = false := by
      simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
    have hSrcExec : SourceSemantics.execStmt fields runtime (.setStorageWord fieldName 0 value) =
        .continue { runtime with
          world := SourceSemantics.writeStorageWordSlots runtime.world [slot] 0 valueNat } := by
      simp [SourceSemantics.execStmt, SourceSemantics.writeStorageWordFieldSlots,
        hwriteSlots, hValueSrc, hfieldTransient]
    exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_sstore_lit_single hIRValue) rfl rfl
      (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
      hexact hscope hbounded
      (runtimeStateMatchesIR_writeStorageWordSlot_zeroOffset hruntime
        (findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
          hnoConflict hfind hwriteSlots hnotTransient hunpacked)
        hnotAddr hnotDyn hvalueLt)

/-- Masking an evaluated word with the address mask evaluates to the masked word. -/
private theorem evalIRExpr_and_addressMask_of_eval
    {state : IRState} {valueIR : YulExpr} {valueNat : Nat}
    (hIRValue : evalIRExpr state valueIR = some valueNat)
    (hvalueLt : valueNat < Compiler.Constants.evmModulus) :
    evalIRExpr state
        (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
      some (valueNat &&& Compiler.Constants.addressMask) := by
  have hMaskedEvalRaw :
      evalIRExpr state
        (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
          some ((valueNat % Compiler.Constants.evmModulus) &&&
            (Compiler.Constants.addressMask % Compiler.Constants.evmModulus)) := by
    simpa using FunctionBody.evalIRExpr_and_of_eval (state := state) (lhs := valueIR)
      (rhs := YulExpr.hex Compiler.Constants.addressMask) (b := Compiler.Constants.addressMask)
      hIRValue (by simp [evalIRExpr, Compiler.Constants.addressMask])
  simpa [Nat.mod_eq_of_lt hvalueLt, Compiler.Constants.addressMask,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hMaskedEvalRaw

/-- Compiled IR for a single-slot address store: `sstore(slot, and(value, addressMask))`. -/
private def sstoreAddressMaskedIR (slot : Nat) (valueIR : YulExpr) : List YulStmt :=
  [YulStmt.exprStmt
    (YulExpr.call "sstore"
      [YulExpr.lit slot,
        YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])]

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
      sizeOf (sstoreAddressMaskedIR slot valueIR) - (sstoreAddressMaskedIR slot valueIR).length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setStorageAddr fieldName value) = sourceResult ∧
        execIRStmts ((sstoreAddressMaskedIR slot valueIR).length + extraFuel + 1) state
            (sstoreAddressMaskedIR slot valueIR) = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStorageAddr fieldName value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcore hinScope hexact hscope hbounded hruntime
      hvalueIR
  have hfieldTransient : SourceSemantics.fieldIsTransient fields fieldName = false := by
    simp [SourceSemantics.fieldIsTransient, hfind]
  have hSrcExec : SourceSemantics.execStmt fields runtime (.setStorageAddr fieldName value) =
      .continue { runtime with
        world := SourceSemantics.writeAddressSlots runtime.world [slot] valueNat } := by
    simp [SourceSemantics.execStmt, SourceSemantics.writeAddressFieldSlots,
      hwriteSlots, hValueSrc, hfieldTransient]
  exact stmtStep_continue_of_vars_eq hSrcExec
    (execIRStmts_sstore_lit_single (evalIRExpr_and_addressMask_of_eval hIRValue hvalueLt))
    rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded
    (runtimeStateMatchesIR_writeAddressSlot hruntime
      (findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
        hnoConflict hfind hwriteSlots (by rfl) (by rfl))
      (by rfl) (by rfl) hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call "sstore"
          [YulExpr.lit slot,
            YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] where
  compileOk := by
    have hNotMapping : isMapping fields fieldName = false :=
      isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetStorage,
      hNotMapping, hfind, hwriteSlots, hvalueIR]
  preserves := compiledStmtStep_setStorageAddr_singleSlot_preserves
    hcore hinScope hfind hwriteSlots hnoConflict hvalueIR

/-- The `preserves` obligation of `CompiledStmtStep` for one statement and its IR. -/
private def CompiledStmtPreserves
    (fields : List Field) (scope : List String) (stmt : Stmt) (compiledIR : List YulStmt) :
    Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (extraFuel : Nat),
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    sizeOf compiledIR - compiledIR.length ≤ extraFuel →
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
      execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- A singleton IR statement list continues exactly when its statement does. -/
private theorem execIRStmts_single_of_execIRStmt
    {state state' : IRState} {stmt : YulStmt} {extraFuel : Nat}
    (h : execIRStmt (extraFuel + 1) state stmt = .continue state') :
    execIRStmts ([stmt].length + extraFuel + 1) state [stmt] = .continue state' := by
  have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
  simp [execIRStmts, hfuelEq, h]

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
    CompiledStmtPreserves fields scope (.mstore offset value)
      [YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨offsetNat, hOffsetSrc, hIROffset, hOffsetLt⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreOffset hinScopeOffset hexact hscope hbounded
      hruntime hoffsetIR
  obtain ⟨valueNat, hValueSrc, hIRValue, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreValue hinScopeValue hexact hscope hbounded
      hruntime hvalueIR
  have hSrcExec : SourceSemantics.execStmt fields runtime (.mstore offset value) =
      .continue { runtime with
        world := runtime.world.writePhysicalMemoryValue offsetNat valueNat } := by
    simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
  have hExecStmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])) =
          .continue (state.writePhysicalMemoryValue offsetNat valueNat) := by
    simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, Nat.mod_eq_of_lt hOffsetLt]
  exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_single_of_execIRStmt hExecStmt)
    rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded
    (FunctionBody.runtimeStateMatchesIR_writePhysicalMemoryValue hruntime offsetNat valueNat)

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
      [YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])] where
  compileOk := by
    have hoffsetIRInternal := compileExprWithInternals_nil_ok hoffsetIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hoffsetIRInternal, hvalueIRInternal, Bind.bind, Except.bind, pure, Except.pure]
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
    CompiledStmtPreserves fields scope (.tstore offset value)
      [YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨offsetNat, hOffsetSrc, hIROffset, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreOffset hinScopeOffset hexact hscope hbounded
      hruntime hoffsetIR
  obtain ⟨valueNat, hValueSrc, hIRValue, hValueLt⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreValue hinScopeValue hexact hscope hbounded
      hruntime hvalueIR
  have hSrcExec : SourceSemantics.execStmt fields runtime (.tstore offset value) =
      .continue { runtime with
        world := runtime.world.writeTransient
          (offsetNat % Compiler.Constants.evmModulus) valueNat } := by
    simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
  have hExecStmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])) =
          .continue { state with
            transientStorage := fun o =>
              if o = offsetNat % Compiler.Constants.evmModulus then valueNat
              else state.transientStorage o } := by
    simp [execIRStmt, evalIRExprs, hIROffset, hIRValue]
  exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_single_of_execIRStmt hExecStmt)
    rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded
    (FunctionBody.runtimeStateMatchesIR_setTransientStorage hruntime
      (offsetNat % Compiler.Constants.evmModulus) valueNat hValueLt)

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
      [YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])] where
  compileOk := by
    have hoffsetIRInternal := compileExprWithInternals_nil_ok hoffsetIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hoffsetIRInternal, hvalueIRInternal, Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_tstore_single_preserves
    hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

private theorem compiledStmtStep_calldatacopy_single_preserves
    {fields : List Field}
    {scope : List String}
    {destOffset sourceOffset size : Expr}
    {destIR sourceIR sizeIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR)
    (hsourceIR : CompilationModel.compileExpr fields .calldata sourceOffset = Except.ok sourceIR)
    (hsizeIR : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR) :
    CompiledStmtPreserves fields scope (.calldatacopy destOffset sourceOffset size)
      [YulStmt.exprStmt (YulExpr.call "calldatacopy" [destIR, sourceIR, sizeIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨destNat, hDestSrc, hIRDest, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreDest hinScopeDest hexact hscope hbounded
      hruntime hdestIR
  obtain ⟨sourceNat, hSourceSrc, hIRSource, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreSource hinScopeSource hexact hscope hbounded
      hruntime hsourceIR
  obtain ⟨sizeNat, hSizeSrc, hIRSize, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreSize hinScopeSize hexact hscope hbounded
      hruntime hsizeIR
  have hSrcExec : SourceSemantics.execStmt fields runtime
      (.calldatacopy destOffset sourceOffset size) = .continue { runtime with
        world := { runtime.world with
          memory := fun o =>
            if Compiler.Proofs.YulGeneration.calldatacopyWritesAt destNat sizeNat o then
              Verity.Core.Uint256.ofNat
                (Compiler.Proofs.YulGeneration.calldataloadWord
                  runtime.selector runtime.world.calldata (sourceNat + (o - destNat)))
            else runtime.world.memory o } } := by
    simp [SourceSemantics.execStmt, hDestSrc, hSourceSrc, hSizeSrc]
  have hExecStmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt (YulExpr.call "calldatacopy" [destIR, sourceIR, sizeIR])) =
          .continue { state with
            memory := Compiler.Proofs.YulGeneration.calldatacopyMemory
              state.selector state.calldata destNat sourceNat sizeNat state.memory } := by
    simp [execIRStmt, hIRDest, hIRSource, hIRSize]
  exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_single_of_execIRStmt hExecStmt)
    rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded
    (FunctionBody.runtimeStateMatchesIR_calldatacopyBothMemory hruntime destNat sourceNat sizeNat)

theorem compiledStmtStep_calldatacopy_single
    {fields : List Field}
    {scope : List String}
    {destOffset sourceOffset size : Expr}
    {destIR sourceIR sizeIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR)
    (hsourceIR : CompilationModel.compileExpr fields .calldata sourceOffset = Except.ok sourceIR)
    (hsizeIR : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR) :
    CompiledStmtStep fields scope (.calldatacopy destOffset sourceOffset size)
      [YulStmt.exprStmt (YulExpr.call "calldatacopy" [destIR, sourceIR, sizeIR])] where
  compileOk := by
    have hdestIRInternal := compileExprWithInternals_nil_ok hdestIR
    have hsourceIRInternal := compileExprWithInternals_nil_ok hsourceIR
    have hsizeIRInternal := compileExprWithInternals_nil_ok hsizeIR
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hdestIRInternal, hsourceIRInternal, hsizeIRInternal, Bind.bind, Except.bind, pure,
      Except.pure]
  preserves := compiledStmtStep_calldatacopy_single_preserves
    hcoreDest hinScopeDest hcoreSource hinScopeSource hcoreSize hinScopeSize
    hdestIR hsourceIR hsizeIR

private theorem compiledStmtStep_returndatacopy_empty_single_preserves
    {fields : List Field}
    {scope : List String}
    {destOffset : Expr}
    {destIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR) :
    CompiledStmtPreserves fields scope (.returndataCopy destOffset (.literal 0) (.literal 0))
      [YulStmt.exprStmt
        (YulExpr.call "returndatacopy" [destIR, YulExpr.lit 0, YulExpr.lit 0])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨destNat, hDestSrc, hIRDest, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreDest hinScopeDest hexact hscope hbounded
      hruntime hdestIR
  -- The zero-extent copy fits any buffer and writes no memory word, so both
  -- the source semantics and the IR interpreter leave their states alone.
  have hzeroNoWrite : ∀ o,
      ¬Compiler.Proofs.YulGeneration.calldatacopyWritesAt destNat 0 o := by
    intro o hwall
    obtain ⟨_, h2, _⟩ := hwall
    simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at h2
    omega
  have hSrcExec : SourceSemantics.execStmt fields runtime
      (.returndataCopy destOffset (.literal 0) (.literal 0)) = .continue runtime := by
    simp [SourceSemantics.execStmt, SourceSemantics.evalExpr, hDestSrc, Nat.zero_le,
      hzeroNoWrite]
  have hExecStmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt
          (YulExpr.call "returndatacopy" [destIR, YulExpr.lit 0, YulExpr.lit 0])) =
          .continue state := by
    simp [execIRStmt, evalIRExpr, hIRDest, Nat.zero_le]
  exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_single_of_execIRStmt hExecStmt)
    rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded hruntime

theorem compiledStmtStep_returndatacopy_empty_single
    {fields : List Field}
    {scope : List String}
    {destOffset : Expr}
    {destIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR) :
    CompiledStmtStep fields scope (.returndataCopy destOffset (.literal 0) (.literal 0))
      [YulStmt.exprStmt
        (YulExpr.call "returndatacopy" [destIR, YulExpr.lit 0, YulExpr.lit 0])] where
  compileOk := by
    have hdestIRInternal := compileExprWithInternals_nil_ok hdestIR
    have hzero : CompilationModel.compileExpr fields .calldata (Expr.literal 0) =
        Except.ok (YulExpr.lit 0) := by
      rw [← CompilationModel.compileExprWithInternals_nil_eq]
      simp [-CompilationModel.compileExprWithInternals_nil_eq,
        CompilationModel.compileExprWithInternals, pure, Except.pure]
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hdestIRInternal, hzero, Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_returndatacopy_empty_single_preserves
    hcoreDest hinScopeDest hdestIR

private theorem execStmt_returndataCopy_of_eval
    {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {destOffset sourceOffset size : Expr} {destNat sourceNat sizeNat : Nat}
    (hDestSrc : SourceSemantics.evalExpr fields runtime destOffset = some destNat)
    (hSourceSrc : SourceSemantics.evalExpr fields runtime sourceOffset = some sourceNat)
    (hSizeSrc : SourceSemantics.evalExpr fields runtime size = some sizeNat) :
    SourceSemantics.execStmt fields runtime (.returndataCopy destOffset sourceOffset size) =
      if sourceNat + sizeNat ≤ 32 * runtime.world.returndata.length then
        .continue { runtime with
          world := { runtime.world with
            memory := Compiler.Proofs.IRGeneration.returndatacopyMemoryPaddedUint256
              runtime.world.returndata destNat sourceNat sizeNat runtime.world.memory } }
      else .revert := by
  by_cases hfit : sourceNat + sizeNat ≤ 32 * runtime.world.returndata.length <;>
    simp [SourceSemantics.execStmt, hDestSrc, hSourceSrc, hSizeSrc, hfit]

private theorem execIRStmt_returndatacopy_of_eval
    {state : IRState} {destIR sourceIR sizeIR : YulExpr} {destNat sourceNat sizeNat : Nat}
    {extraFuel : Nat}
    (hIRDest : evalIRExpr state destIR = some destNat)
    (hIRSource : evalIRExpr state sourceIR = some sourceNat)
    (hIRSize : evalIRExpr state sizeIR = some sizeNat) :
    execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt (YulExpr.call "returndatacopy" [destIR, sourceIR, sizeIR])) =
      if sourceNat + sizeNat ≤ 32 * state.returndata.length then
        .continue { state with
          memory := Compiler.Proofs.IRGeneration.returndatacopyMemoryPadded
            state.returndata destNat sourceNat sizeNat state.memory }
      else .revert state := by
  by_cases hfit : sourceNat + sizeNat ≤ 32 * state.returndata.length <;>
    simp [execIRStmt, hIRDest, hIRSource, hIRSize, hfit]

/-- A singleton IR statement list reverts exactly when its statement does. -/
private theorem execIRStmts_single_revert_of_execIRStmt
    {state state' : IRState} {stmt : YulStmt} {extraFuel : Nat}
    (h : execIRStmt (extraFuel + 1) state stmt = .revert state') :
    execIRStmts ([stmt].length + extraFuel + 1) state [stmt] = .revert state' := by
  have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
  simp [execIRStmts, hfuelEq, h]

/-- Both layers branch on the same fit guard (the buffers agree by
`runtimeStateMatchesIR_returndata`), so the step corresponds in either branch: the
in-bounds copy continues with the same words, the out-of-bounds extent reverts on
both sides. -/
private theorem compiledStmtStep_returndatacopy_bounded_single_preserves
    {fields : List Field} {scope : List String} {destOffset sourceOffset size : Expr}
    {destIR sourceIR sizeIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR)
    (hsourceIR : CompilationModel.compileExpr fields .calldata sourceOffset = Except.ok sourceIR)
    (hsizeIR : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR) :
    CompiledStmtPreserves fields scope (.returndataCopy destOffset sourceOffset size)
      [YulStmt.exprStmt (YulExpr.call "returndatacopy" [destIR, sourceIR, sizeIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _
  obtain ⟨destNat, hDestSrc, hIRDest, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreDest hinScopeDest hexact hscope hbounded
      hruntime hdestIR
  obtain ⟨sourceNat, hSourceSrc, hIRSource, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreSource hinScopeSource hexact hscope hbounded
      hruntime hsourceIR
  obtain ⟨sizeNat, hSizeSrc, hIRSize, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcoreSize hinScopeSize hexact hscope hbounded
      hruntime hsizeIR
  have hSrcExec := execStmt_returndataCopy_of_eval hDestSrc hSourceSrc hSizeSrc
  have hExecStmt :=
    execIRStmt_returndatacopy_of_eval (extraFuel := extraFuel) hIRDest hIRSource hIRSize
  have hrd := FunctionBody.runtimeStateMatchesIR_returndata hruntime
  by_cases hfit : sourceNat + sizeNat ≤ 32 * runtime.world.returndata.length
  · rw [if_pos hfit] at hSrcExec
    rw [if_pos (show sourceNat + sizeNat ≤ 32 * state.returndata.length from hrd ▸ hfit)]
      at hExecStmt
    exact stmtStep_continue_of_vars_eq hSrcExec (execIRStmts_single_of_execIRStmt hExecStmt)
      rfl rfl (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
      hexact hscope hbounded
      (FunctionBody.runtimeStateMatchesIR_returndatacopyBothMemory hruntime
        destNat sourceNat sizeNat)
  · rw [if_neg hfit] at hSrcExec
    rw [if_neg (show ¬(sourceNat + sizeNat ≤ 32 * state.returndata.length) from hrd ▸ hfit)]
      at hExecStmt
    exact ⟨_, _, hSrcExec, execIRStmts_single_revert_of_execIRStmt hExecStmt, trivial⟩

/-- Bounded `returndataCopy` correspondence: the compiled single
`returndatacopy(destIR, sourceIR, sizeIR)` step agrees with the source
semantics for every extent — in-bounds copies continue with the same
word-granular memory (via `runtimeStateMatchesIR_returndatacopyBothMemory`),
out-of-bounds extents revert on both layers. This is the ready-made consumer
for the follow-up fragment-widening slice; no supported-surface predicate is
relaxed here. -/
theorem compiledStmtStep_returndatacopy_bounded_single
    {fields : List Field}
    {scope : List String}
    {destOffset sourceOffset size : Expr}
    {destIR sourceIR sizeIR : YulExpr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope)
    (hdestIR : CompilationModel.compileExpr fields .calldata destOffset = Except.ok destIR)
    (hsourceIR : CompilationModel.compileExpr fields .calldata sourceOffset = Except.ok sourceIR)
    (hsizeIR : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR) :
    CompiledStmtStep fields scope (.returndataCopy destOffset sourceOffset size)
      [YulStmt.exprStmt (YulExpr.call "returndatacopy" [destIR, sourceIR, sizeIR])] where
  compileOk := by
    have hdestIRInternal := compileExprWithInternals_nil_ok hdestIR
    have hsourceIRInternal := compileExprWithInternals_nil_ok hsourceIR
    have hsizeIRInternal := compileExprWithInternals_nil_ok hsizeIR
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hdestIRInternal, hsourceIRInternal, hsizeIRInternal, Bind.bind, Except.bind, pure,
      Except.pure]
  preserves := compiledStmtStep_returndatacopy_bounded_single_preserves
    hcoreDest hinScopeDest hcoreSource hinScopeSource hcoreSize hinScopeSize
    hdestIR hsourceIR hsizeIR

/-- Direct empty revert has no memory or returndata premise. This coarse IR
step agreement complements the byte-exact Denote/frame lemmas. -/
theorem compiledStmtStep_revertEmpty_single
    {fields : List Field} {scope : List String} :
    CompiledStmtStep fields scope .revertEmpty
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      pure, Except.pure]
  preserves := by
    intro runtime state extraFuel _ _ _ _ _
    refine ⟨.revert, .revert state, rfl, ?_, trivial⟩
    have hfuel : 1 + extraFuel + 1 = Nat.succ (Nat.succ extraFuel) := by omega
    change execIRStmts (1 + extraFuel + 1) state
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] = .revert state
    rw [hfuel]
    exact EmptyRevert.ir_exact state extraFuel

/-- Compiled IR for `revertReturndata`: copy the whole returndata buffer to memory
and revert with it. -/
private def revertReturndataIR : List YulStmt :=
  [YulStmt.block [
    YulStmt.let_ "__returndata_size" (YulExpr.call "returndatasize" []),
    YulStmt.exprStmt (YulExpr.call "returndatacopy"
      [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__returndata_size"]),
    YulStmt.exprStmt (YulExpr.call "revert"
      [YulExpr.lit 0, YulExpr.ident "__returndata_size"])
  ]]

private theorem execIRStmt_revert_returndataSize (n : Nat) (s : IRState) :
    execIRStmt n s (YulStmt.exprStmt (YulExpr.call "revert"
      [YulExpr.lit 0, YulExpr.ident "__returndata_size"])) = .revert s := by
  cases n <;> simp [execIRStmt]

/-- Whichever branch the copy takes for the current EIP-211 buffer — the in-bounds
copy continues with a memory update, the out-of-bounds extent reverts immediately —
the trailing `revert` lands the frame in a reverted state, so only the
reverted-ness is pinned here. -/
private theorem execIRStmts_revertReturndataIR_revert (k : Nat) (state : IRState) :
    ∃ s, execIRStmts (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ k))))) state
      revertReturndataIR = .revert s := by
  simp [revertReturndataIR, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    IRState.getVar, IRState.setVar, execIRStmt_revert_returndataSize]
  split_ifs <;> exact ⟨_, rfl⟩

/-- `revertReturndata` bubbles the callee's revert reason.  The compiler's
temporary is exactly `returndatasize()`; whichever branch the copy takes for the
current EIP-211 buffer, both it and the following `revert` land in
`IRExecResult.revert`, matching the source statement's `.revert`. -/
private theorem compiledStmtStep_revertReturndata_empty_single_preserves
    {fields : List Field}
    {scope : List String} :
    CompiledStmtPreserves fields scope .revertReturndata revertReturndataIR := by
  intro runtime state extraFuel _ _ _ _ hslack
  have h3 : 3 ≤ extraFuel := by
    have : 4 ≤ sizeOf revertReturndataIR := by decide
    have : revertReturndataIR.length = 1 := rfl
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h3
  have hfuel : revertReturndataIR.length + (3 + k) + 1 =
      Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ k)))) := by
    have : revertReturndataIR.length = 1 := rfl
    omega
  rw [hfuel]
  obtain ⟨s, hs⟩ := execIRStmts_revertReturndataIR_revert k state
  exact ⟨.revert, .revert s, rfl, hs, trivial⟩

theorem compiledStmtStep_revertReturndata_empty_single
    {fields : List Field} {scope : List String} :
    CompiledStmtStep fields scope .revertReturndata
      [YulStmt.block [
        YulStmt.let_ "__returndata_size" (YulExpr.call "returndatasize" []),
        YulStmt.exprStmt (YulExpr.call "returndatacopy"
          [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__returndata_size"]),
        YulStmt.exprStmt (YulExpr.call "revert"
          [YulExpr.lit 0, YulExpr.ident "__returndata_size"])
      ]] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      pure, Except.pure]
  preserves := compiledStmtStep_revertReturndata_empty_single_preserves

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
      (Compiler.Yul.YulStmt.exprStmt (Compiler.Yul.YulExpr.call "sstore"
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
      (Compiler.Yul.YulStmt.exprStmt (Compiler.Yul.YulExpr.call "tstore"
        [slotExpr, valueExpr])) =
      .continue { state with
        transientStorage := fun slot =>
          if slot = slotVal % Compiler.Constants.evmModulus then valueVal
          else state.transientStorage slot } := by
    simp [execIRStmt, hslot, hvalue]

/-- The word a field load (`sload`/`tload`) reads at `target` from the field's channel. -/
private def irFieldWord (fields : List Field) (fieldName : String) (state : IRState)
    (target : Nat) : Nat :=
  if SourceSemantics.fieldIsTransient fields fieldName then
    state.transientStorage (SourceSemantics.wordNormalize target)
  else
    Compiler.Proofs.IRGeneration.IRStorageWord.toNat (state.storage (IRStorageSlot.ofNat target))

/-- The IR state after a field store (`sstore`/`tstore`) of `value` at `target`. -/
private def irFieldStore (fields : List Field) (fieldName : String) (state : IRState)
    (target value : Nat) : IRState :=
  if SourceSemantics.fieldIsTransient fields fieldName then
    { state with transientStorage := fun o =>
        if o = SourceSemantics.wordNormalize target then value else state.transientStorage o }
  else
    { state with storage :=
        Compiler.Proofs.abstractStoreStorageOrMapping state.storage target value }

private theorem evalIRExpr_fieldLoad_of_eval {fields : List Field} {fieldName : String}
    {state : IRState} {slotExpr : YulExpr} {target : Nat}
    (hslot : evalIRExpr state slotExpr = some target) :
    evalIRExpr state (YulExpr.call (fieldLoadBuiltin fields fieldName) [slotExpr]) =
      some (irFieldWord fields fieldName state target) := by
  unfold irFieldWord
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName <;>
    simp [evalIRExpr, evalIRCall, evalIRExprs, fieldLoadBuiltin, htrans, hslot,
      SourceSemantics.wordNormalize,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

private theorem execIRStmt_fieldStore_of_eval {fields : List Field} {fieldName : String}
    {state : IRState} {slotExpr valueExpr : YulExpr} {target value fuel : Nat}
    (hslot : evalIRExpr state slotExpr = some target)
    (hvalue : evalIRExpr state valueExpr = some value) :
    execIRStmt (fuel + 1) state
      (YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName) [slotExpr, valueExpr])) =
      .continue (irFieldStore fields fieldName state target value) := by
  unfold irFieldStore
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa [fieldStoreBuiltin, htrans] using
      execIRStmt_sstore_of_eval (fuel := fuel) hslot hvalue
  · simpa [fieldStoreBuiltin, htrans, SourceSemantics.wordNormalize] using
      execIRStmt_tstore_of_eval (fuel := fuel) hslot hvalue

private theorem bindingsExactlyMatchIRVarsOnScope_irFieldStore {fields : List Field}
    {fieldName : String} {scope : List String} {bindings : List (String × Nat)}
    {state : IRState} {target value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      (irFieldStore fields fieldName state target value) := by
  intro name hname
  unfold irFieldStore
  split <;> simpa [IRState.getVar] using hexact name hname

/-- A compiled core expression evaluates in any IR state matching the runtime on its scope
to the expression's source value. -/
private theorem evalIRExpr_of_compileExpr_core_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {expr : Expr} {exprIR : YulExpr} {n : Nat}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hIR : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hsrc : SourceSemantics.evalExpr fields runtime expr = some n) :
    evalIRExpr state exprIR = some n := by
  obtain ⟨m, hm, hir, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcore hinScope hexact hscope hbounded hruntime hIR
  rw [hsrc, Option.some.injEq] at hm
  exact hm ▸ hir

/-- A source statement that rewrites storage words and compiles to a single field store steps in
lockstep with the IR, given its source update and the matching post-state relation. -/
private theorem compiledStmtStep_fieldStore_single_of_eval
    {fields : List Field} {scope : List String} {fieldName : String} {stmt : Stmt}
    {slotExpr valueIR : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {world' : Verity.ContractState} {target value : Nat} (extraFuel : Nat)
    (hincl : FunctionBody.scopeNamesIncluded (stmtNextScope scope stmt) scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hslot : evalIRExpr state slotExpr = some target)
    (hvalue : evalIRExpr state valueIR = some value)
    (hsrc : SourceSemantics.execStmt fields runtime stmt =
      .continue { runtime with world := world' })
    (hmatch : FunctionBody.runtimeStateMatchesIR fields { runtime with world := world' }
      (irFieldStore fields fieldName state target value)) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
      execIRStmts
          ([YulStmt.exprStmt (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [slotExpr, valueIR])].length + extraFuel + 1) state
          [YulStmt.exprStmt (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [slotExpr, valueIR])] = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec := by
  refine ⟨_, .continue (irFieldStore fields fieldName state target value), hsrc, ?_, ?_⟩
  · rw [show [YulStmt.exprStmt (YulExpr.call (fieldStoreBuiltin fields fieldName)
        [slotExpr, valueIR])].length + extraFuel + 1 = extraFuel + 1 + 1 by simp; omega,
      execIRStmts_succ_cons_of_continue _ _ _ _ _ (execIRStmt_fieldStore_of_eval hslot hvalue)]
    rfl
  · exact ⟨hmatch, FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (bindingsExactlyMatchIRVarsOnScope_irFieldStore hexact) hincl,
      hbounded, FunctionBody.scopeNamesPresent_of_included hscope hincl⟩

/-- A uint-keyed mapping field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeUintKeyedMappingFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved : findResolvedFieldAtSlotCopy fields
      (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeUintKeyedMappingFieldSlots
            fields fieldName runtime.world [slot] key value }
      (irFieldStore fields fieldName state
        (Compiler.Proofs.abstractMappingSlot slot key) value) := by
  unfold irFieldStore SourceSemantics.writeUintKeyedMappingFieldSlots
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa using runtimeStateMatchesIR_writeUintKeyedMappingSlot hruntime hresolved hdyn hvalue
  · simpa [SourceSemantics.wordNormalize_idem] using runtimeStateMatchesIR_writeTransientTarget
      (target := SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
      hruntime hvalue

/-- An address-keyed mapping field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved : findResolvedFieldAtSlotCopy fields
      (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingFieldSlots
            fields fieldName runtime.world [slot] key value }
      (irFieldStore fields fieldName state
        (Compiler.Proofs.abstractMappingSlot slot key) value) := by
  unfold irFieldStore SourceSemantics.writeAddressKeyedMappingFieldSlots
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa using runtimeStateMatchesIR_writeAddressKeyedMappingSlot hruntime hresolved hdyn hvalue
  · simpa [SourceSemantics.wordNormalize_idem] using runtimeStateMatchesIR_writeTransientTarget
      (target := SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
      hruntime hvalue

/-- A mapping-word field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingWordFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (mappingWordTargetSlot slot key wordOffset) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordFieldSlots
            fields fieldName runtime.world [slot] key wordOffset value }
      (irFieldStore fields fieldName state (mappingWordTargetSlot slot key wordOffset) value) := by
  unfold irFieldStore SourceSemantics.writeAddressKeyedMappingWordFieldSlots
    SourceSemantics.writeMappingTargets
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa [SourceSemantics.wordNormalize_idem, SourceSemantics.writeAddressKeyedMappingWordSlots]
      using runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot hruntime hresolved hdyn hvalue
  · simp only [↓reduceIte, List.map_cons, List.map_nil]
    exact runtimeStateMatchesIR_writeTransientTarget
      (target := mappingWordTargetSlot slot key wordOffset) hruntime hvalue

/-- A two-key mapping-word field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2WordFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key1 key2 wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved : findResolvedFieldAtSlotCopy fields
      (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2WordFieldSlots
            fields fieldName runtime.world [slot] key1 key2 wordOffset value }
      (irFieldStore fields fieldName state
        (mapping2WordTargetSlot slot key1 key2 wordOffset) value) := by
  unfold irFieldStore SourceSemantics.writeAddressKeyedMapping2WordFieldSlots
    SourceSemantics.writeMappingTargets
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa [SourceSemantics.wordNormalize_idem, SourceSemantics.writeAddressKeyedMapping2WordSlots]
      using runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot hruntime hresolved hdyn hvalue
  · simp only [↓reduceIte, List.map_cons, List.map_nil]
    exact runtimeStateMatchesIR_writeTransientTarget
      (target := mapping2WordTargetSlot slot key1 key2 wordOffset) hruntime hvalue

/-- A mapping-chain field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingChainFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot : Nat} {keys : List Nat} {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields (SourceSemantics.mappingSlotChain slot keys) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (SourceSemantics.mappingSlotChain slot keys) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainFieldSlots
            fields fieldName runtime.world [slot] keys value }
      (irFieldStore fields fieldName state (SourceSemantics.mappingSlotChain slot keys) value) := by
  unfold irFieldStore SourceSemantics.writeAddressKeyedMappingChainFieldSlots
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa using
      runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot hruntime hresolved hdyn hvalue
  · have h := runtimeStateMatchesIR_writeTransientTarget
      (target := SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain slot keys))
      hruntime hvalue
    rw [SourceSemantics.wordNormalize_idem] at h
    simp only [↓reduceIte, List.map_cons, List.map_nil]
    exact h

/-- A two-key mapping field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2FieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key1 key2 value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved : findResolvedFieldAtSlotCopy fields (Compiler.Proofs.abstractMappingSlot
      (Compiler.Proofs.abstractMappingSlot slot key1) key2) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2) = none)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2FieldSlots
            fields fieldName runtime.world [slot] key1 key2 value }
      (irFieldStore fields fieldName state (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2) value) := by
  unfold irFieldStore SourceSemantics.writeAddressKeyedMapping2FieldSlots
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa using runtimeStateMatchesIR_writeAddressKeyedMapping2Slot hruntime hresolved hdyn hvalue
  · have h := runtimeStateMatchesIR_writeTransientTarget
      (target := SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2)) hruntime hvalue
    rw [SourceSemantics.wordNormalize_idem] at h
    simp only [↓reduceIte, List.map_cons, List.map_nil]
    exact h

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
    CompiledStmtPreserves fields scope (.setMappingUint fieldName key value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨keyNat, hKeySrc, hIRKey, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey hinScopeKey hexact hscope hbounded hruntime hkeyIR
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
  have hslot : evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
      some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
    simpa [SourceSemantics.mappingSlotChain] using evalIRExpr_mappingSlotChain
      (baseSlot := slot) (keyIRs := [keyIR]) (keyVals := [keyNat]) (by simp [hIRKey])
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded hslot hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc])
    (runtimeStateMatchesIR_writeUintKeyedMappingFieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkeyIRInternal := compileExprWithInternals_nil_ok hkeyIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIRInternal, hvalueIRInternal]
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
      exact ⟨[], by
        simp [CompilationModel.compileExprList, CompilationModel.compileExprListWithInternals,
          pure, Except.pure]⟩
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
      rcases ih htail with ⟨restIR, hrestIR⟩
      have hexprIRInternal := compileExprWithInternals_nil_ok hexprIR
      have hrestIRInternal := compileExprListWithInternals_nil_ok hrestIR
      exact ⟨exprIR :: restIR, by
        simp [CompilationModel.compileExprList, CompilationModel.compileExprListWithInternals,
          hexprIRInternal, hrestIRInternal, bind, Except.bind, pure, Except.pure]
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
  have hargExprsInternal := compileExprListWithInternals_nil_ok hargExprs
  refine ⟨compileScalarEmitFromCompiledArgs eventDef args argExprs, ?_⟩
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    CompilationModel.compileEmit]
  simp [hfind, hlen, hargExprsInternal, hindexedGuard, hscalarCompile,
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
    simpa [hcompiled, Except.toOption] using h
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
      simp [CompilationModel.compileExprList, CompilationModel.compileExprListWithInternals] at hcompiled
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
      have hexprIRInternal := compileExprWithInternals_nil_ok hexprIR
      have hrestIRsInternal := compileExprListWithInternals_nil_ok hrestIRs
      simp [CompilationModel.compileExprList, CompilationModel.compileExprListWithInternals,
        hexprIRInternal, hrestIRsInternal] at hcompiled
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
    simpa [SourceSemantics.mappingSlotChain,
      Compiler.Proofs.abstractMappingSlot_eq_solidity] using
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
  simpa [SourceSemantics.mappingSlotChain,
    Compiler.Proofs.abstractMappingSlot_eq_solidity] using
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
    CompiledStmtPreserves fields scope (.setMappingChain fieldName keys value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases eval_compileExprList_core_of_scope
      hcoreKeys hexact hinScopeKeys hbounded hscope hruntime hkeyIRs with
    ⟨resolvedKeys, hkeysEval, hkeyIRVals⟩
  rcases hslotSafety runtime resolvedKeys hkeysEval with ⟨hresolvedNone, hdynNone⟩
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded (evalIRExpr_mappingSlotChain hkeyIRVals) hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hkeysEval, hValueSrc])
    (runtimeStateMatchesIR_writeAddressKeyedMappingChainFieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkeyIRsInternal := compileExprListWithInternals_nil_ok hkeyIRs
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetMappingChain,
      hmapping, hwriteSlots, hkeyIRsInternal, hvalueIRInternal]
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
    CompiledStmtPreserves fields scope (.setMapping fieldName key value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨keyNat, hKeySrc, hIRKey, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey hinScopeKey hexact hscope hbounded hruntime hkeyIR
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
  have hslot : evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
      some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
    simpa [SourceSemantics.mappingSlotChain] using evalIRExpr_mappingSlotChain
      (baseSlot := slot) (keyIRs := [keyIR]) (keyVals := [keyNat]) (by simp [hIRKey])
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded hslot hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc])
    (runtimeStateMatchesIR_writeAddressKeyedMappingFieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkeyIRInternal := compileExprWithInternals_nil_ok hkeyIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIRInternal, hvalueIRInternal]
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
    CompiledStmtPreserves fields scope (.setMappingWord fieldName key wordOffset value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨keyNat, hKeySrc, hIRKey, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey hinScopeKey hexact hscope hbounded hruntime hkeyIR
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded (evalIRExpr_mappingWordTarget_of_eval hIRKey) hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc])
    (runtimeStateMatchesIR_writeAddressKeyedMappingWordFieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkeyIRInternal := compileExprWithInternals_nil_ok hkeyIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIRInternal, hvalueIRInternal]
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

private theorem uint256_ofNat_val (x : Verity.Core.Uint256) :
    Verity.Core.Uint256.ofNat x.val = x := by
  ext
  simp only [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

private theorem evalIRExpr_and_eq_uint256 {state : IRState} {lhs rhs : YulExpr} {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a) (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "and" [lhs, rhs]) =
      some (Verity.Core.Uint256.and a b).val := by
  rw [FunctionBody.evalIRExpr_and_of_eval hlhs hrhs, uint256_and_val_eq_land_mod]

private theorem evalIRExpr_or_eq_uint256 {state : IRState} {lhs rhs : YulExpr} {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a) (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "or" [lhs, rhs]) =
      some (Verity.Core.Uint256.or a b).val := by
  rw [FunctionBody.evalIRExpr_or_of_eval hlhs hrhs, uint256_or_val_eq_lor_mod]

private theorem evalIRExpr_not_eq_uint256 {state : IRState} {expr : YulExpr} {a : Nat}
    (heval : evalIRExpr state expr = some a) :
    evalIRExpr state (YulExpr.call "not" [expr]) = some (Verity.Core.Uint256.not a).val := by
  rw [FunctionBody.evalIRExpr_not_of_eval heval, uint256_not_val_eq_xor_allOnes_mod]

private theorem evalIRExpr_shl_lit_eq_uint256 {state : IRState} {valueExpr : YulExpr}
    {shift value : Nat} (hshift : shift < 256)
    (hvalue : evalIRExpr state valueExpr = some value) :
    evalIRExpr state (YulExpr.call "shl" [YulExpr.lit shift, valueExpr]) =
      some (Verity.Core.Uint256.shl shift value).val := by
  have hmod : shift % Compiler.Constants.evmModulus = shift :=
    Nat.mod_eq_of_lt (lt_trans hshift (by decide))
  rw [FunctionBody.evalIRExpr_shl_of_eval (shift := shift) (by simp [evalIRExpr]) hvalue, hmod,
    if_pos hshift, uint256_shl_val_eq_mul_pow_mod _ _ hshift]

/-- A read-modify-write of one normalized transient slot preserves the runtime/IR match,
provided the IR applies the same word transformer to the raw slot value. -/
private theorem runtimeStateMatchesIR_modifyTransientTarget
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {target : Nat} {f : Verity.Core.Uint256 → Verity.Core.Uint256} {g : Nat → Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hfg : ∀ w : Verity.Core.Uint256, (f w).val = g w.val) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := runtime.world.modifyTransientSlots [target] f }
      { state with transientStorage := fun o =>
          if o = target then g (state.transientStorage target) else state.transientStorage o } := by
  rcases hruntime with ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock,
    hchain, hret, hevents, hcs⟩
  refine ⟨?_, ?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents, hcs⟩
  · funext query
    rw [hstorage]
    exact congrArg Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorageAt_congr (by simp) (by simp) (by simp))
  · funext query
    by_cases hquery : query = target
    · subst hquery
      simp [htransient, hfg]
    · have hfalse : [target].contains query = false := by simpa [eq_comm] using hquery
      simp only [hquery, if_false]
      rw [Verity.ContractState.transientStorage_modifyTransientSlots_not_mem _ _ _ hfalse]
      exact congrFun htransient query

/-- Every list of Yul statements is strictly larger (in `sizeOf`) than its length. -/
private theorem yulStmtList_length_add_one_le_sizeOf (l : List YulStmt) :
    l.length + 1 ≤ sizeOf l := by
  induction l with
  | nil => simp
  | cons h t ih =>
      show t.length + 1 + 1 ≤ 1 + sizeOf h + sizeOf t
      omega

/-- The fuel slack of a singleton block covers one step per body statement plus one. -/
private theorem singletonBlock_length_add_one_le_slack (body : List YulStmt) :
    body.length + 1 ≤ sizeOf [YulStmt.block body] - [YulStmt.block body].length := by
  rw [singletonBlock_sizeOf_slack]
  have := yulStmtList_length_add_one_le_sizeOf body
  omega

/-- The mapping-word slot expression `mappingSlot(slot, key) [+ wordOffset]`. -/
private def mappingWordSlotExpr (slot : Nat) (keyIR : YulExpr) (wordOffset : Nat) : YulExpr :=
  let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
  if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]

/-- The compiled read-modify-write block body of a packed mapping-word write. -/
private def packedMappingWordBody (fields : List Field) (fieldName : String) (slot : Nat)
    (keyIR : YulExpr) (wordOffset : Nat) (packed : PackedBits) (valueIR : YulExpr) :
    List YulStmt :=
  [ YulStmt.let_ "__compat_value" valueIR
  , YulStmt.let_ "__compat_packed"
      (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])
  , YulStmt.let_ "__compat_slot_word"
      (YulExpr.call (fieldLoadBuiltin fields fieldName)
        [mappingWordSlotExpr slot keyIR wordOffset])
  , YulStmt.let_ "__compat_slot_cleared"
      (YulExpr.call "and"
        [YulExpr.ident "__compat_slot_word",
          YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
  , YulStmt.exprStmt
      (YulExpr.call (fieldStoreBuiltin fields fieldName)
        [mappingWordSlotExpr slot keyIR wordOffset,
          YulExpr.call "or"
            [YulExpr.ident "__compat_slot_cleared",
              YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]]) ]

private theorem getVar_setVar_self (state : IRState) (name : String) (value : Nat) :
    (state.setVar name value).getVar name = some value := by
  simp [IRState.getVar, IRState.setVar]

/-- The merged packed word evaluates to `packedWordWrite` of the bound temporaries. -/
private theorem evalIRExpr_packedWordMerge_of_getVar {state : IRState} {old value : Nat}
    {packed : PackedBits} (hoffset : packed.offset < 256)
    (hcleared : state.getVar "__compat_slot_cleared" = some
      (Verity.Core.Uint256.and old (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
    (hpacked : state.getVar "__compat_packed" =
      some (Verity.Core.Uint256.and value (packedMaskNat packed)).val) :
    evalIRExpr state
      (YulExpr.call "or"
        [YulExpr.ident "__compat_slot_cleared",
          YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]) =
      some (SourceSemantics.packedWordWrite old value packed) := by
  rw [evalIRExpr_or_eq_uint256 (by simpa [evalIRExpr] using hcleared)
    (evalIRExpr_shl_lit_eq_uint256 hoffset (by simpa [evalIRExpr] using hpacked))]
  simp only [uint256_ofNat_val, SourceSemantics.packedWordWrite]

/-- The cleared slot word evaluates to the old word with the packed field masked out. -/
private theorem evalIRExpr_packedSlotCleared_of_getVar {state : IRState} {old : Nat}
    {packed : PackedBits} (hword : state.getVar "__compat_slot_word" = some old) :
    evalIRExpr state
      (YulExpr.call "and"
        [YulExpr.ident "__compat_slot_word",
          YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]]) =
      some (Verity.Core.Uint256.and old
        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
  rw [evalIRExpr_and_eq_uint256 (by simpa [evalIRExpr] using hword)
    (evalIRExpr_not_eq_uint256 (a := packedShiftedMaskNat packed) (by simp [evalIRExpr]))]
  simp only [uint256_ofNat_val]

/-- A `let` binds the value its initializer evaluates to. -/
private theorem execIRStmt_let_of_eval {state : IRState} {name : String} {valueExpr : YulExpr}
    {value : Nat} (heval : evalIRExpr state valueExpr = some value) (fuel : Nat) :
    execIRStmt (fuel + 1) state (YulStmt.let_ name valueExpr) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

/-- Binding a temporary outside the scope keeps both the scope and the runtime match. -/
private theorem scopeRuntimeMatch_setVar {fields : List Field} {scope : List String}
    {runtime : SourceSemantics.RuntimeState} {state : IRState} {name : String} {value : Nat}
    (h : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hname : name ∉ scope) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
        (state.setVar name value) ∧
      FunctionBody.runtimeStateMatchesIR fields runtime (state.setVar name value) :=
  ⟨FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant h.1 hname,
    FunctionBody.runtimeStateMatchesIR_setVar_irrelevant h.2⟩

/-- The first two packed-write statements bind the value and its masked field bits. -/
private theorem execIRStmts_packedValueLets_of_eval {state : IRState} {valueIR : YulExpr}
    {valueNat fuel : Nat} {packed : PackedBits} {rest : List YulStmt}
    (hvalue : evalIRExpr state valueIR = some valueNat) :
    execIRStmts (fuel + 3) state
      (YulStmt.let_ "__compat_value" valueIR ::
        YulStmt.let_ "__compat_packed" (YulExpr.call "and"
          [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)]) :: rest) =
      execIRStmts (fuel + 1) ((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
        (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) rest := by
  have hpk := evalIRExpr_and_eq_uint256 (state := state.setVar "__compat_value" valueNat)
    (lhs := YulExpr.ident "__compat_value") (rhs := YulExpr.lit (packedMaskNat packed))
    (a := valueNat) (b := packedMaskNat packed)
    (by simp [evalIRExpr, IRState.getVar, IRState.setVar]) (by simp [evalIRExpr])
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _ (execIRStmt_let_of_eval hvalue _),
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (execIRStmt_let_of_eval hpk _)]

/-- The middle two packed-write statements load the slot word and clear the field bits. -/
private theorem execIRStmts_packedSlotLets_of_eval {fields : List Field} {fieldName : String}
    {state : IRState} {slotExpr : YulExpr} {target fuel : Nat} {packed : PackedBits}
    {rest : List YulStmt} (hslot : evalIRExpr state slotExpr = some target) :
    execIRStmts (fuel + 3) state
      (YulStmt.let_ "__compat_slot_word"
          (YulExpr.call (fieldLoadBuiltin fields fieldName) [slotExpr]) ::
        YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and"
          [YulExpr.ident "__compat_slot_word",
            YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]]) :: rest) =
      execIRStmts (fuel + 1)
        ((state.setVar "__compat_slot_word" (irFieldWord fields fieldName state target)).setVar
          "__compat_slot_cleared"
          (Verity.Core.Uint256.and (irFieldWord fields fieldName state target)
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) rest := by
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_let_of_eval (evalIRExpr_fieldLoad_of_eval hslot) _),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_let_of_eval (evalIRExpr_packedSlotCleared_of_getVar (packed := packed)
        (getVar_setVar_self _ _ _)) _)]

/-- The packed mapping-word block binds its four compat temporaries (without disturbing the
scope or runtime match) and then stores the merged word at the mapping-word target. -/
private theorem execIRStmts_packedMappingWordBody_of_eval
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {scope : List String} {state : IRState} {keyIR valueIR : YulExpr}
    {slot wordOffset keyNat valueNat fuel : Nat} {packed : PackedBits}
    (hmatch : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hfresh : "__compat_value" ∉ scope ∧ "__compat_packed" ∉ scope ∧
      "__compat_slot_word" ∉ scope ∧ "__compat_slot_cleared" ∉ scope)
    (hkey : ∀ st, FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings st ∧
      FunctionBody.runtimeStateMatchesIR fields runtime st → evalIRExpr st keyIR = some keyNat)
    (hvalue : evalIRExpr state valueIR = some valueNat) (hoffset : packed.offset < 256) :
    ∃ st, (FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings st ∧
        FunctionBody.runtimeStateMatchesIR fields runtime st) ∧
      execIRStmts (fuel + 6) state
          (packedMappingWordBody fields fieldName slot keyIR wordOffset packed valueIR) =
        .continue (irFieldStore fields fieldName st (mappingWordTargetSlot slot keyNat wordOffset)
          (SourceSemantics.packedWordWrite
            (irFieldWord fields fieldName st (mappingWordTargetSlot slot keyNat wordOffset))
            valueNat packed)) := by
  rcases hfresh with ⟨h1, h2, h3, h4⟩
  let s2 := (state.setVar "__compat_value" valueNat).setVar "__compat_packed"
    (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val
  have hm2 := scopeRuntimeMatch_setVar (state := state.setVar "__compat_value" valueNat)
    (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
    (scopeRuntimeMatch_setVar hmatch h1) h2
  have hslot2 : evalIRExpr s2 (mappingWordSlotExpr slot keyIR wordOffset) =
    some (mappingWordTargetSlot slot keyNat wordOffset) :=
    evalIRExpr_mappingWordTarget_of_eval (hkey s2 hm2)
  let old := irFieldWord fields fieldName s2 (mappingWordTargetSlot slot keyNat wordOffset)
  have hm4 := scopeRuntimeMatch_setVar (value := (Verity.Core.Uint256.and old
    (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
    (scopeRuntimeMatch_setVar (value := old) hm2 h3) h4
  let s4 := (s2.setVar "__compat_slot_word" old).setVar "__compat_slot_cleared"
    (Verity.Core.Uint256.and old (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val
  refine ⟨s4, hm4, ?_⟩
  have hmerge := evalIRExpr_packedWordMerge_of_getVar (state := s4) (value := valueNat) hoffset
    (getVar_setVar_self _ _ _) (by simp [s4, s2, IRState.getVar, IRState.setVar])
  have hold : irFieldWord fields fieldName s4 (mappingWordTargetSlot slot keyNat wordOffset) =
    old := rfl
  rw [hold, show fuel + 6 = fuel + 3 + 3 from rfl, packedMappingWordBody,
    execIRStmts_packedValueLets_of_eval hvalue, show fuel + 3 + 1 = fuel + 1 + 3 from rfl,
    execIRStmts_packedSlotLets_of_eval hslot2,
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (execIRStmt_fieldStore_of_eval
      (slotExpr := mappingWordSlotExpr slot keyIR wordOffset)
      (evalIRExpr_mappingWordTarget_of_eval (hkey _ hm4)) hmerge)]
  rfl

/-- A packed mapping-word field write keeps the runtime/IR match on either storage channel. -/
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordFieldSlots
    {fields : List Field} {fieldName : String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {slot key wordOffset value : Nat} {packed : PackedBits}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn : findDynamicArrayElementAtSlotCopy fields runtime.world
      (mappingWordTargetSlot slot key wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
            fields fieldName runtime.world [slot] key wordOffset packed value }
      (irFieldStore fields fieldName state (mappingWordTargetSlot slot key wordOffset)
        (SourceSemantics.packedWordWrite
          (irFieldWord fields fieldName state (mappingWordTargetSlot slot key wordOffset))
          value packed)) := by
  unfold irFieldStore irFieldWord SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
  cases htrans : SourceSemantics.fieldIsTransient fields fieldName
  · simpa using runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
      (packed := packed) (value := value) hruntime hresolved hdyn
  · have hnorm : SourceSemantics.wordNormalize (mappingWordTargetSlot slot key wordOffset) =
        mappingWordTargetSlot slot key wordOffset := SourceSemantics.wordNormalize_idem _
    simp only [if_true, hnorm]
    exact runtimeStateMatchesIR_modifyTransientTarget
      (target := mappingWordTargetSlot slot key wordOffset)
      (g := fun n => SourceSemantics.packedWordWrite n value packed) hruntime
      (fun _ => by simp only [SourceSemantics.packedWordWrite, uint256_ofNat_val])

/-- `execIRStmts_single_block_of_continue` at the `length + fuel + 1` shape of
`CompiledStmtStep.preserves`. -/
private theorem execIRStmts_singleton_block_of_continue {fuel : Nat} {state next : IRState}
    {body : List YulStmt} (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts ([YulStmt.block body].length + fuel + 1) state [YulStmt.block body] =
      .continue next := by
  simpa [Nat.add_comm, Nat.add_left_comm] using
    execIRStmts_single_block_of_continue fuel state next body hbody

private theorem packedBits_offset_lt_of_valid {packed : PackedBits}
    (hpacked : packedBitsValid packed = true) : packed.offset < 256 := by
  have hvalid := hpacked
  simp [CompilationModel.packedBitsValid] at hvalid
  omega

private theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {wordOffset : Nat} {packed : PackedBits} {keyIR valueIR : YulExpr} {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope) (hcompatPacked : "__compat_packed" ∉ scope)
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
    CompiledStmtPreserves fields scope (.setMappingPackedWord fieldName key wordOffset packed value)
      [YulStmt.block
        (packedMappingWordBody fields fieldName slot keyIR wordOffset packed valueIR)] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨keyNat, hKeySrc, hIRKey, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey hinScopeKey hexact hscope hbounded hruntime hkeyIR
  obtain ⟨valueNat, hValueSrc, hIRValue, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
  have hfuel : 6 ≤ extraFuel := le_trans (singletonBlock_length_add_one_le_slack
    (packedMappingWordBody fields fieldName slot keyIR wordOffset packed valueIR)) hslack
  obtain ⟨st, ⟨hexactSt, hruntimeSt⟩, hbody⟩ := execIRStmts_packedMappingWordBody_of_eval
    (fieldName := fieldName) (slot := slot) (wordOffset := wordOffset) (fuel := extraFuel - 6)
    ⟨hexact, hruntime⟩ ⟨hcompatValue, hcompatPacked, hcompatSlotWord, hcompatSlotCleared⟩
    (fun _ h => evalIRExpr_of_compileExpr_core_of_scope
      hcoreKey hinScopeKey h.1 hscope hbounded h.2 hkeyIR hKeySrc) hIRValue
    (packedBits_offset_lt_of_valid hpacked)
  rw [Nat.sub_add_cancel hfuel] at hbody
  have hincl : FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value))
      scope := fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn
  refine ⟨_, _, rfl, execIRStmts_singleton_block_of_continue hbody, ?_⟩
  simp only [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, hpacked]
  exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordFieldSlots
      hruntimeSt hresolvedNone hdynNone,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (bindingsExactlyMatchIRVarsOnScope_irFieldStore hexactSt) hincl,
    hbounded, FunctionBody.scopeNamesPresent_of_included hscope hincl⟩

private theorem compileStmt_setMappingPackedWord_singleSlot_ok
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {wordOffset : Nat} {packed : PackedBits} {keyIR valueIR : YulExpr} {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hpacked : packedBitsValid packed = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.setMappingPackedWord fieldName key wordOffset packed value) =
      Except.ok
        [YulStmt.block
          (packedMappingWordBody fields fieldName slot keyIR wordOffset packed valueIR)] := by
  rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
    ⟨f, hfind, _⟩
  have hkeyIRInternal := compileExprWithInternals_nil_ok hkeyIR
  have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    CompilationModel.compileMappingPackedSlotWrite, hmapping, hpacked, hwriteSlots,
    hkeyIRInternal, hvalueIRInternal, Bool.not_true, bne_self_eq_false,
    ite_false, ite_true, pure, Except.pure, bind, Except.bind]
  simp [hfind, fieldLoadBuiltin, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
    packedMappingWordBody, mappingWordSlotExpr, Bind.bind, Except.bind, pure, Except.pure]

theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {wordOffset : Nat} {packed : PackedBits} {keyIR valueIR : YulExpr} {slot : Nat}
    (hmapping : isMapping fields fieldName = true) (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope) (hcompatPacked : "__compat_packed" ∉ scope)
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
        , YulStmt.exprStmt
            (YulExpr.call (fieldStoreBuiltin fields fieldName)
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
               YulExpr.call "or"
                 [YulExpr.ident "__compat_slot_cleared",
                   YulExpr.call "shl"
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] :=
  ⟨compileStmt_setMappingPackedWord_singleSlot_ok hmapping hpacked hwriteSlots hkeyIR hvalueIR,
    compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
      hcoreKey hinScopeKey hcoreValue hinScopeValue hcompatValue hcompatPacked
      hcompatSlotWord hcompatSlotCleared hpacked hwriteSlots hslotSafety hkeyIR hvalueIR⟩

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
    (hmember : findStructMember members memberName =
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
    CompiledStmtPreserves fields scope (.setStructMember fieldName key memberName value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] := by
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
  · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtBindNames]
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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkeyIRInternal := compileExprWithInternals_nil_ok hkeyIR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetStructMember,
      CompilationModel.compileMappingSlotWrite, hmapping, hnotMapping2, hmembers, hmember,
      hwriteSlots, hkeyIRInternal, hvalueIRInternal]
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
    (hcoreKey1 : FunctionBody.ExprCompileCore key1) (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2) (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
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
    CompiledStmtPreserves fields scope (.setMapping2 fieldName key1 key2 value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨key1Nat, hKey1Src, hIRKey1, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey1 hinScopeKey1 hexact hscope hbounded hruntime hkey1IR
  obtain ⟨key2Nat, hKey2Src, hIRKey2, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey2 hinScopeKey2 hexact hscope hbounded hruntime hkey2IR
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded (evalIRExpr_mappingSlot2_of_eval hIRKey1 hIRKey2) hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc])
    (runtimeStateMatchesIR_writeAddressKeyedMapping2FieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1) (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2) (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
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
        [YulStmt.exprStmt
          (YulExpr.call (fieldStoreBuiltin fields fieldName)
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkey1IRInternal := compileExprWithInternals_nil_ok hkey1IR
    have hkey2IRInternal := compileExprWithInternals_nil_ok hkey2IR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetMapping2,
      hmapping2, hwriteSlots, hkey1IRInternal, hkey2IRInternal, hvalueIRInternal]
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
    CompiledStmtPreserves fields scope (.setMapping2Word fieldName key1 key2 wordOffset value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] := by
  intro runtime state extraFuel hexact hscope hbounded hruntime _hslack
  obtain ⟨key1Nat, hKey1Src, hIRKey1, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey1 hinScopeKey1 hexact hscope hbounded hruntime hkey1IR
  obtain ⟨key2Nat, hKey2Src, hIRKey2, -⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreKey2 hinScopeKey2 hexact hscope hbounded hruntime hkey2IR
  obtain ⟨valueNat, hValueSrc, hIRValue, hvalueLt⟩ := exists_eval_of_compileExpr_core_of_scope
    hcoreValue hinScopeValue hexact hscope hbounded hruntime hvalueIR
  rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
  exact compiledStmtStep_fieldStore_single_of_eval extraFuel
    (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
    hexact hscope hbounded (evalIRExpr_mapping2WordTarget_of_eval hIRKey1 hIRKey2) hIRValue
    (by simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc])
    (runtimeStateMatchesIR_writeAddressKeyedMapping2WordFieldSlots
      hruntime hresolvedNone hdynNone hvalueLt)

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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkey1IRInternal := compileExprWithInternals_nil_ok hkey1IR
    have hkey2IRInternal := compileExprWithInternals_nil_ok hkey2IR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetMapping2Word,
      hmapping2, hwriteSlots, hkey1IRInternal, hkey2IRInternal, hvalueIRInternal]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

private theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    {fields : List Field} {scope : List String}
    {fieldName memberName : String} {key1 key2 value : Expr}
    {wordOffset : Nat} {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr} {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember : findStructMember members memberName =
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
    CompiledStmtPreserves fields scope (.setStructMember2 fieldName key1 key2 memberName value)
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] := by
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
  · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtBindNames]
      using hmatch

theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
    {fields : List Field} {scope : List String}
    {fieldName memberName : String} {key1 key2 value : Expr}
    {wordOffset : Nat} {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr} {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1) (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2) (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember : findStructMember members memberName =
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
      [YulStmt.exprStmt
        (YulExpr.call (fieldStoreBuiltin fields fieldName)
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    rcases findFieldWithResolvedSlot_of_findFieldWriteSlots_singleton hwriteSlots with
      ⟨f, hfind, _⟩
    have hkey1IRInternal := compileExprWithInternals_nil_ok hkey1IR
    have hkey2IRInternal := compileExprWithInternals_nil_ok hkey2IR
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, CompilationModel.compileSetStructMember2,
      hmapping2, hmembers, hmember, hwriteSlots, hkey1IRInternal, hkey2IRInternal,
      hvalueIRInternal]
    simp [hfind, fieldStoreBuiltin, SourceSemantics.fieldIsTransient,
      Bind.bind, Except.bind, pure, Except.pure]
  preserves := compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hmembers hmember hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

private theorem exists_evalExpr_eq_evalIRExpr_of_core
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {expr : Expr} {exprIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hexprIR : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ value, SourceSemantics.evalExpr fields runtime expr = some value ∧
      evalIRExpr state exprIR = some value := by
  have hpresent : FunctionBody.exprBoundNamesPresent expr runtime.bindings :=
    FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
  have heval := FunctionBody.eval_compileExpr_core_of_scope
    hcore hexact hinScope hbounded hpresent hruntime
  rw [hexprIR] at heval
  simp [Except.toOption] at heval
  rcases hIRValue : evalIRExpr state exprIR with _ | value
  · simp [hIRValue, Option.bind] at heval
  · simp [hIRValue, Option.bind] at heval
    exact ⟨value, heval.symm, rfl⟩

private theorem evalExpr_lt_modulus_of_core
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {expr : Expr} {value : Nat}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (heval : SourceSemantics.evalExpr fields runtime expr = some value) :
    value < Verity.Core.Uint256.modulus := by
  have hlt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded
    (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rw [heval] at hlt
  simpa using hlt

/-- Body of the block emitted for a scalar storage write mirrored into alias slots. -/
private abbrev aliasSlotsBody (valueIR : YulExpr) (slots : List Nat) : List YulStmt :=
  [YulStmt.let_ "__compat_value" valueIR] ++
    slots.map (fun writeSlot =>
      YulStmt.exprStmt
        (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))

/-- IR state after binding `__compat_value` and storing it to every slot in `slots`. -/
private abbrev aliasSlotsPostState (state : IRState) (slots : List Nat) (value : Nat) :
    IRState :=
  { state.setVar "__compat_value" value with
      storage := abstractStoreStorageOrMappingMany
        (state.setVar "__compat_value" value).storage slots value }

private theorem compileStmt_setStorage_aliasSlots_eq
    {fields : List Field} {scope : List String} {fieldName : String} {value : Expr}
    {valueIR : YulExpr} {f : Field} {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (halias : f.aliasSlots ≠ [])
    (hunpacked : f.packedBits = none)
    (hnotTransient : f.isTransient = false)
    (hNotMapping : isMapping fields fieldName = false)
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.setStorage fieldName value) =
      Except.ok [YulStmt.block (aliasSlotsBody valueIR (slot :: f.aliasSlots))] := by
  cases hty : f.ty with
  | adt name maxFields => exact False.elim (hNotAdt name maxFields hty)
  | uint256 | int256 | address | fixedArrayUint128 | dynamicArray | mappingTyped
    | mappingStruct | mappingStruct2 | mappingFixedArray =>
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileSetStorage, hNotMapping, hfind, halias, hunpacked,
        hnotTransient, hvalueIR, hty, pure, Except.pure, Bind.bind, Except.bind]

private theorem execIRStmts_aliasSlotsBlock_eq
    {state : IRState} {valueIR : YulExpr} {slots : List Nat} {value extraFuel : Nat}
    (hvalueEval : evalIRExpr state valueIR = some value)
    (hslack : sizeOf [YulStmt.block (aliasSlotsBody valueIR slots)] -
      [YulStmt.block (aliasSlotsBody valueIR slots)].length ≤ extraFuel) :
    execIRStmts ([YulStmt.block (aliasSlotsBody valueIR slots)].length + extraFuel + 1) state
        [YulStmt.block (aliasSlotsBody valueIR slots)] =
      .continue (aliasSlotsPostState state slots value) := by
  have hle := singletonBlock_length_add_one_le_slack (aliasSlotsBody valueIR slots)
  have hlen : (aliasSlotsBody valueIR slots).length = 1 + slots.length := by
    simp [aliasSlotsBody]
    omega
  have hbody := execIRStmts_let_then_sstore_lit_ident_slots_continue
    (extraFuel - (slots.length + 2)) state slots "__compat_value" valueIR value hvalueEval
  rw [show slots.length + (extraFuel - (slots.length + 2)) + 2 = extraFuel by omega] at hbody
  have hblock := execIRStmts_single_block_of_continue extraFuel state
    (aliasSlotsPostState state slots value) (aliasSlotsBody valueIR slots) hbody
  rw [List.length_singleton, show 1 + extraFuel + 1 = extraFuel + 2 by omega]
  exact hblock

private theorem execStmt_setStorage_aliasSlots_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {fieldName : String}
    {value : Expr} {f : Field} {slot valueNat : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnotTransient : f.isTransient = false)
    (hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmt fields runtime (.setStorage fieldName value) =
      .continue { runtime with world :=
        SourceSemantics.writeUintSlots runtime.world (slot :: f.aliasSlots) valueNat } := by
  have hfieldTransient : SourceSemantics.fieldIsTransient fields fieldName = false := by
    simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
  simp [SourceSemantics.execStmt, SourceSemantics.writeUintFieldSlots,
    SourceSemantics.writeMappingTargets, hwriteSlots, hValueSrc, hfieldTransient,
    hfind, hunpacked, hnotTransient]

private theorem stmtStepMatchesIRExec_setStorage_aliasSlots
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {fieldName : String} {value : Expr} {f : Field} {slots : List Nat}
    {valueNat : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope)
    (hresolved : ∀ writeSlot ∈ slots, findResolvedFieldAtSlotCopy fields writeSlot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueLt : valueNat < Verity.Core.Uint256.modulus) :
    stmtStepMatchesIRExec fields (stmtNextScope scope (.setStorage fieldName value))
      (.continue { runtime with
        world := SourceSemantics.writeUintSlots runtime.world slots valueNat })
      (.continue (aliasSlotsPostState state slots valueNat)) := by
  have hincl : FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.setStorage fieldName value)) scope := fun n hn => by
    simpa [stmtNextScope, collectStmtBindNames] using hn
  have hexactSet := FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
    (value := valueNat) hexact (compatValue_not_mem_scope_of_reservedPrefix hscopeReserved)
  exact ⟨runtimeStateMatchesIR_writeUintSlots
      (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime)
      hresolved hnotAddr hnotDyn hvalueLt,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (bindingsExactlyMatchIRVarsOnScope_writeUintSlots hexactSet) hincl,
    hbounded, FunctionBody.scopeNamesPresent_of_included hscope hincl⟩

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
            YulStmt.exprStmt
              (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] where
  compileOk := compileStmt_setStorage_aliasSlots_eq hfind halias hunpacked hnotTransient
    hNotMapping hNotAdt hvalueIR
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    obtain ⟨valueNat, hValueSrc, hvalueEval⟩ := exists_evalExpr_eq_evalIRExpr_of_core
      hcore hvalueIR hinScope hexact hscope hbounded hruntime
    refine ⟨_, _, execStmt_setStorage_aliasSlots_eq hfind hwriteSlots hunpacked hnotTransient
      hValueSrc, execIRStmts_aliasSlotsBlock_eq hvalueEval hslack, ?_⟩
    exact stmtStepMatchesIRExec_setStorage_aliasSlots hexact hscope hbounded hruntime
      hscopeReserved
      (fun _ hmem => findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
        hnoConflict hfind hwriteSlots hmem hnotTransient hunpacked) hnotAddr hnotDyn
      (evalExpr_lt_modulus_of_core hcore hinScope hexact hscope hbounded hruntime hValueSrc)

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
  · exact ⟨_, compiledStmtStep_setStorage_singleSlot hcore hinScope hfind
      (by simpa [halias] using hwriteSlots) halias hunpacked hnoConflict hnotAddr hnotDyn
      hnotTransient hNotMapping hNotAdt hvalueIR⟩
  · exact ⟨_, compiledStmtStep_setStorage_aliasSlots hcore hinScope hfind hwriteSlots halias
      (scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes hvalidate hfn hscopeNames)
      hunpacked hnoConflict hnotAddr hnotDyn hnotTransient hNotMapping hNotAdt hvalueIR⟩

private theorem collectStmtListBindNames_append_left {a b : List Stmt} {x : String}
    (hx : x ∈ collectStmtListBindNames a) : x ∈ collectStmtListBindNames (a ++ b) := by
  induction a with
  | nil => simp [collectStmtListBindNames] at hx
  | cons s rest ih =>
      simp only [collectStmtListBindNames, List.mem_append, List.cons_append] at hx ⊢
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)

private theorem collectStmtListAssignedNames_append_left {a b : List Stmt} {x : String}
    (hx : x ∈ collectStmtListAssignedNames a) : x ∈ collectStmtListAssignedNames (a ++ b) := by
  induction a with
  | nil => simp [collectStmtListAssignedNames] at hx
  | cons s rest ih =>
      simp only [collectStmtListAssignedNames, List.mem_append, List.cons_append] at hx ⊢
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)

/-- Every name in scope after a scope-disciplined body prefix is a parameter, a body
binder, a body assignment target, or a field name. -/
private theorem scopeNames_of_stmtListScopeDiscipline_prefix
    {spec : CompilationModel} {fn : FunctionSpec} {«prefix» rest : List Stmt}
    (hprefix :
      StmtListScopeDiscipline (spec.fields.map (·.name)) (fn.params.map (·.name)) «prefix»)
    (hbody : fn.body = «prefix» ++ rest) :
    ∀ name, name ∈ List.foldl stmtNextScope (fn.params.map (·.name)) «prefix» →
      name ∈
        (fn.params.map (·.name) ++
          collectStmtListBindNames fn.body ++
          collectStmtListAssignedNames fn.body ++
          spec.fields.map (·.name)) := by
  intro name hmem
  have hscopeNames := stmtListScopeDiscipline_scope_names hprefix name hmem
  simp only [List.mem_append] at hscopeNames ⊢
  rcases hscopeNames with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (by rw [hbody]; exact collectStmtListBindNames_append_left h)))
  · exact Or.inl (Or.inr (by rw [hbody]; exact collectStmtListAssignedNames_append_left h))
  · exact Or.inr h

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
  exact compiledStmtStep_setStorage_of_validateIdentifierShapes hvalidate hfn
    (scopeNames_of_stmtListScopeDiscipline_prefix hprefix hbody) hcore hinScope hfind
    hwriteSlots hunpacked hnoConflict hnotAddr hnotDyn hnotTransient hNotMapping hNotAdt hvalueIR

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
  exact compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    hvalidateShapes hfn
    (stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
      hprefixCore hvalidateRefs hparamScope (by simpa [List.append_assoc] using hbody))
    hbody hcore hinScope hfind hwriteSlots hunpacked hnoConflict hnotAddr hnotDyn
    hnotTransient hNotMapping hNotAdt hvalueIR

-- NOTE: The _of_compileStmtList intermediate was superseded by _of_bodySurface below.
-- Its TYPESIG_SORRY signature had a bug (missing hNotMapping parameter) and was bypassed.

/-- The value of a `setStorage` statement in a body that avoids the unsupported contract
surface compiles through the core expression fragment. -/
private theorem exprCompileCore_setStorage_of_bodySurface
    {fn : FunctionSpec} {«prefix» «suffix» : List Stmt} {fieldName : String} {value : Expr}
    (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix») :
    FunctionBody.ExprCompileCore value := by
  have hstmtSurface :
      stmtTouchesUnsupportedContractSurface (.setStorage fieldName value) = false :=
    stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
      (by simpa [hbody] using hbodySurface)
  exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
    (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)

/-- A compiled `setStorage` statement inside a compiled body targets neither a mapping
nor an ADT field. -/
private theorem setStorage_notMapping_notAdt_of_compileStmtList
    {spec : CompilationModel} {fn : FunctionSpec} {«prefix» «suffix» : List Stmt}
    {bodyIR : List YulStmt} {fieldName : String} {value : Expr} {valueIR : YulExpr}
    {f : Field} {slot : Nat}
    (hbodyCompile :
      CompilationModel.compileStmtList
        spec.fields [] [] .calldata [] false (fn.params.map (·.name)) [] fn.body =
          Except.ok bodyIR)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    isMapping spec.fields fieldName = false ∧
      ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields := by
  rcases compileStmt_ok_of_compileStmtList_append_cons
    (by simpa [hbody] using hbodyCompile) with ⟨stmtIR, hstmt⟩
  have hNotMapping : isMapping spec.fields fieldName = false :=
    isMapping_false_of_compileStmt_setStorage_ok hstmt
  refine ⟨hNotMapping, fun name maxFields hty => ?_⟩
  simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    CompilationModel.compileSetStorage, hNotMapping, hfind, hty, hvalueIR, pure, Pure.pure,
    Except.pure, Bind.bind, Except.bind] at hstmt

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
  have hvalueCore := exprCompileCore_setStorage_of_bodySurface hbodySurface hbody
  have hinScope := exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
    hprefixCore hvalueCore hvalidateRefs hparamScope hbody
  obtain ⟨hNotMapping, hNotAdt⟩ :=
    setStorage_notMapping_notAdt_of_compileStmtList hbodyCompile hbody hfind hvalueIR
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

/-- Fresh temporary holding the condition value of a compiled terminal `ite`. -/
private abbrev iteTempName (scope : List String) (cond : Expr)
    (thenBranch elseBranch : List Stmt) : String :=
  CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
    (scope ++ collectExprNames cond ++
      collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)

/-- The single block emitted for a terminal `ite` statement. -/
private abbrev compiledIteIR (tempName : String) (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) : List YulStmt :=
  [YulStmt.block
    [ YulStmt.let_ tempName condIR
    , YulStmt.if_ (YulExpr.ident tempName) thenIR
    , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]

private theorem compileStmt_ite_eq_compiledIteIR
    {fields : List Field} {scope : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt} {condIR : YulExpr} {thenIR elseIR : List YulStmt}
    (hcondIR : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthenIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] thenBranch = Except.ok thenIR)
    (helseIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] elseBranch = Except.ok elseIR)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.ite cond thenBranch elseBranch) =
      Except.ok (compiledIteIR (iteTempName scope cond thenBranch elseBranch)
        condIR thenIR elseIR) := by
  have helseNonempty : elseBranch.isEmpty = false := by
    cases elseBranch with
    | nil => exact absurd rfl (FunctionBody.stmtListTerminalCore_ne_nil helse)
    | cons => simp
  have hcondIRInternal := compileExprWithInternals_nil_ok hcondIR
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
    hcondIRInternal, hthenIR, helseIR, Except.bind, helseNonempty]
  simp [compiledIteIR, iteTempName, List.append_assoc, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- A terminal `ite` branch, run after binding the condition temporary, matches its source. -/
private theorem stmtResultMatchesIRExec_iteBranch_of_setTemp
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {cond : Expr} {thenBranch elseBranch branch : List Stmt}
    {branchIR : List YulStmt} {condVal : Nat} (fuel : Nat)
    (hbranch : FunctionBody.StmtListTerminalCore scope branch)
    (hbranchIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] branch = Except.ok branchIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime branch)
      (execIRStmts (sizeOf branchIR + fuel + 1)
        (state.setVar (iteTempName scope cond thenBranch elseBranch) condVal) branchIR) := by
  have hBindIte :=
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
      (inScopeNames := scope) (cond := cond) (thenBranch := thenBranch)
      (elseBranch := elseBranch) (value := condVal) hexact FunctionBody.scopeNamesIncluded_refl
  have hRuntimeIte := FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
    (name := iteTempName scope cond thenBranch elseBranch) (value := condVal) hruntime
  rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel (extraFuel := fuel)
      hbranch FunctionBody.scopeNamesIncluded_refl hscope hBindIte hbounded hRuntimeIte with
    ⟨branchIR', hbranchIR', hsem⟩
  rw [hbranchIR] at hbranchIR'
  cases hbranchIR'
  exact hsem

private theorem stmtResultMatchesIRExec_compiledIteIR_else
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {cond : Expr} {elseBranch : List Stmt}
    {tempName : String} {condIR : YulExpr} {thenIR elseIR : List YulStmt}
    {condVal wholeExtraFuel : Nat}
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch)
    (hbranch : ∀ fuel, FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime elseBranch)
      (execIRStmts (sizeOf elseIR + fuel + 1) (state.setVar tempName condVal) elseIR))
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hcondEval : evalIRExpr state condIR = some condVal)
    (hcondZero : condVal = 0) :
    FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime elseBranch)
      (execIRStmts (sizeOf (compiledIteIR tempName condIR thenIR elseIR) + wholeExtraFuel + 1)
        state (compiledIteIR tempName condIR thenIR elseIR)) := by
  have hElse6 : sizeOf elseIR + 6 ≤ sizeOf (compiledIteIR tempName condIR thenIR elseIR) := by
    simp_wf; omega
  have hmatch := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
    (thenBranch := []) (rest := []) (extraFuel := wholeExtraFuel)
    (tempName := tempName) (condIR := condIR) (thenIR := thenIR) (tailIR := []) helse
    (hbranch (sizeOf (compiledIteIR tempName condIR thenIR elseIR) - (sizeOf elseIR + 5) +
      wholeExtraFuel - 1))
    hCondSrc (by simp [hcondZero]) hcondEval hcondZero
    (by congr 1; simp only [List.append_nil, compiledIteIR] at hElse6 ⊢; omega)
  rw [FunctionBody.execStmtList_terminal_core_ite_else_eq helse hCondSrc
    (by simp [hcondZero])] at hmatch
  simpa only [List.append_nil] using hmatch

private theorem stmtResultMatchesIRExec_compiledIteIR_then
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {cond : Expr} {thenBranch : List Stmt}
    {tempName : String} {condIR : YulExpr} {thenIR elseIR : List YulStmt}
    {condVal wholeExtraFuel : Nat}
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (hbranch : ∀ fuel, FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime thenBranch)
      (execIRStmts (sizeOf thenIR + fuel + 1) (state.setVar tempName condVal) thenIR))
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hcondEval : evalIRExpr state condIR = some condVal)
    (hcondNonzero : condVal ≠ 0) :
    FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime thenBranch)
      (execIRStmts (sizeOf (compiledIteIR tempName condIR thenIR elseIR) + wholeExtraFuel + 1)
        state (compiledIteIR tempName condIR thenIR elseIR)) := by
  have hmatch := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
    (elseBranch := []) (rest := []) (extraFuel := wholeExtraFuel)
    (tempName := tempName) (condIR := condIR) (thenIR := thenIR) (elseIR := elseIR)
    (tailIR := []) hthen
    (hbranch (sizeOf (compiledIteIR tempName condIR thenIR elseIR) - (sizeOf thenIR + 5) +
      wholeExtraFuel))
    hCondSrc (by simp [hcondNonzero]) hcondEval hcondNonzero
    (by simp only [List.append_nil, compiledIteIR])
  rw [FunctionBody.execStmtList_terminal_core_ite_then_eq hthen hCondSrc
    (by simp [hcondNonzero])] at hmatch
  simpa only [List.append_nil] using hmatch

/-- Close a terminal `ite` step from the match of the branch it selects. -/
private theorem stmtStep_ite_of_branch_match
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {cond : Expr} {thenBranch elseBranch branch : List Stmt}
    {compiledIR : List YulStmt} {extraFuel : Nat}
    (hbranch : FunctionBody.StmtListTerminalCore scope branch)
    (hexec : SourceSemantics.execStmt fields runtime (.ite cond thenBranch elseBranch) =
      SourceSemantics.execStmtList fields runtime branch)
    (hle : compiledIR.length ≤ sizeOf compiledIR)
    (hslack : sizeOf compiledIR - compiledIR.length ≤ extraFuel)
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime branch)
      (execIRStmts (sizeOf compiledIR + (extraFuel - (sizeOf compiledIR - compiledIR.length)) +
        1) state compiledIR)) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime (.ite cond thenBranch elseBranch) =
        sourceResult ∧
      execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.ite cond thenBranch elseBranch))
        sourceResult irExec := by
  have hfuel : compiledIR.length + extraFuel + 1 =
      sizeOf compiledIR + (extraFuel - (sizeOf compiledIR - compiledIR.length)) + 1 := by
    omega
  refine ⟨_, _, rfl, rfl, ?_⟩
  apply terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
  · rw [hexec, hfuel]
    exact hmatch
  · rw [hexec]
    exact FunctionBody.execStmtList_terminal_core_not_continue hbranch

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
  rcases FunctionBody.compileStmtList_terminal_core_ok (fields := fields) (inScopeNames := scope)
    hthen with ⟨thenIR, hthenIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok (fields := fields) (inScopeNames := scope)
    helse with ⟨elseIR, helseIR⟩
  refine ⟨_, compileStmt_ite_eq_compiledIteIR hcondIR hthenIR helseIR helse, ?_⟩
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨condVal, hCondSrc, hcondEval⟩ :=
    exists_evalExpr_eq_evalIRExpr_of_core hcond hcondIR hinScope hexact hscope hbounded hruntime
  by_cases hcondZero : condVal = 0
  · exact stmtStep_ite_of_branch_match helse (by simp [SourceSemantics.execStmt, hCondSrc,
      hcondZero]) (by simp_wf) hslack <| stmtResultMatchesIRExec_compiledIteIR_else helse
      (stmtResultMatchesIRExec_iteBranch_of_setTemp · helse helseIR hexact hscope hbounded
        hruntime) hCondSrc hcondEval hcondZero
  · exact stmtStep_ite_of_branch_match hthen (by simp [SourceSemantics.execStmt, hCondSrc,
      hcondZero]) (by simp_wf) hslack <| stmtResultMatchesIRExec_compiledIteIR_then hthen
      (stmtResultMatchesIRExec_iteBranch_of_setTemp · hthen hthenIR hexact hscope hbounded
        hruntime) hCondSrc hcondEval hcondZero

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

/-! ### Single-word storage reads bound into a local

`let`/`assign` of `Expr.storage`/`Expr.storageAddr` compile to a single
`sload` bound to the target. The lemmas below factor the shared argument: the
source and the IR read the same in-range word, and binding one in-range word
preserves the step invariant. -/

/-- Binding one in-range word on both sides preserves the statement-step invariant. -/
private theorem stmtStep_preserves_of_bindValue
    {fields : List Field} {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt}
    {name : String} {v fuel : Nat} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (hsrc : SourceSemantics.execStmt fields runtime stmt =
      .continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v })
    (hir : execIRStmts fuel state compiledIR = .continue (state.setVar name v))
    (hlt : v < Verity.Core.UINT256_MODULUS)
    (hnext : FunctionBody.scopeNamesIncluded (stmtNextScope scope stmt) (name :: scope))
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
      execIRStmts fuel state compiledIR = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec := by
  refine ⟨_, _, hsrc, hir, ?_⟩
  simp only [stmtStepMatchesIRExec]
  exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hnext,
    FunctionBody.bindingsBounded_bindValue hbounded name v hlt,
    FunctionBody.scopeNamesPresent_of_included
      (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hnext⟩

private theorem execStmt_letVar_of_evalExpr {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {name : String} {e : Expr} {v : Nat}
    (h : SourceSemantics.evalExpr fields runtime e = some v) :
    SourceSemantics.execStmt fields runtime (.letVar name e) =
      .continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v } := by
  change (match SourceSemantics.evalExpr fields runtime e with
    | some r => SourceSemantics.StmtResult.continue
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name r }
    | none => SourceSemantics.StmtResult.revert) = _
  rw [h]

private theorem execStmt_assignVar_of_evalExpr {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {name : String} {e : Expr} {v : Nat}
    (h : SourceSemantics.evalExpr fields runtime e = some v) :
    SourceSemantics.execStmt fields runtime (.assignVar name e) =
      .continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v } := by
  change (match SourceSemantics.evalExpr fields runtime e with
    | some r => SourceSemantics.StmtResult.continue
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name r }
    | none => SourceSemantics.StmtResult.revert) = _
  rw [h]

private theorem execIRStmts_singleton_let_of_eval {state : IRState} {name : String}
    {e : YulExpr} {v : Nat} (extraFuel : Nat) (h : evalIRExpr state e = some v) :
    execIRStmts ([YulStmt.let_ name e].length + extraFuel + 1) state [YulStmt.let_ name e] =
      .continue (state.setVar name v) := by
  rw [show [YulStmt.let_ name e].length + extraFuel + 1 = extraFuel + 1 + 1 by
    simp only [List.length_singleton]; omega]
  simp [execIRStmts, execIRStmt, h]

private theorem execIRStmts_singleton_assign_of_eval {state : IRState} {name : String}
    {e : YulExpr} {v : Nat} (extraFuel : Nat) (h : evalIRExpr state e = some v) :
    execIRStmts ([YulStmt.assign name e].length + extraFuel + 1) state [YulStmt.assign name e] =
      .continue (state.setVar name v) := by
  rw [show [YulStmt.assign name e].length + extraFuel + 1 = extraFuel + 1 + 1 by
    simp only [List.length_singleton]; omega]
  simp [execIRStmts, execIRStmt, h]

/-- A persistent, unpacked scalar field resolves at its IR slot. -/
private theorem findResolvedFieldAtSlotCopy_ofNat_of_findField
    {fields : List Field} {fieldName : String} {ty : FieldType} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := ty }, slot)) :
    findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat slot).toNat =
      some { name := fieldName, ty := ty } := by
  have hresolved := findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
    hnoConflict hfind
    (by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind) (by rfl) (by rfl)
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS] using
    (show findResolvedFieldAtSlotCopy fields (SourceSemantics.wordNormalize slot) =
        some { name := fieldName, ty := ty } from by
      rw [findResolvedFieldAtSlotCopy_wordNormalize]; exact hresolved)

private theorem evalExpr_storage_of_findField_uint256 {fields : List Field}
    {fieldName : String} {slot : Nat} {runtime : SourceSemantics.RuntimeState}
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    SourceSemantics.evalExpr fields runtime (.storage fieldName) =
      some (runtime.world.storage (SourceSemantics.wordNormalize slot)).val := by
  rw [SourceSemantics.evalExpr, hfind]
  rfl

private theorem evalExpr_storageAddr_of_findField_address {fields : List Field}
    {fieldName : String} {slot : Nat} {runtime : SourceSemantics.RuntimeState}
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    SourceSemantics.evalExpr fields runtime (.storageAddr fieldName) =
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

/-- The compiled `sload` of a resolved `uint256` field reads its source word. -/
private theorem evalIRExpr_sload_of_findField_uint256 {fields : List Field}
    {fieldName : String} {slot : Nat} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "sload" [YulExpr.lit slot]) =
      some (runtime.world.storage (SourceSemantics.wordNormalize slot)).val := by
  have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
  rw [encodeStorageAt_eq_storage_of_resolvedSlot
    (findResolvedFieldAtSlotCopy_ofNat_of_findField hnoConflict hfind) (by rfl) (by rfl)] at hIR
  have hlt : (runtime.world.storage (SourceSemantics.wordNormalize slot)).val <
      EvmYul.UInt256.size := (runtime.world.storage _).isLt
  rw [hIR, IRStorageSlot.toNat_ofNat_wordNormalize, Nat.mod_eq_of_lt hlt]

/-- The compiled `sload` of a resolved `address` field reads its source address. -/
private theorem evalIRExpr_sload_of_findField_address {fields : List Field}
    {fieldName : String} {slot : Nat} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "sload" [YulExpr.lit slot]) =
      some (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val := by
  have hIR := FunctionBody.evalIRExpr_sload_of_runtimeStateMatchesIR hruntime slot
  rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot
    (findResolvedFieldAtSlotCopy_ofNat_of_findField hnoConflict hfind) (by rfl) (by rfl)] at hIR
  have hlt : (runtime.world.storageAddr (SourceSemantics.wordNormalize slot)).val <
      EvmYul.UInt256.size :=
    Nat.lt_trans (runtime.world.storageAddr _).isLt (by decide)
  rw [hIR, IRStorageSlot.toNat_ofNat_wordNormalize, Nat.mod_eq_of_lt hlt]

private theorem storageAddr_val_lt_modulus (world : Verity.ContractState) (slot : Nat) :
    (world.storageAddr slot).val < Verity.Core.UINT256_MODULUS :=
  Nat.lt_trans (world.storageAddr slot).isLt (by decide)

private theorem compiledStmtStep_letStorageField
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (_hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.letVar tmp (Expr.storage fieldName))
      [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      CompilationModel.compileExprWithInternals, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ :=
    stmtStep_preserves_of_bindValue
      (execStmt_letVar_of_evalExpr (evalExpr_storage_of_findField_uint256 hfind))
      (execIRStmts_singleton_let_of_eval extraFuel
        (evalIRExpr_sload_of_findField_uint256 hnoConflict hfind hruntime))
      (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt
      (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
      hexact hscope hbounded hruntime

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

private theorem compiledStmtStep_letStorageAddrField
    {fields : List Field} {scope : List String} {tmp fieldName : String} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (_hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.letVar tmp (Expr.storageAddr fieldName))
      [YulStmt.let_ tmp (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      CompilationModel.compileExprWithInternals, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ :=
    stmtStep_preserves_of_bindValue
      (execStmt_letVar_of_evalExpr (evalExpr_storageAddr_of_findField_address hfind))
      (execIRStmts_singleton_let_of_eval extraFuel
        (evalIRExpr_sload_of_findField_address hnoConflict hfind hruntime))
      (storageAddr_val_lt_modulus runtime.world _)
      (fun n hn => by simpa [stmtNextScope, collectStmtBindNames] using hn)
      hexact hscope hbounded hruntime

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
    (_hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.assignVar name (Expr.storage fieldName))
      [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      CompilationModel.compileExprWithInternals, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ :=
    stmtStep_preserves_of_bindValue
      (execStmt_assignVar_of_evalExpr (evalExpr_storage_of_findField_uint256 hfind))
      (execIRStmts_singleton_assign_of_eval extraFuel
        (evalIRExpr_sload_of_findField_uint256 hnoConflict hfind hruntime))
      (runtime.world.storage (SourceSemantics.wordNormalize slot)).isLt
      (fun n hn => List.mem_cons_of_mem _ (by simpa [stmtNextScope, collectStmtBindNames] using hn))
      hexact hscope hbounded hruntime

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

private theorem compiledStmtStep_assignStorageAddrField
    {fields : List Field} {scope : List String} {name fieldName : String} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (_hfieldInScope : fieldName ∈ scope) :
    CompiledStmtStep fields scope (.assignVar name (Expr.storageAddr fieldName))
      [YulStmt.assign name (YulExpr.call "sload" [YulExpr.lit slot])] where
  compileOk := by
    have hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      CompilationModel.compileExprWithInternals, hNotMapping, hfind]
    rfl
  preserves runtime state extraFuel hexact hscope hbounded hruntime _ :=
    stmtStep_preserves_of_bindValue
      (execStmt_assignVar_of_evalExpr (evalExpr_storageAddr_of_findField_address hfind))
      (execIRStmts_singleton_assign_of_eval extraFuel
        (evalIRExpr_sload_of_findField_address hnoConflict hfind hruntime))
      (storageAddr_val_lt_modulus runtime.world _)
      (fun n hn => List.mem_cons_of_mem _ (by simpa [stmtNextScope, collectStmtBindNames] using hn))
      hexact hscope hbounded hruntime

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

private theorem stmtListGenericCore_singleton_setStorageWord_zeroOffset_singleSlot
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
    StmtListGenericCore fields scope [Stmt.setStorageWord fieldName 0 value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStorageWord_singleSlot_zeroOffset
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

private theorem stmtListGenericCore_singleton_calldatacopy_single
    {fields : List Field}
    {scope : List String}
    {destOffset sourceOffset size : Expr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope) :
    StmtListGenericCore fields scope [Stmt.calldatacopy destOffset sourceOffset size] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreDest with ⟨destIR, hdestIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreSource with
    ⟨sourceIR, hsourceIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreSize with ⟨sizeIR, hsizeIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_calldatacopy_single
      (hcoreDest := hcoreDest)
      (hinScopeDest := hinScopeDest)
      (hcoreSource := hcoreSource)
      (hinScopeSource := hinScopeSource)
      (hcoreSize := hcoreSize)
      (hinScopeSize := hinScopeSize)
      (hdestIR := hdestIR)
      (hsourceIR := hsourceIR)
      (hsizeIR := hsizeIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_returndatacopy_empty_single
    {fields : List Field}
    {scope : List String}
    {destOffset : Expr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope) :
    StmtListGenericCore fields scope
      [Stmt.returndataCopy destOffset (Expr.literal 0) (Expr.literal 0)] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreDest with ⟨destIR, hdestIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_returndatacopy_empty_single
      (hcoreDest := hcoreDest)
      (hinScopeDest := hinScopeDest)
      (hdestIR := hdestIR))
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

theorem stmtListGenericCore_of_supportedStmtList_calldatacopySingle_of_surface
    {fields : List Field}
    {scope : List String}
    {destOffset sourceOffset size : Expr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hinScopeSource : FunctionBody.exprBoundNamesInScope sourceOffset scope)
    (hcoreSize : FunctionBody.ExprCompileCore size)
    (hinScopeSize : FunctionBody.exprBoundNamesInScope size scope) :
    StmtListGenericCore fields scope [Stmt.calldatacopy destOffset sourceOffset size] :=
  stmtListGenericCore_singleton_calldatacopy_single
    (fields := fields)
    (scope := scope)
    (hcoreDest := hcoreDest)
    (hinScopeDest := hinScopeDest)
    (hcoreSource := hcoreSource)
    (hinScopeSource := hinScopeSource)
    (hcoreSize := hcoreSize)
    (hinScopeSize := hinScopeSize)

theorem stmtListGenericCore_of_supportedStmtList_returndataCopyEmptySingle_of_surface
    {fields : List Field}
    {scope : List String}
    {destOffset : Expr}
    (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hinScopeDest : FunctionBody.exprBoundNamesInScope destOffset scope) :
    StmtListGenericCore fields scope
      [Stmt.returndataCopy destOffset (Expr.literal 0) (Expr.literal 0)] :=
  stmtListGenericCore_singleton_returndatacopy_empty_single
    (fields := fields)
    (scope := scope)
    (hcoreDest := hcoreDest)
    (hinScopeDest := hinScopeDest)

theorem stmtListGenericCore_of_supportedStmtList_revertEmptySingle_of_surface
    {fields : List Field} {scope : List String} :
    StmtListGenericCore fields scope [Stmt.revertEmpty] :=
  StmtListGenericCore.cons compiledStmtStep_revertEmpty_single
    StmtListGenericCore.nil

theorem stmtListGenericCore_of_supportedStmtList_revertReturndataEmptySingle_of_surface
    {fields : List Field} {scope : List String} :
    StmtListGenericCore fields scope [Stmt.revertReturndata] :=
  StmtListGenericCore.cons compiledStmtStep_revertReturndata_empty_single
    StmtListGenericCore.nil


end Compiler.Proofs.IRGeneration
