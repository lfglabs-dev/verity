import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Model.Denote

/-!
# Agreement between the compiler-free denotation and `SourceSemantics` (P4)

`Verity.Core.Model.Denote` mirrors `SourceSemantics` arm-for-arm, routing the
two compiler-engine dependencies (mapping-slot hashing and Keccak over a
memory slice) through a `DenoteOracle`. This file instantiates that oracle
with the real engines (`sourceOracle`) and proves that the two expression
evaluators agree on every expression (and expression list).

The proofs deliberately avoid `simp [Denote.evalExpr, SourceSemantics.evalExpr]`
and functional induction: realizing the derived equations / induction principle
for these ~90-arm matches exceeds the (non-configurable) realization budget,
which is also why `SourceSemantics` carries hand-rolled per-arm `rfl` lemmas.
Instead, every arm is closed definitionally (`rfl`) or by the bind-congruence
helper `bindAgree` plus the structural induction hypotheses.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

namespace DenoteAgreement

open Compiler.CompilationModel.Denote

/-- Canonical oracle: the engines `SourceSemantics` uses directly. -/
def sourceOracle : DenoteOracle :=
  { mappingSlot := Compiler.Proofs.abstractMappingSlot
    keccakMemorySlice := SourceSemantics.keccakMemorySlice }

/-- The state conversion is field-for-field (the two structures coincide). -/
def toRuntimeState (s : DenoteState) : SourceSemantics.RuntimeState :=
  { world := s.world, immutable := s.immutable, bindings := s.bindings, selector := s.selector }

@[simp] theorem toRuntimeState_world (s : DenoteState) :
    (toRuntimeState s).world = s.world := rfl

@[simp] theorem toRuntimeState_immutable (s : DenoteState) :
    (toRuntimeState s).immutable = s.immutable := rfl

@[simp] theorem toRuntimeState_bindings (s : DenoteState) :
    (toRuntimeState s).bindings = s.bindings := rfl

@[simp] theorem toRuntimeState_selector (s : DenoteState) :
    (toRuntimeState s).selector = s.selector := rfl

@[simp] theorem sourceOracle_mappingSlot :
    sourceOracle.mappingSlot = Compiler.Proofs.abstractMappingSlot := rfl

@[simp] theorem sourceOracle_keccakMemorySlice :
    sourceOracle.keccakMemorySlice = SourceSemantics.keccakMemorySlice := rfl

/-- Congruence for `Option.bind`: used to thread induction hypotheses through
the `do`-blocks shared by `Denote.evalExpr` and `SourceSemantics.evalExpr`. -/
theorem bindAgree {α β : Type} {o₁ o₂ : Option α} {f g : α → Option β}
    (h : o₁ = o₂) (hf : ∀ x, f x = g x) : o₁.bind f = o₂.bind g := by
  cases h
  exact congrArg _ (funext hf)

/-! ## Expression-level agreement -/

theorem denote_evalExpr_eq (fields : List Field) (s : DenoteState) :
    ∀ e : Expr,
      Denote.evalExpr sourceOracle fields s e =
        SourceSemantics.evalExpr fields (toRuntimeState s) e
  | .literal _ | .param _ | .immutable _ | .constructorArg _ | .storage _ | .storageAddr _
  | .mappingChain _ [] | .mappingChain _ (_ :: _ :: _ :: _) | .localVar _
  | .storageArrayLength _ | .dynamicBytesEq ..
  | .memoryArrayLength _ | .memoryArrayElement .. | .paramDynamicMemberLength ..
  | .paramDynamicMemberDataOffset .. | .paramDynamicMemberElement ..
  | .paramDynamicStaticComposite .. | .paramDynamicHeadWord ..
  | .arrayLength _ | .arrayElementWord ..
  | .call .. | .staticcall .. | .delegatecall .. | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall .. | .internalCall ..
  | .intrinsic .. | .forkIfAtLeast .. | .mulDiv512Down .. | .mulDiv512Up ..
  | .adtConstruct .. | .adtTag .. | .adtField ..
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue | .selfBalance
  | .blockTimestamp | .blockNumber | .blobbasefee | .calldatasize
  | .returndataSize => rfl
  | .bitNot a | .logicalNot a | .mload a | .tload a | .calldataload a
  | .mapping _ a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .mappingUint _ a | .mappingChain _ [a] | .structMember _ a _
  | .storageArrayElement _ a
  | .arrayElement _ a
  | .arrayElementDynamicWord _ a _
  | .arrayElementDynamicDataOffset _ a
  | .arrayElementDynamicMemberLength _ a _
  | .arrayElementDynamicMemberDataOffset _ a _ =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ => rfl
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
  | .byte a b | .signextend a b | .eq a b | .ge a b | .gt a b | .sgt a b
  | .lt a b | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b
  | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b
  | .keccak256 a b | .mapping2 _ a b | .mapping2Word _ a b _
  | .mappingChain _ [a, b]
  | .structMember2 _ a b _ =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ => rfl
  | .mulDivDown a b c | .mulDivUp a b c =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ =>
          bindAgree (denote_evalExpr_eq fields s c) fun _ => rfl
  | .arrayElementDynamicMemberElement _ a _ b =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ => rfl
  | .ite c t e =>
      bindAgree (denote_evalExpr_eq fields s c) fun v => by
        by_cases h : (v != 0) = true
        · simpa [h] using denote_evalExpr_eq fields s t
        · simpa [h] using denote_evalExpr_eq fields s e

theorem denote_evalExprList_eq (fields : List Field) (s : DenoteState) :
    ∀ es : List Expr,
      Denote.evalExprList sourceOracle fields s es =
        SourceSemantics.evalExprList fields (toRuntimeState s) es
  | [] => rfl
  | e :: rest =>
      bindAgree (denote_evalExpr_eq fields s e) fun _ =>
        bindAgree (denote_evalExprList_eq fields s rest) fun _ => rfl

/-! ## Statement-level agreement: outcome conversion and write bridges -/

/-- Outcome conversion between the mirrored result types. -/
def toStmtResult : StmtOutcome → SourceSemantics.StmtResult
  | .continue st => .continue (toRuntimeState st)
  | .stop st => .stop (toRuntimeState st)
  | .return v st => .return v (toRuntimeState st)
  | .revert => .revert

theorem storageArraySetAt_eq :
    ∀ (xs : List Verity.Core.Uint256) (idx : Nat) (v : Verity.Core.Uint256),
      Denote.storageArraySetAt xs idx v = SourceSemantics.storageArraySetAt xs idx v
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: rest, idx + 1, v => by
      simp only [Denote.storageArraySetAt, SourceSemantics.storageArraySetAt,
        storageArraySetAt_eq rest idx v]

theorem storageArrayDropLast?_eq :
    ∀ xs : List Verity.Core.Uint256,
      Denote.storageArrayDropLast? xs = SourceSemantics.storageArrayDropLast? xs
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
      simp only [Denote.storageArrayDropLast?, SourceSemantics.storageArrayDropLast?,
        storageArrayDropLast?_eq (y :: rest)]

/-- The Nat-level mapping-write storage view of `Denote` tracks the
`IRStorageSlot`-level view of `SourceSemantics` (see Denote header note 3). -/
def StorageRel (cur : Nat → Nat) (CUR : IRStorageSlot → IRStorageWord) : Prop :=
  ∀ n : Nat, cur (Denote.wordNormalize n) = (CUR (IRStorageSlot.ofNat n)).toNat

theorem storageRel_base (w : Verity.ContractState) :
    StorageRel (Denote.storageNatView w)
      (fun s => IRStorageWord.ofNat (w.storage s.toNat).val) := by
  intro n
  show (w.storage (Denote.wordNormalize (Denote.wordNormalize n))).val =
    ((w.storage ((IRStorageSlot.ofNat n).toNat)).val) % EvmYul.UInt256.size
  have hidem : Denote.wordNormalize (Denote.wordNormalize n) = Denote.wordNormalize n := by
    show n % Compiler.Constants.evmModulus % Compiler.Constants.evmModulus =
      n % Compiler.Constants.evmModulus
    exact Nat.mod_mod_of_dvd n dvd_rfl
  have hslot : (IRStorageSlot.ofNat n).toNat = Denote.wordNormalize n := by
    simp [SourceSemantics.UInt256_size_eq_UINT256_MODULUS]
    rfl
  rw [hidem, hslot,
    Nat.mod_eq_of_lt (by simpa [SourceSemantics.UInt256_size_eq_UINT256_MODULUS] using
      (w.storage (Denote.wordNormalize n)).isLt)]

theorem storageRel_step {cur : Nat → Nat} {CUR : IRStorageSlot → IRStorageWord}
    (base k v : Nat) (h : StorageRel cur CUR) :
    StorageRel (Denote.storeMappingEntryNat sourceOracle cur base k v)
      (Compiler.Proofs.abstractStoreMappingEntry CUR base k v) := by
  intro n
  show (if Denote.wordNormalize n =
          Denote.wordNormalize (sourceOracle.mappingSlot base k) then
        Denote.wordNormalize v
      else cur (Denote.wordNormalize n)) =
    ((if IRStorageSlot.ofNat n =
          IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot base k) then
        IRStorageWord.ofNat v
      else CUR (IRStorageSlot.ofNat n))).toNat
  have hcond : (Denote.wordNormalize n =
        Denote.wordNormalize (sourceOracle.mappingSlot base k)) ↔
      (IRStorageSlot.ofNat n =
        IRStorageSlot.ofNat (Compiler.Proofs.solidityMappingSlot base k)) := by
    constructor
    · intro hn
      apply IRStorageSlot.eq_of_toNat_eq
      change n % Verity.Core.UINT256_MODULUS =
        Compiler.Proofs.solidityMappingSlot base k % Verity.Core.UINT256_MODULUS
      change n % Verity.Core.UINT256_MODULUS =
        Compiler.Proofs.solidityMappingSlot base k % Verity.Core.UINT256_MODULUS at hn
      exact hn
    · intro hn
      have := congrArg IRStorageSlot.toNat hn
      change n % Verity.Core.UINT256_MODULUS =
        Compiler.Proofs.solidityMappingSlot base k % Verity.Core.UINT256_MODULUS
      simpa [SourceSemantics.UInt256_size_eq_UINT256_MODULUS] using this
  by_cases hc : Denote.wordNormalize n =
      Denote.wordNormalize (sourceOracle.mappingSlot base k)
  · rw [if_pos hc, if_pos (hcond.mp hc)]
    simp [SourceSemantics.UInt256_size_eq_UINT256_MODULUS]
    rfl
  · rw [if_neg hc, if_neg (fun hn => hc (hcond.mpr hn))]
    exact h n

theorem storageRel_foldl (k v : Nat) (f : Nat → Nat) :
    ∀ (slots : List Nat) {cur : Nat → Nat} {CUR : IRStorageSlot → IRStorageWord},
      StorageRel cur CUR →
        StorageRel
          (slots.foldl
            (fun c slot => Denote.storeMappingEntryNat sourceOracle c (f slot) k v) cur)
          (slots.foldl
            (fun C slot => Compiler.Proofs.abstractStoreMappingEntry C (f slot) k v) CUR)
  | [], _, _, h => h
  | slot :: rest, _, _, h =>
      storageRel_foldl k v f rest (storageRel_step (f slot) k v h)

/-- Common shape of the three fold-based mapping-write storage fields. -/
theorem storage_field_eq_of_rel {cur : Nat → Nat} {CUR : IRStorageSlot → IRStorageWord}
    (h : StorageRel cur CUR) :
    (fun s => ((cur (Denote.wordNormalize s) : Verity.Core.Uint256))) =
      (fun s => ((IRStorageWord.toNat (CUR (IRStorageSlot.ofNat s)) : Verity.Core.Uint256))) :=
  funext fun s => congrArg _ (h s)

theorem writeAddressKeyedMappingSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k v : Nat) :
    Denote.writeAddressKeyedMappingSlots sourceOracle w slots k v =
      SourceSemantics.writeAddressKeyedMappingSlots w slots k v := by
  cases slots with
  | nil => rfl
  | cons slot rest =>
      have h := storageRel_foldl k v id (slot :: rest) (storageRel_base w)
      simp only [Denote.writeAddressKeyedMappingSlots,
        SourceSemantics.writeAddressKeyedMappingSlots]
      congr 1
      exact storage_field_eq_of_rel h

theorem writeUintKeyedMappingSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k v : Nat) :
    Denote.writeUintKeyedMappingSlots sourceOracle w slots k v =
      SourceSemantics.writeUintKeyedMappingSlots w slots k v := by
  cases slots with
  | nil => rfl
  | cons slot rest =>
      have h := storageRel_foldl k v id (slot :: rest) (storageRel_base w)
      simp only [Denote.writeUintKeyedMappingSlots,
        SourceSemantics.writeUintKeyedMappingSlots]
      congr 1
      exact storage_field_eq_of_rel h

theorem writeAddressKeyedMapping2Slots_eq
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 v : Nat) :
    Denote.writeAddressKeyedMapping2Slots sourceOracle w slots k1 k2 v =
      SourceSemantics.writeAddressKeyedMapping2Slots w slots k1 k2 v := by
  cases slots with
  | nil => rfl
  | cons slot rest =>
      have h := storageRel_foldl k2 v (fun slot => Compiler.Proofs.abstractMappingSlot slot k1)
        (slot :: rest) (storageRel_base w)
      simp only [Denote.writeAddressKeyedMapping2Slots,
        SourceSemantics.writeAddressKeyedMapping2Slots]
      congr 1
      exact storage_field_eq_of_rel h

@[simp] theorem fieldIsTransient_eq (fields : List Field) (fieldName : String) :
    Denote.fieldIsTransient fields fieldName =
      SourceSemantics.fieldIsTransient fields fieldName := rfl

@[simp] theorem writeTransientTargets_eq
    (w : Verity.ContractState) (targets : List Nat) (v : Nat) :
    Denote.writeTransientTargets w targets v =
      SourceSemantics.writeTransientTargets w targets v := rfl

theorem writeAddressKeyedMappingFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k v : Nat) :
    Denote.writeAddressKeyedMappingFieldSlots sourceOracle fields fieldName w slots k v =
      SourceSemantics.writeAddressKeyedMappingFieldSlots fields fieldName w slots k v := by
  simp only [Denote.writeAddressKeyedMappingFieldSlots,
    SourceSemantics.writeAddressKeyedMappingFieldSlots]
  by_cases h : SourceSemantics.fieldIsTransient fields fieldName = true
  · simp [fieldIsTransient_eq, h, sourceOracle, writeTransientTargets_eq,
      Denote.wordNormalize, SourceSemantics.wordNormalize]
  · simp [fieldIsTransient_eq, h, writeAddressKeyedMappingSlots_eq]

theorem writeUintKeyedMappingFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k v : Nat) :
    Denote.writeUintKeyedMappingFieldSlots sourceOracle fields fieldName w slots k v =
      SourceSemantics.writeUintKeyedMappingFieldSlots fields fieldName w slots k v := by
  simp only [Denote.writeUintKeyedMappingFieldSlots,
    SourceSemantics.writeUintKeyedMappingFieldSlots]
  by_cases h : SourceSemantics.fieldIsTransient fields fieldName = true
  · simp [fieldIsTransient_eq, h, sourceOracle, writeTransientTargets_eq,
      Denote.wordNormalize, SourceSemantics.wordNormalize]
  · simp [fieldIsTransient_eq, h, writeUintKeyedMappingSlots_eq]

theorem writeAddressKeyedMapping2FieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 v : Nat) :
    Denote.writeAddressKeyedMapping2FieldSlots sourceOracle fields fieldName w slots k1 k2 v =
      SourceSemantics.writeAddressKeyedMapping2FieldSlots fields fieldName w slots k1 k2 v := by
  simp only [Denote.writeAddressKeyedMapping2FieldSlots,
    SourceSemantics.writeAddressKeyedMapping2FieldSlots]
  by_cases h : SourceSemantics.fieldIsTransient fields fieldName = true
  · simp [fieldIsTransient_eq, h, sourceOracle, writeTransientTargets_eq,
      Denote.wordNormalize, SourceSemantics.wordNormalize]
  · simp [fieldIsTransient_eq, h, writeAddressKeyedMapping2Slots_eq]

/-! ## Definitional write/helper bridges (the mirrors are byte-for-byte) -/

@[simp] theorem wordNormalize_eq (n : Nat) :
    Denote.wordNormalize n = SourceSemantics.wordNormalize n := rfl

@[simp] theorem bindValue_eq (b : List (String × Nat)) (n : String) (v : Nat) :
    Denote.bindValue b n v = SourceSemantics.bindValue b n v := rfl

@[simp] theorem valuesAsEventArgs_eq (vs : List Nat) :
    Denote.valuesAsEventArgs vs = SourceSemantics.valuesAsEventArgs vs :=
  match vs with
  | [] => rfl
  | _ :: rest => congrArg (List.cons _) (valuesAsEventArgs_eq rest)

@[simp] theorem writeUintSlots_eq (w : Verity.ContractState) (slots : List Nat) (v : Nat) :
    Denote.writeUintSlots w slots v = SourceSemantics.writeUintSlots w slots v := rfl

@[simp] theorem writeFixedUint128ArrayElementSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (size index value : Nat) :
    Denote.writeFixedUint128ArrayElementSlots w slots size index value =
      SourceSemantics.writeFixedUint128ArrayElementSlots w slots size index value := rfl

@[simp] theorem writeStorageWordSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (off v : Nat) :
    Denote.writeStorageWordSlots w slots off v =
      SourceSemantics.writeStorageWordSlots w slots off v := rfl

@[simp] theorem writeAddressSlots_eq (w : Verity.ContractState) (slots : List Nat) (v : Nat) :
    Denote.writeAddressSlots w slots v = SourceSemantics.writeAddressSlots w slots v := rfl

@[simp] theorem writeAddressKeyedMappingWordSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k off v : Nat) :
    Denote.writeAddressKeyedMappingWordSlots sourceOracle w slots k off v =
      SourceSemantics.writeAddressKeyedMappingWordSlots w slots k off v := rfl

@[simp] theorem writeAddressKeyedMappingPackedWordSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k off : Nat)
    (p : PackedBits) (v : Nat) :
    Denote.writeAddressKeyedMappingPackedWordSlots sourceOracle w slots k off p v =
      SourceSemantics.writeAddressKeyedMappingPackedWordSlots w slots k off p v := rfl

@[simp] theorem writeAddressKeyedMappingPackedWordFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k off : Nat)
    (p : PackedBits) (v : Nat) :
    Denote.writeAddressKeyedMappingPackedWordFieldSlots
        sourceOracle fields fieldName w slots k off p v =
      SourceSemantics.writeAddressKeyedMappingPackedWordFieldSlots
        fields fieldName w slots k off p v := rfl

@[simp] theorem writeAddressKeyedMapping2WordSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 off v : Nat) :
    Denote.writeAddressKeyedMapping2WordSlots sourceOracle w slots k1 k2 off v =
      SourceSemantics.writeAddressKeyedMapping2WordSlots w slots k1 k2 off v := rfl

@[simp] theorem writeAddressKeyedMapping2PackedWordSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 off : Nat)
    (p : PackedBits) (v : Nat) :
    Denote.writeAddressKeyedMapping2PackedWordSlots sourceOracle w slots k1 k2 off p v =
      SourceSemantics.writeAddressKeyedMapping2PackedWordSlots w slots k1 k2 off p v := rfl

@[simp] theorem writeAddressKeyedMapping2PackedWordFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 off : Nat)
    (p : PackedBits) (v : Nat) :
    Denote.writeAddressKeyedMapping2PackedWordFieldSlots
        sourceOracle fields fieldName w slots k1 k2 off p v =
      SourceSemantics.writeAddressKeyedMapping2PackedWordFieldSlots
        fields fieldName w slots k1 k2 off p v := rfl

@[simp] theorem writeAddressKeyedMappingChainSlots_eq
    (w : Verity.ContractState) (slots keys : List Nat) (v : Nat) :
    Denote.writeAddressKeyedMappingChainSlots sourceOracle w slots keys v =
      SourceSemantics.writeAddressKeyedMappingChainSlots w slots keys v := rfl

@[simp] theorem writeAddressKeyedMappingWordFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k off v : Nat) :
    Denote.writeAddressKeyedMappingWordFieldSlots sourceOracle fields fieldName w slots k off v =
      SourceSemantics.writeAddressKeyedMappingWordFieldSlots fields fieldName w slots k off v := rfl

@[simp] theorem writeAddressKeyedMapping2WordFieldSlots_eq
    (fields : List Field) (fieldName : String)
    (w : Verity.ContractState) (slots : List Nat) (k1 k2 off v : Nat) :
    Denote.writeAddressKeyedMapping2WordFieldSlots sourceOracle fields fieldName w slots k1 k2 off v =
      SourceSemantics.writeAddressKeyedMapping2WordFieldSlots fields fieldName w slots k1 k2 off v := rfl

@[simp] theorem writeStorageArray_eq
    (w : Verity.ContractState) (slot : Nat) (vs : List Verity.Core.Uint256) :
    Denote.writeStorageArray w slot vs = SourceSemantics.writeStorageArray w slot vs := rfl

@[simp] theorem packedBitsValid_eq (p : PackedBits) :
    Denote.packedBitsValid p = Compiler.CompilationModel.packedBitsValid p := rfl

/-! ## Statement-level agreement -/

theorem execForEachLoop_agree {varName : String}
    {runBody : DenoteState → StmtOutcome}
    {runBody' : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (h : ∀ ls, toStmtResult (runBody ls) = runBody' (toRuntimeState ls)) :
    ∀ (st : DenoteState) (index remaining : Nat),
      toStmtResult (Denote.execForEachLoop varName runBody st index remaining) =
        SourceSemantics.execForEachLoop varName runBody' (toRuntimeState st) index remaining
  | _, _, 0 => rfl
  | st, index, remaining + 1 => by
      have hb := h ⟨st.world,
        st.immutable,
        SourceSemantics.bindValue st.bindings varName (SourceSemantics.wordNormalize index),
        st.selector⟩
      rw [SourceSemantics.execForEachLoop_succ]
      simp only [toRuntimeState] at hb ⊢
      rw [← hb]
      show toStmtResult
          (match runBody ⟨st.world,
              st.immutable,
              SourceSemantics.bindValue st.bindings varName (SourceSemantics.wordNormalize index),
              st.selector⟩ with
            | .continue next => Denote.execForEachLoop varName runBody next (index + 1) remaining
            | .stop next => .stop next
            | .return value next => .return value next
            | .revert => .revert) = _
      cases runBody ⟨st.world,
          st.immutable,
          SourceSemantics.bindValue st.bindings varName (SourceSemantics.wordNormalize index),
          st.selector⟩ <;>
        first
          | rfl
          | exact execForEachLoop_agree h _ (index + 1) remaining

theorem execForEachSetBitLoop_agree {varName : String}
    {runBody : DenoteState → StmtOutcome}
    {runBody' : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (h : ∀ ls, toStmtResult (runBody ls) = runBody' (toRuntimeState ls)) :
    ∀ (fuel : Nat) (st : DenoteState) (bitmap : Nat),
      toStmtResult (Denote.execForEachSetBitLoop varName runBody fuel st bitmap) =
        SourceSemantics.execForEachSetBitLoop varName runBody' fuel (toRuntimeState st) bitmap
  | 0, _, _ => rfl
  | fuel + 1, st, bitmap => by
      rw [SourceSemantics.execForEachSetBitLoop_succ]
      by_cases hbitmap : bitmap = 0
      · simp [Denote.execForEachSetBitLoop, hbitmap, toStmtResult]
      · have hb := h ⟨st.world,
          st.immutable,
          SourceSemantics.bindValue st.bindings varName
            (SourceSemantics.wordNormalize (SourceSemantics.msbIndex bitmap)),
          st.selector⟩
        simp only [Denote.execForEachSetBitLoop, hbitmap, if_false, toRuntimeState] at hb ⊢
        rw [← hb]
        show toStmtResult
            (match runBody ⟨st.world,
                st.immutable,
                SourceSemantics.bindValue st.bindings varName
                  (SourceSemantics.wordNormalize (SourceSemantics.msbIndex bitmap)),
                st.selector⟩ with
            | .continue next =>
                Denote.execForEachSetBitLoop varName runBody fuel next
                  (SourceSemantics.clearMsb bitmap)
            | .stop next => .stop next
            | .return value next => .return value next
            | .revert => .revert) = _
        cases runBody ⟨st.world,
            st.immutable,
            SourceSemantics.bindValue st.bindings varName
              (SourceSemantics.wordNormalize (SourceSemantics.msbIndex bitmap)),
            st.selector⟩ <;>
          first
            | rfl
            | exact execForEachSetBitLoop_agree h fuel _ (SourceSemantics.clearMsb bitmap)

theorem execStmt_forEachSetBit_eq (fields : List Field)
    (st : DenoteState) (v : String) (bitmap : Expr) (body : List Stmt)
    (hbody : ∀ ls,
      toStmtResult (Denote.execStmtList sourceOracle fields ls body) =
        SourceSemantics.execStmtList fields (toRuntimeState ls) body) :
    toStmtResult
        (Denote.execStmt sourceOracle fields st (.forEachSetBit v bitmap body)) =
      SourceSemantics.execStmt fields (toRuntimeState st) (.forEachSetBit v bitmap body) := by
  simp only [Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
  cases Denote.evalExpr sourceOracle fields st bitmap with
  | none => rfl
  | some bits =>
      exact execForEachSetBitLoop_agree
        (runBody' := fun ls => SourceSemantics.execStmtList fields ls body)
        hbody 256 st bits

/-- Generic discharge tactic for the non-recursive `execStmt` arms: align the
expression evaluators, split every residual match/ite, then close each leaf
definitionally or by the mapping-write/array bridges. -/
macro "denote_stmt_arm" : tactic =>
  `(tactic|
    (simp only [Denote.execStmt, SourceSemantics.execStmt,
       ← denote_evalExpr_eq, ← denote_evalExprList_eq]
     repeat' (split <;>
         try simp_all [toStmtResult, toRuntimeState,
         writeAddressKeyedMappingSlots_eq, writeUintKeyedMappingSlots_eq,
         writeAddressKeyedMapping2Slots_eq, writeAddressKeyedMappingFieldSlots_eq,
         writeUintKeyedMappingFieldSlots_eq, writeAddressKeyedMapping2FieldSlots_eq,
         storageArraySetAt_eq,
         storageArrayDropLast?_eq,
         writeFixedUint128ArrayElementSlots_eq,
         SourceSemantics.eventFromResolvedArgs?,
         SourceSemantics.eventScratchMemoryAfterEmit?])
     all_goals subst_vars
     all_goals
       first
         | rfl
         | simp_all [toStmtResult, toRuntimeState,
             writeAddressKeyedMappingSlots_eq, writeUintKeyedMappingSlots_eq,
             writeAddressKeyedMapping2Slots_eq, writeAddressKeyedMappingFieldSlots_eq,
             writeUintKeyedMappingFieldSlots_eq, writeAddressKeyedMapping2FieldSlots_eq,
             storageArraySetAt_eq,
             storageArrayDropLast?_eq,
             writeFixedUint128ArrayElementSlots_eq,
             SourceSemantics.eventFromResolvedArgs?,
             SourceSemantics.eventScratchMemoryAfterEmit?]))

mutual

theorem execStmt_eq (fields : List Field) :
    ∀ (st : DenoteState) (stmt : Stmt),
      toStmtResult (Denote.execStmt sourceOracle fields st stmt) =
        SourceSemantics.execStmt fields (toRuntimeState st) stmt
  | _, .letVar n v | _, .assignVar n v => by denote_stmt_arm
  | _, .setStorage f v | _, .setStorageAddr f v | _, .setImmutable f v => by denote_stmt_arm
  | _, .setStorageWord f w v => by denote_stmt_arm
  | _, .setMapping f k v | _, .setMappingUint f k v => by denote_stmt_arm
  | _, .setMappingWord f k w v => by denote_stmt_arm
  | _, .setMappingPackedWord f k w p v => by denote_stmt_arm
  | _, .setStructMember f k m v => by denote_stmt_arm
  | _, .setMapping2 f k1 k2 v => by denote_stmt_arm
  | _, .setMapping2Word f k1 k2 w v => by denote_stmt_arm
  | _, .setStructMember2 f k1 k2 m v => by denote_stmt_arm
  | _, .setMappingChain f ks v => by denote_stmt_arm
  | _, .storageArrayPush f v | _, .storageArrayPop f => by denote_stmt_arm
  | _, .setStorageArrayElement f i v => by denote_stmt_arm
  | _, .mstore o v | _, .tstore o v => by denote_stmt_arm
  | _, .require _ _ | _, .requireError .. | _, .revertError .. | _, .panicCode _ => by denote_stmt_arm
  | _, .return v => by denote_stmt_arm
  | _, .stop => rfl
  | _, .emit n args => by denote_stmt_arm
  | st, .ite c t e => by
      simp only [Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
      cases Denote.evalExpr sourceOracle fields st c with
      | none => rfl
      | some v =>
          by_cases hv : (v != 0) = true
          · simp only [if_pos hv]
            exact execStmtList_eq fields st t
          · simp only [if_neg hv]
            exact execStmtList_eq fields st e
  | st, .forEach v cnt body => by
      simp only [Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
      cases Denote.evalExpr sourceOracle fields st cnt with
      | none => rfl
      | some bound =>
          exact execForEachLoop_agree
            (runBody' := fun ls => SourceSemantics.execStmtList fields ls body)
            (fun ls => execStmtList_eq fields ls body)
            ⟨st.world, st.immutable, Denote.bindValue st.bindings v (Denote.wordNormalize 0), st.selector⟩
            0 bound
  | st, .forEachSetBit v bitmap body =>
      execStmt_forEachSetBit_eq fields st v bitmap body (fun ls => execStmtList_eq fields ls body)
  | _, .returnValues .. | _, .returnArray ..
  | _, .returnBytes .. | _, .returnStorageWords .. | _, .returnCodeData .. | _, .calldatacopy ..
  | _, .returndataCopy .. | _, .revertReturndata .. | _, .internalCall .. | _, .internalCallAssign ..
  | _, .rawLog .. | _, .externalCallBind .. | _, .tryExternalCallBind .. | _, .ecm ..
  | _, .unsafeBlock .. | _, .unsafeYul .. | _, .matchAdt .. => rfl

theorem execStmtList_eq (fields : List Field) :
    ∀ (st : DenoteState) (stmts : List Stmt),
      toStmtResult (Denote.execStmtList sourceOracle fields st stmts) =
        SourceSemantics.execStmtList fields (toRuntimeState st) stmts
  | _, [] => rfl
  | st, stmt :: rest => by
      simp only [Denote.execStmtList, SourceSemantics.execStmtList,
        ← execStmt_eq fields st stmt]
      cases Denote.execStmt sourceOracle fields st stmt <;>
        first
          | rfl
          | exact execStmtList_eq fields _ rest

end

end DenoteAgreement

end Compiler.Proofs.IRGeneration
