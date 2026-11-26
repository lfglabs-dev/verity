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

/-- The oracle the source semantics uses for custom-error bytes is this one. -/
theorem sourceOracle_eq_denoteOracle : sourceOracle = SourceSemantics.denoteOracle := rfl

/-- The state conversion is field-for-field (the two structures coincide). -/
def toRuntimeState (s : DenoteState) : SourceSemantics.RuntimeState :=
  { world := s.world, immutable := s.immutable, bindings := s.bindings, selector := s.selector,
    externalCallOracle := fun n =>
      ⟨s.externalCallSucceeded n, s.externalCallReturnValues n, s.externalCallPostWorld n,
        s.externalCallRevertData n⟩,
    externalCallIndex := s.externalCallIndex,
    observedReturnWords := s.observedReturnWords, errors := s.errors }

@[simp] theorem toRuntimeState_world (s : DenoteState) :
    (toRuntimeState s).world = s.world := rfl

@[simp] theorem toRuntimeState_immutable (s : DenoteState) :
    (toRuntimeState s).immutable = s.immutable := rfl

@[simp] theorem toRuntimeState_bindings (s : DenoteState) :
    (toRuntimeState s).bindings = s.bindings := rfl

@[simp] theorem toRuntimeState_selector (s : DenoteState) :
    (toRuntimeState s).selector = s.selector := rfl

@[simp] theorem toRuntimeState_externalCallOracle (s : DenoteState) :
    (toRuntimeState s).externalCallOracle = fun n =>
      ⟨s.externalCallSucceeded n, s.externalCallReturnValues n, s.externalCallPostWorld n,
        s.externalCallRevertData n⟩ := rfl

@[simp] theorem toRuntimeState_externalCallIndex (s : DenoteState) :
    (toRuntimeState s).externalCallIndex = s.externalCallIndex := rfl

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

/-! ## Byte-call scope of the agreement

`Denote` executes closed byte transports (`ExternalCallModule.byteTransport`)
against an explicit byte adversary; `SourceSemantics` has no byte adversary.
The exact return buffer lives in the shared world (`ContractState.rawReturndata`):
both semantics install the callee's revert bytes after a caught failed call and
reset it after a successful legacy call, and every returndata reader consults it
first, so the agreement holds from every frame. Only statements with byte
transports are out of scope.
The IR proof fragments never contain byte transports (`SupportedStmtList` admits
only `ecmPureHashing` modules, and the contract surface rejects every ECM). -/

mutual
/-- No closed byte transport occurs in the statement or its nested bodies. -/
def stmtByteFree : Stmt → Bool
  | .ecm mod _ => mod.byteTransport.isNone
  | .ite _ thenBranch elseBranch => stmtListByteFree thenBranch && stmtListByteFree elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body | .forEachWhile _ _ _ body
  | .unsafeBlock _ body => stmtListByteFree body
  | .matchAdt _ _ branches => branchesByteFree branches
  | _ => true

def stmtListByteFree : List Stmt → Bool
  | [] => true
  | stmt :: rest => stmtByteFree stmt && stmtListByteFree rest

def branchesByteFree : List (String × List String × List Stmt) → Bool
  | [] => true
  | (_, _, body) :: rest => stmtListByteFree body && branchesByteFree rest
end

/-! ## Expression-level agreement -/

/-- Shorthand for expression-level agreement at one expression. -/
private abbrev ExprAgree (fields : List Field) (s : DenoteState) (e : Expr) : Prop :=
  Denote.evalExpr sourceOracle fields s e = SourceSemantics.evalExpr fields (toRuntimeState s) e

/-- Conditional-expression agreement, given agreement on all three operands. -/
private theorem denote_evalExpr_ite_eq (fields : List Field) (s : DenoteState)
    (c t e : Expr) (ihc : ExprAgree fields s c) (iht : ExprAgree fields s t)
    (ihe : ExprAgree fields s e) : ExprAgree fields s (.ite c t e) :=
  bindAgree ihc fun v => by
    by_cases h : (v != 0) = true
    · simpa [h] using iht
    · simpa [h] using ihe

/-- Both evaluators guard the reserved `exp` builtin lane on the same name
test, so the two-argument external-call arms agree branch-for-branch. -/
private theorem denote_evalExpr_externalCall_two_eq (fields : List Field) (s : DenoteState)
    (name : String) (base exponent : Expr) (ihb : ExprAgree fields s base)
    (ihe : ExprAgree fields s exponent) :
    ExprAgree fields s (.externalCall name [base, exponent]) := by
  have guard : ∀ (c : Bool) (x y : Option Nat),
      x = y → (if c then x else none) = (if c then y else none) := by
    intro c x y h; cases c <;> simp [h]
  exact guard _ _ _ (bindAgree ihb fun _ => bindAgree ihe fun _ => rfl)

theorem denote_evalExpr_eq (fields : List Field) (s : DenoteState) :
    ∀ e : Expr,
      Denote.evalExpr sourceOracle fields s e =
        SourceSemantics.evalExpr fields (toRuntimeState s) e
  | .literal _ | .param _ | .immutable _ | .constructorArg _ | .storage _ | .storageAddr _
  | .mappingChain _ [] | .mappingChain _ (_ :: _ :: _ :: _) | .localVar _ | .dynamicBytesEq ..
  | .storageArrayLength _ | .memoryArrayLength _ | .paramDynamicMemberLength ..
  | .paramDynamicMemberDataOffset .. | .paramDynamicMemberElement .. | .arrayLength _
  | .paramDynamicStaticComposite .. | .paramDynamicHeadWord .. | .arrayElementWord ..
  | .call .. | .staticcall .. | .delegatecall .. | .externalCall _ [] | .externalCall _ [_]
  | .externalCall _ (_ :: _ :: _ :: _) | .internalCall .. | .intrinsic .. | .forkIfAtLeast ..
  | .mulDiv512Down .. | .mulDiv512Up .. | .adtConstruct .. | .adtTag .. | .adtField .. | .abiLiteral ..
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue | .selfBalance
  | .blockTimestamp | .blockNumber | .blobbasefee | .baseFee | .gasPrice | .calldatasize
  | .returndataSize => rfl
  | .bitNot a | .logicalNot a | .mload a | .tload a | .calldataload a | .extcodesize a
  | .mapping _ a | .mappingWord _ a _ | .mappingPackedWord _ a _ _ | .mappingUint _ a
  | .mappingChain _ [a] | .structMember _ a _ | .storageArrayElement _ a | .arrayElement _ a
  | .arrayElementDynamicWord _ a _ | .arrayElementDynamicDataOffset _ a
  | .arrayElementDynamicMemberLength _ a _ | .arrayElementDynamicMemberDataOffset _ a _
  | .memoryArrayElement _ a | .returndataOptionalBoolAt a =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ => rfl
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b | .bitAnd a b
  | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b | .logicalAnd a b
  | .logicalOr a b | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b
  | .keccak256 a b | .mapping2 _ a b | .mapping2Word _ a b _ | .mappingChain _ [a, b]
  | .structMember2 _ a b _ | .arrayElementDynamicMemberElement _ a _ b =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ => rfl
  | .mulDivDown a b c | .mulDivUp a b c =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ =>
          bindAgree (denote_evalExpr_eq fields s c) fun _ => rfl
  | .ite c t e => denote_evalExpr_ite_eq fields s c t e (denote_evalExpr_eq fields s c)
      (denote_evalExpr_eq fields s t) (denote_evalExpr_eq fields s e)
  | .externalCall _ [base, exponent] => denote_evalExpr_externalCall_two_eq fields s _ base
      exponent (denote_evalExpr_eq fields s base) (denote_evalExpr_eq fields s exponent)

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
  | .revert => .revert .empty
  | .revertWithData data => .revert (.raw data)

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
        SourceSemantics.writeAddressKeyedMappingSlots,
        Verity.ContractState.withStorageChannel, Verity.ContractState.writeMap]
      congr 1
      funext storageKey
      by_cases hmap :
          storageKey =
            Verity.StorageKey.map slot (Verity.wordToAddress (Verity.Core.Uint256.ofNat k))
      · subst hmap; simp
      · simp
        cases storageKey with
        | slot s =>
            exact congrFun (storage_field_eq_of_rel h) s
        | _ => rfl

theorem writeUintKeyedMappingSlots_eq
    (w : Verity.ContractState) (slots : List Nat) (k v : Nat) :
    Denote.writeUintKeyedMappingSlots sourceOracle w slots k v =
      SourceSemantics.writeUintKeyedMappingSlots w slots k v := by
  cases slots with
  | nil => rfl
  | cons slot rest =>
      have h := storageRel_foldl k v id (slot :: rest) (storageRel_base w)
      simp only [Denote.writeUintKeyedMappingSlots,
        SourceSemantics.writeUintKeyedMappingSlots,
        Verity.ContractState.withStorageChannel, Verity.ContractState.writeMapUint]
      congr 1
      funext storageKey
      by_cases hmap :
          storageKey = Verity.StorageKey.mapUint slot (Verity.Core.Uint256.ofNat k)
      · subst hmap; simp
      · simp [hmap]
        cases storageKey with
        | slot s =>
            exact congrFun (storage_field_eq_of_rel h) s
        | _ => rfl

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
        SourceSemantics.writeAddressKeyedMapping2Slots,
        Verity.ContractState.withStorageChannel, Verity.ContractState.writeMap2]
      congr 1
      funext storageKey
      by_cases hmap :
          storageKey =
            Verity.StorageKey.map2 slot
              (Verity.wordToAddress (Verity.Core.Uint256.ofNat k1))
              (Verity.wordToAddress (Verity.Core.Uint256.ofNat k2))
      · subst hmap; simp
      · simp
        cases storageKey with
        | slot s =>
            exact congrFun (storage_field_eq_of_rel h) s
        | _ => rfl

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

@[simp] theorem bindValues_eq (b : List (String × Nat)) (ns : List String) (vs : List Nat) :
    Denote.bindValues b ns vs = SourceSemantics.bindValues b ns vs := by
  induction ns generalizing b vs with
  | nil => rfl
  | cons n ns ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
          simp only [Denote.bindValues, SourceSemantics.bindValues, bindValue_eq]
          exact ih _ _

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
    (h : ∀ ls : DenoteState, toStmtResult (runBody ls) = runBody' (toRuntimeState ls)) :
    ∀ (st : DenoteState) (index remaining : Nat),
      toStmtResult (Denote.execForEachLoop varName runBody st index remaining) =
        SourceSemantics.execForEachLoop varName runBody' (toRuntimeState st) index remaining
  | _, _, 0 => rfl
  | st, index, remaining + 1 => by
      let ls := { st with bindings :=
        SourceSemantics.bindValue st.bindings varName (SourceSemantics.wordNormalize index) }
      have hb := h ls
      rw [SourceSemantics.execForEachLoop_succ]
      simp only [toRuntimeState] at hb ⊢
      rw [← hb]
      show toStmtResult
          (match runBody ls with
            | .continue next => Denote.execForEachLoop varName runBody next (index + 1) remaining
            | .stop next => .stop next
            | .return value next => .return value next
            | .revert => .revert
            | .revertWithData data => .revertWithData data) = _
      cases runBody ls <;>
        first
          | rfl
          | exact execForEachLoop_agree h _ (index + 1) remaining

/-- One iteration of `execForEachWhileLoop_agree`: the body agrees, and the
continuation agrees by the induction hypothesis `ih`. -/
theorem execForEachWhileLoop_agree_step {varName : String}
    {evalGuard : DenoteState → Option Nat}
    {evalGuard' : SourceSemantics.RuntimeState → Option Nat}
    {runBody : DenoteState → StmtOutcome}
    {runBody' : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (h : ∀ ls : DenoteState, toStmtResult (runBody ls) = runBody' (toRuntimeState ls))
    (st : DenoteState) (index remaining : Nat)
    (ih : ∀ next : DenoteState,
      toStmtResult (Denote.execForEachWhileLoop varName evalGuard runBody next (index + 1)
          remaining) =
        SourceSemantics.execForEachWhileLoop varName evalGuard' runBody'
          (toRuntimeState next) (index + 1) remaining) :
    toStmtResult
        (match runBody { st with
            bindings := bindValue st.bindings varName (wordNormalize index) } with
        | .continue next =>
            Denote.execForEachWhileLoop varName evalGuard runBody next (index + 1) remaining
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
        | .revertWithData data => .revertWithData data) =
      (match runBody' { (toRuntimeState st) with
          bindings := SourceSemantics.bindValue st.bindings varName
            (SourceSemantics.wordNormalize index) } with
      | .continue next =>
          SourceSemantics.execForEachWhileLoop varName evalGuard' runBody' next (index + 1)
            remaining
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert payload => .revert payload) := by
  let ls := { st with bindings :=
    SourceSemantics.bindValue st.bindings varName (SourceSemantics.wordNormalize index) }
  have hb := h ls
  simp only [toRuntimeState] at hb ⊢
  rw [← hb]
  show toStmtResult
      (match runBody ls with
        | .continue next =>
            Denote.execForEachWhileLoop varName evalGuard runBody next (index + 1) remaining
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
        | .revertWithData data => .revertWithData data) = _
  cases runBody ls <;> first | rfl | exact ih _

theorem execForEachWhileLoop_agree {varName : String}
    {evalGuard : DenoteState → Option Nat}
    {evalGuard' : SourceSemantics.RuntimeState → Option Nat}
    {runBody : DenoteState → StmtOutcome}
    {runBody' : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (hg : ∀ ls : DenoteState, evalGuard ls = evalGuard' (toRuntimeState ls))
    (h : ∀ ls : DenoteState, toStmtResult (runBody ls) = runBody' (toRuntimeState ls)) :
    ∀ (st : DenoteState) (index remaining : Nat),
      toStmtResult (Denote.execForEachWhileLoop varName evalGuard runBody st index remaining) =
        SourceSemantics.execForEachWhileLoop varName evalGuard' runBody'
          (toRuntimeState st) index remaining
  | st, _, 0 => by
      rw [SourceSemantics.execForEachWhileLoop_zero, ← hg st]
      simp only [Denote.execForEachWhileLoop]
      cases evalGuard st <;> rfl
  | st, index, remaining + 1 => by
      rw [SourceSemantics.execForEachWhileLoop_succ, ← hg st]
      simp only [Denote.execForEachWhileLoop]
      cases evalGuard st with
      | none => rfl
      | some g =>
          by_cases hg0 : g = 0
          · simp only [if_pos hg0]
            rfl
          · simp only [if_neg hg0]
            exact execForEachWhileLoop_agree_step (evalGuard' := evalGuard') h st index
              remaining (fun next => execForEachWhileLoop_agree hg h next (index + 1) remaining)

theorem execForEachSetBitLoop_agree {varName : String}
    {runBody : DenoteState → StmtOutcome}
    {runBody' : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (h : ∀ ls : DenoteState, toStmtResult (runBody ls) = runBody' (toRuntimeState ls)) :
    ∀ (fuel : Nat) (st : DenoteState) (bitmap : Nat),
      toStmtResult (Denote.execForEachSetBitLoop varName runBody fuel st bitmap) =
        SourceSemantics.execForEachSetBitLoop varName runBody' fuel (toRuntimeState st) bitmap
  | 0, _, _ => rfl
  | fuel + 1, st, bitmap => by
      rw [SourceSemantics.execForEachSetBitLoop_succ]
      by_cases hbitmap : bitmap = 0
      · simp [Denote.execForEachSetBitLoop, hbitmap, toStmtResult]
      · let val := SourceSemantics.wordNormalize (SourceSemantics.msbIndex bitmap)
        let ls := { st with bindings := SourceSemantics.bindValue st.bindings varName val }
        have hb := h ls
        simp only [Denote.execForEachSetBitLoop, hbitmap, if_false, toRuntimeState] at hb ⊢
        rw [← hb]
        show toStmtResult
            (match runBody ls with
            | .continue next =>
                Denote.execForEachSetBitLoop varName runBody fuel next
                  (SourceSemantics.clearMsb bitmap)
            | .stop next => .stop next
            | .return value next => .return value next
            | .revert => .revert
            | .revertWithData data => .revertWithData data) = _
        cases runBody ls <;>
          first
            | rfl
            | exact execForEachSetBitLoop_agree h fuel _ (SourceSemantics.clearMsb bitmap)

section StatementTactics

/-- Generic discharge tactic for the non-recursive `execStmt` arms: align the
expression evaluators, split every residual match/ite, then close each leaf
definitionally or by the mapping-write/array bridges. -/
macro "denote_stmt_arm" : tactic =>
  `(tactic|
    (simp only [Denote.execStmt, SourceSemantics.execStmt,
       ← denote_evalExpr_eq, ← denote_evalExprList_eq]
     repeat' (split at * <;>
         try simp_all [toStmtResult, toRuntimeState,
         Verity.ContractState.readArray, Verity.ContractState.writeArray,
         writeAddressKeyedMappingSlots_eq, writeUintKeyedMappingSlots_eq,
         writeAddressKeyedMapping2Slots_eq, writeAddressKeyedMappingFieldSlots_eq,
         writeUintKeyedMappingFieldSlots_eq, writeAddressKeyedMapping2FieldSlots_eq,
         storageArraySetAt_eq,
         storageArrayDropLast?_eq,
         writeFixedUint128ArrayElementSlots_eq,
         SourceSemantics.eventFromResolvedArgs?,
         SourceSemantics.eventScratchWorldAfterEmit?])
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
             SourceSemantics.eventScratchWorldAfterEmit?]
         | (simp_all only [Option.bind_eq_some_iff]; aesop)))

end StatementTactics

theorem execStmt_forEachSetBit_eq (fields : List Field)
    (st : DenoteState) (v : String) (bitmap : Expr) (body : List Stmt)
    (hbody : ∀ ls : DenoteState,
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

/-- Shorthand for statement-level agreement at one statement. -/
private abbrev StmtAgree (fields : List Field) (st : DenoteState) (stmt : Stmt) : Prop :=
  toStmtResult (Denote.execStmt sourceOracle fields st stmt) =
    SourceSemantics.execStmt fields (toRuntimeState st) stmt

/-- Shorthand for statement-list agreement at one statement list. -/
private abbrev StmtListAgree (fields : List Field) (st : DenoteState) (stmts : List Stmt) :
    Prop :=
  toStmtResult (Denote.execStmtList sourceOracle fields st stmts) =
    SourceSemantics.execStmtList fields (toRuntimeState st) stmts

/-- `ite` agreement, given agreement on both branches from the same frame. -/
private theorem execStmt_ite_eq (fields : List Field) (st : DenoteState) (c : Expr)
    (t e : List Stmt) (iht : StmtListAgree fields st t)
    (ihe : StmtListAgree fields st e) : StmtAgree fields st (.ite c t e) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
  cases Denote.evalExpr sourceOracle fields st c with
  | none => rfl
  | some v =>
      by_cases hv : (v != 0) = true
      · simp only [if_pos hv]
        exact iht
      · simp only [if_neg hv]
        exact ihe

/-- `forEach` agreement, given agreement of the body from every frame. -/
private theorem execStmt_forEach_eq (fields : List Field) (st : DenoteState) (v : String)
    (cnt : Expr) (body : List Stmt)
    (hbody : ∀ ls : DenoteState, StmtListAgree fields ls body) :
    StmtAgree fields st (.forEach v cnt body) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
  cases Denote.evalExpr sourceOracle fields st cnt with
  | none => rfl
  | some bound =>
      exact execForEachLoop_agree
        (runBody' := fun ls => SourceSemantics.execStmtList fields ls body) hbody
        { st with bindings := Denote.bindValue st.bindings v (Denote.wordNormalize 0) }
        0 bound

/-- `forEachWhile` agreement, given agreement of the body from every frame. The
guard is evaluated by the same expression evaluator on both sides. -/
private theorem execStmt_forEachWhile_eq (fields : List Field) (st : DenoteState)
    (v : String) (cnt guard : Expr) (body : List Stmt)
    (hbody : ∀ ls : DenoteState, StmtListAgree fields ls body) :
    StmtAgree fields st (.forEachWhile v cnt guard body) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt, ← denote_evalExpr_eq]
  cases Denote.evalExpr sourceOracle fields st cnt with
  | none => rfl
  | some bound =>
      exact execForEachWhileLoop_agree
        (evalGuard' := fun ls => SourceSemantics.evalExpr fields ls guard)
        (runBody' := fun ls => SourceSemantics.execStmtList fields ls body)
        (fun ls => denote_evalExpr_eq fields ls guard) hbody
        { st with bindings := Denote.bindValue st.bindings v (Denote.wordNormalize 0) }
        0 bound

/-- `externalCallBind` agreement: both lanes read the same oracle answer. -/
private theorem execStmt_externalCallBind_eq (fields : List Field) (st : DenoteState)
    (resultVars : List String) (externalName : String) (args : List Expr) :
    StmtAgree fields st (.externalCallBind resultVars externalName args) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    ← denote_evalExprList_eq]
  cases Denote.evalExprList sourceOracle fields st args with
  | none => rfl
  | some _ =>
      have hw : (wordNormalize : Nat → Nat) = SourceSemantics.wordNormalize :=
        funext wordNormalize_eq
      by_cases h : st.externalCallSucceeded st.externalCallIndex = true
      · simp only [h, ite_true]
        by_cases harity :
            (st.externalCallReturnValues st.externalCallIndex).length != resultVars.length
        · simp [toStmtResult, toRuntimeState, h, harity]
        · simp [toStmtResult, toRuntimeState, h, harity, hw, bindValues_eq,
            SourceSemantics.returndataAfterCall]
      · simp [toStmtResult, toRuntimeState, h]

/-- `tryExternalCallBind` agreement: both lanes read the same oracle answer. -/
private theorem execStmt_tryExternalCallBind_eq (fields : List Field) (st : DenoteState)
    (successVar : String) (resultVars : List String) (externalName : String)
    (args : List Expr) :
    StmtAgree fields st (.tryExternalCallBind successVar resultVars externalName args) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    ← denote_evalExprList_eq]
  cases Denote.evalExprList sourceOracle fields st args with
  | none => rfl
  | some _ =>
      have hw : (wordNormalize : Nat → Nat) = SourceSemantics.wordNormalize :=
        funext wordNormalize_eq
      by_cases h : st.externalCallSucceeded st.externalCallIndex = true
      · simp only [h, ite_true]
        by_cases harity :
            (st.externalCallReturnValues st.externalCallIndex).length != resultVars.length
        · simp [toStmtResult, toRuntimeState, h, harity]
        · simp [toStmtResult, toRuntimeState, h, harity, hw, bindValue_eq, bindValues_eq,
            SourceSemantics.returndataAfterCall]
      · simp [toStmtResult, toRuntimeState, h, hw, bindValue_eq, bindValues_eq,
          SourceSemantics.returndataAfterCall]

/-- Agreement for an ECM without a closed byte transport: both lanes read the
same oracle answer. -/
private theorem execStmt_ecm_eq (fields : List Field) (st : DenoteState)
    (mod : ECM.ExternalCallModule) (args : List Expr) (hb : mod.byteTransport = none) :
    StmtAgree fields st (.ecm mod args) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt, hb,
    ← denote_evalExprList_eq]
  cases Denote.evalExprList sourceOracle fields st args with
  | none => rfl
  | some _ =>
      have hw : (wordNormalize : Nat → Nat) = SourceSemantics.wordNormalize :=
        funext wordNormalize_eq
      by_cases h : st.externalCallSucceeded st.externalCallIndex = true
      · simp only [h, ite_true]
        by_cases harity :
            (st.externalCallReturnValues st.externalCallIndex).length != mod.resultVars.length
        · simp [toStmtResult, toRuntimeState, h, harity]
        · simp [toStmtResult, toRuntimeState, h, harity, hw, bindValues_eq,
            SourceSemantics.returndataAfterCall]
      · simp [toStmtResult, toRuntimeState, h]

/-- `returnBytes` agreement: both lanes look up the same dynamic-array binding. -/
private theorem execStmt_returnBytes_eq (fields : List Field) (st : DenoteState)
    (name : String) : StmtAgree fields st (.returnBytes name) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    Denote.dynamicArrayBinding?, SourceSemantics.dynamicArrayBinding?,
    toRuntimeState_bindings]
  cases DynamicAbi.dynamicArrayBinding? st.bindings name <;> rfl

/-- Custom-error `require` agreement: both lanes build `customErrorBytes`. -/
private theorem execStmt_requireError_eq (fields : List Field) (st : DenoteState)
    (cond : Expr) (name : String) (args : List Expr) :
    StmtAgree fields st (.requireError cond name args) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    SourceSemantics.typedErrorRevertResult, sourceOracle_eq_denoteOracle,
    ← denote_evalExpr_eq, ← denote_evalExprList_eq]
  repeat' (split at * <;> try simp_all [toStmtResult, toRuntimeState])

/-- Custom-error `revert` agreement: both lanes build `customErrorBytes`. -/
private theorem execStmt_revertError_eq (fields : List Field) (st : DenoteState)
    (name : String) (args : List Expr) :
    StmtAgree fields st (.revertError name args) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    SourceSemantics.typedErrorRevertResult, sourceOracle_eq_denoteOracle,
    ← denote_evalExprList_eq]
  repeat' (split at * <;> try simp_all [toStmtResult, toRuntimeState])

/-- `revert(offset, size)` agreement: both lanes slice `byteMemory`. -/
private theorem execStmt_revertMemory_eq (fields : List Field) (st : DenoteState)
    (offset size : Expr) :
    StmtAgree fields st (.revertMemory offset size) := by
  simp only [StmtAgree, Denote.execStmt, SourceSemantics.execStmt,
    ← denote_evalExpr_eq]
  cases Denote.evalExpr sourceOracle fields st offset <;>
    cases Denote.evalExpr sourceOracle fields st size <;> rfl

/-- Bubbled-returndata agreement: both lanes prefer the same raw buffer. -/
private theorem execStmt_revertReturndata_eq (fields : List Field) (st : DenoteState) :
    StmtAgree fields st .revertReturndata := rfl

mutual

/-- Statement agreement on byte-free statements. Closed byte transports execute
against the byte adversary in `Denote` only, so they are excluded rather than
routed through the legacy word-return oracle. -/
theorem execStmt_eq (fields : List Field) :
    ∀ (st : DenoteState) (stmt : Stmt), stmtByteFree stmt = true →
      toStmtResult (Denote.execStmt sourceOracle fields st stmt) =
        SourceSemantics.execStmt fields (toRuntimeState st) stmt
  | _, .letVar .., _ | _, .assignVar .., _ | _, .setStorage .., _
  | _, .setStorageAddr .., _ | _, .setImmutable .., _ | _, .setStorageWord .., _
  | _, .setMapping .., _ | _, .setMappingUint .., _ | _, .setMappingWord .., _
  | _, .setMappingPackedWord .., _ | _, .setStructMember .., _ | _, .setMapping2 .., _
  | _, .setMapping2Word .., _ | _, .setStructMember2 .., _ | _, .setMappingChain .., _
  | _, .storageArrayPush .., _ | _, .storageArrayPop .., _ | _, .mstore .., _
  | _, .setStorageArrayElement .., _ | _, .tstore .., _
  | _, .return .., _ | _, .emit .., _ | _, .calldatacopy .., _
  | _, .returnValues .., _ | _, .require .., _ | _, .panicCode .., _
  | _, .panic .., _ => by denote_stmt_arm
  -- The raw lanes coincide; the word lanes use definitionally equal padded-copy mirrors.
  | _, .returndataCopy _ _ _, _ => by denote_stmt_arm; rfl
  | st, .requireError c n a, _ => execStmt_requireError_eq fields st c n a
  | st, .revertError n a, _ => execStmt_revertError_eq fields st n a
  | st, .ite c t e, hb =>
      have hb : stmtListByteFree t = true ∧ stmtListByteFree e = true := by
        simpa only [stmtByteFree, Bool.and_eq_true] using hb
      execStmt_ite_eq fields st c t e (execStmtList_eq fields st t hb.1)
        (execStmtList_eq fields st e hb.2)
  | st, .forEach v cnt body, hb =>
      execStmt_forEach_eq fields st v cnt body (execStmtList_eq fields · body hb)
  | st, .forEachSetBit v bitmap body, hb =>
      execStmt_forEachSetBit_eq fields st v bitmap body (execStmtList_eq fields · body hb)
  | st, .forEachWhile v cnt guard body, hb =>
      execStmt_forEachWhile_eq fields st v cnt guard body (execStmtList_eq fields · body hb)
  | st, .externalCallBind rv n args, _ => execStmt_externalCallBind_eq fields st rv n args
  | st, .tryExternalCallBind sv rv n args, _ =>
      execStmt_tryExternalCallBind_eq fields st sv rv n args
  | st, .ecm mod args, hb =>
      execStmt_ecm_eq fields st mod args (by simpa only [stmtByteFree, Option.isNone_iff_eq_none]
        using hb)
  | st, .returnBytes name, _ => execStmt_returnBytes_eq fields st name
  | st, .revertMemory offset size, _ => execStmt_revertMemory_eq fields st offset size
  | st, .revertReturndata, _ => execStmt_revertReturndata_eq fields st
  | _, .stop, _ | _, .returnArray .., _ | _, .returnStorageWords .., _
  | _, .returnCodeData .., _ | _, .revertEmpty, _
  | _, .internalCall .., _ | _, .internalCallAssign .., _ | _, .rawLog .., _
  | _, .unsafeBlock .., _ | _, .unsafeYul .., _ | _, .matchAdt .., _ => rfl

theorem execStmtList_eq (fields : List Field) :
    ∀ (st : DenoteState) (stmts : List Stmt), stmtListByteFree stmts = true →
      toStmtResult (Denote.execStmtList sourceOracle fields st stmts) =
        SourceSemantics.execStmtList fields (toRuntimeState st) stmts
  | _, [], _ => rfl
  | st, stmt :: rest, hb => by
      simp only [stmtListByteFree, Bool.and_eq_true] at hb
      simp only [Denote.execStmtList, SourceSemantics.execStmtList,
        ← execStmt_eq fields st stmt hb.1]
      cases Denote.execStmt sourceOracle fields st stmt <;>
        first
          | rfl
          | exact execStmtList_eq fields _ rest hb.2

end

end DenoteAgreement

end Compiler.Proofs.IRGeneration
