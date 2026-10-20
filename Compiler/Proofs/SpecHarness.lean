/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.Proofs.MetaSpecs

namespace Compiler.Proofs.SpecHarness

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.MetaSpecs

/-!
# Declarative Table-Driven Compiler Invariant Harness (`SpecHarness`, Node M2)

This module replaces scattered per-feature `native_decide` smoke blocks with a
single declarative, kernel-checked (`by decide`, `0 native_decide`) table-driven
invariant harness:

1. **Structural Trust-Surface Collectors (`stmtListLowLevelMechanicsStructural`,
   `stmtListUnsafeReasonsStructural`, `structuralSiteUndischargedCount`)**:
   Total structural catamorphisms over `Expr` and `Stmt` that compute low-level
   mechanics, `unsafe` block reasons, and unproved local obligations directly in
   the Lean kernel without `WellFounded.fix` or `@[extern]` string hashing.
2. **Declarative Guard Boundary Descriptor (`GuardBoundaryCase`)**:
   Compact descriptor for equality (`tx == threshold`) and lower-bound
   (`tx ≥ threshold`) EVM security guards, together with a soundness bridge
   (`differentialGuardMetaSpec_of_checkGuardBoundary_eq_true`) producing a
   `DifferentialGuardMetaSpec` witness from `checkGuardBoundary g = true`.
3. **Table-Driven Suite Runner (`CompilerInvariantCase`, `checkCompilerInvariantSuite`)**:
   Verifies surface bitmasks, profile inclusion, complement-bit flagging
   (no silent fallthrough), undischarged trust-report counts, and security-guard
   mutation sensitivity across a 12-feature canonical suite
   (`canonicalCompilerFeatureSuite`) in a single `by decide` theorem
   (`all_cases_hold_of_checkCompilerInvariantSuite_eq_true`).
-/

/-! ## 1. Structural Kernel-Reducible Trust-Surface Collectors -/

mutual
/-- Structural catamorphism collecting low-level mechanic names from an `Expr`. -/
def exprLowLevelMechanicsStructural : Expr → List String
  | .intrinsic _ (.builtin "create2") _ args =>
      "create2" :: exprListLowLevelMechanicsStructural args
  | .intrinsic _ (.builtin "extcodecopy") _ args =>
      "extcodecopy" :: exprListLowLevelMechanicsStructural args
  | .intrinsic _ (.builtin "codecopy") _ args =>
      "codecopy" :: exprListLowLevelMechanicsStructural args
  | .call g t v io is oo os =>
      "call" :: (exprLowLevelMechanicsStructural g ++ exprLowLevelMechanicsStructural t ++
        exprLowLevelMechanicsStructural v ++ exprLowLevelMechanicsStructural io ++
        exprLowLevelMechanicsStructural is ++ exprLowLevelMechanicsStructural oo ++
        exprLowLevelMechanicsStructural os)
  | .staticcall g t io is oo os =>
      "staticcall" :: (exprLowLevelMechanicsStructural g ++ exprLowLevelMechanicsStructural t ++
        exprLowLevelMechanicsStructural io ++ exprLowLevelMechanicsStructural is ++
        exprLowLevelMechanicsStructural oo ++ exprLowLevelMechanicsStructural os)
  | .delegatecall g t io is oo os =>
      "delegatecall" :: (exprLowLevelMechanicsStructural g ++ exprLowLevelMechanicsStructural t ++
        exprLowLevelMechanicsStructural io ++ exprLowLevelMechanicsStructural is ++
        exprLowLevelMechanicsStructural oo ++ exprLowLevelMechanicsStructural os)
  | .returndataSize => ["returndataSize"]
  | .blobbasefee => ["blobbasefee"]
  | .tload a => "tload" :: exprLowLevelMechanicsStructural a
  | .returndataOptionalBoolAt a =>
      "returndataOptionalBoolAt" :: exprLowLevelMechanicsStructural a
  | .mload a => "mload" :: exprLowLevelMechanicsStructural a
  | .calldataload a => "calldataload" :: exprLowLevelMechanicsStructural a
  | .extcodesize a => "extcodesize" :: exprLowLevelMechanicsStructural a
  | .literal _ | .param _ | .constructorArg _ | .immutable _ | .storage _ | .storageAddr _
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue | .selfBalance
  | .blockTimestamp | .blockNumber | .baseFee | .gasPrice | .calldatasize | .localVar _
  | .arrayLength _ | .memoryArrayLength _ | .paramDynamicHeadWord _ _
  | .paramDynamicMemberLength _ _ | .paramDynamicMemberDataOffset _ _
  | .paramDynamicStaticComposite _ _ | .storageArrayLength _ | .dynamicBytesEq _ _
  | .adtTag _ _ | .adtField _ _ _ _ _ => []
  | .mapping _ k | .mappingWord _ k _ | .mappingPackedWord _ k _ _
  | .mappingUint _ k | .structMember _ k _ | .arrayElement _ k
  | .memoryArrayElement _ k | .arrayElementWord _ k _ _ | .arrayElementDynamicWord _ k _
  | .arrayElementDynamicDataOffset _ k | .arrayElementDynamicMemberLength _ k _
  | .arrayElementDynamicMemberDataOffset _ k _ | .storageArrayElement _ k
  | .paramDynamicMemberElement _ _ k | .bitNot k | .logicalNot k =>
      exprLowLevelMechanicsStructural k
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _
  | .keccak256 a b | .arrayElementDynamicMemberElement _ a _ b
  | .forkIfAtLeast _ a b | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b
  | .mod a b | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .ceilDiv a b | .wMulDown a b | .wDivUp a b
  | .min a b | .max a b =>
      exprLowLevelMechanicsStructural a ++ exprLowLevelMechanicsStructural b
  | .ite a b c | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprLowLevelMechanicsStructural a ++ exprLowLevelMechanicsStructural b ++
        exprLowLevelMechanicsStructural c
  | .mappingChain _ args | .externalCall _ args | .internalCall _ args
  | .intrinsic _ _ _ args | .adtConstruct _ _ args =>
      exprListLowLevelMechanicsStructural args

/-- Structural low-level mechanic collector over an expression list. -/
def exprListLowLevelMechanicsStructural : List Expr → List String
  | [] => []
  | e :: es => exprLowLevelMechanicsStructural e ++ exprListLowLevelMechanicsStructural es
end

mutual
/-- Structural catamorphism collecting low-level mechanic names from a `Stmt`. -/
def stmtLowLevelMechanicsStructural : Stmt → List String
  | .mstore o v =>
      "mstore" :: (exprLowLevelMechanicsStructural o ++ exprLowLevelMechanicsStructural v)
  | .tstore o v =>
      "tstore" :: (exprLowLevelMechanicsStructural o ++ exprLowLevelMechanicsStructural v)
  | .calldatacopy d s sz =>
      "calldatacopy" :: (exprLowLevelMechanicsStructural d ++
        exprLowLevelMechanicsStructural s ++ exprLowLevelMechanicsStructural sz)
  | .returndataCopy d s sz =>
      "returndataCopy" :: (exprLowLevelMechanicsStructural d ++
        exprLowLevelMechanicsStructural s ++ exprLowLevelMechanicsStructural sz)
  | .revertReturndata => ["revertReturndata"]
  | .unsafeYul frag => frag.mechanics.map LowLevelMechanic.toReportString
  | .letVar _ v | .assignVar _ v | .setStorage _ v | .setStorageAddr _ v
  | .setImmutable _ v | .setStorageWord _ _ v | .storageArrayPush _ v
  | .require v _ | .panicCode v | .return v | .returnCodeData v =>
      exprLowLevelMechanicsStructural v
  | .setStorageArrayElement _ k v | .setMapping _ k v | .setMappingWord _ k _ v
  | .setMappingPackedWord _ k _ _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v =>
      exprLowLevelMechanicsStructural k ++ exprLowLevelMechanicsStructural v
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v
  | .setStructMember2 _ k1 k2 _ v =>
      exprLowLevelMechanicsStructural k1 ++ exprLowLevelMechanicsStructural k2 ++
        exprLowLevelMechanicsStructural v
  | .setMappingChain _ keys v =>
      exprListLowLevelMechanicsStructural keys ++ exprLowLevelMechanicsStructural v
  | .requireError cond _ args =>
      exprLowLevelMechanicsStructural cond ++ exprListLowLevelMechanicsStructural args
  | .revertError _ args | .returnValues args | .emit _ args
  | .internalCall _ args | .internalCallAssign _ _ args
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args | .ecm _ args =>
      exprListLowLevelMechanicsStructural args
  | .rawLog topics dOff dSz =>
      exprListLowLevelMechanicsStructural topics ++
        exprLowLevelMechanicsStructural dOff ++ exprLowLevelMechanicsStructural dSz
  | .ite cond tB eB =>
      exprLowLevelMechanicsStructural cond ++
        stmtListLowLevelMechanicsStructural tB ++ stmtListLowLevelMechanicsStructural eB
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprLowLevelMechanicsStructural count ++ stmtListLowLevelMechanicsStructural body
  | .unsafeBlock _ body =>
      stmtListLowLevelMechanicsStructural body
  | .matchAdt _ scrutinee branches =>
      exprLowLevelMechanicsStructural scrutinee ++
        matchBranchesLowLevelMechanicsStructural branches
  | .storageArrayPop _ | .panic _ | .returnArray _ | .returnBytes _
  | .returnStorageWords _ | .revertEmpty | .stop => []

/-- Structural low-level mechanic collector over ADT match branches. -/
def matchBranchesLowLevelMechanicsStructural :
    List (String × List String × List Stmt) → List String
  | [] => []
  | (_, _, body) :: rest =>
      stmtListLowLevelMechanicsStructural body ++
        matchBranchesLowLevelMechanicsStructural rest

/-- Structural low-level mechanic collector over a `List Stmt`. -/
def stmtListLowLevelMechanicsStructural : List Stmt → List String
  | [] => []
  | s :: ss => stmtLowLevelMechanicsStructural s ++ stmtListLowLevelMechanicsStructural ss
end

mutual
/-- Structural catamorphism collecting `unsafe` block reasons from a `Stmt`. -/
def stmtUnsafeReasonsStructural : Stmt → List String
  | .unsafeBlock reason body => reason :: stmtListUnsafeReasonsStructural body
  | .unsafeYul frag => [frag.label]
  | .ite _ tB eB =>
      stmtListUnsafeReasonsStructural tB ++ stmtListUnsafeReasonsStructural eB
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListUnsafeReasonsStructural body
  | .matchAdt _ _ branches =>
      matchBranchesUnsafeReasonsStructural branches
  | _ => []

/-- Structural `unsafe` reason collector over ADT match branches. -/
def matchBranchesUnsafeReasonsStructural :
    List (String × List String × List Stmt) → List String
  | [] => []
  | (_, _, body) :: rest =>
      stmtListUnsafeReasonsStructural body ++ matchBranchesUnsafeReasonsStructural rest

/-- Structural `unsafe` reason collector over a `List Stmt`. -/
def stmtListUnsafeReasonsStructural : List Stmt → List String
  | [] => []
  | s :: ss => stmtUnsafeReasonsStructural s ++ stmtListUnsafeReasonsStructural ss
end

/-- Count of undischarged trust-surface items (deduplicated low-level mechanics,
unproved local obligations, and deduplicated `unsafe` block reasons) at a site. -/
def structuralSiteUndischargedCount
    (localObligations : List LocalObligation) (stmts : List Stmt) : Nat :=
  let mechanics := dedupPreserveSpec (stmtListLowLevelMechanicsStructural stmts)
  let unprovedObligations :=
    localObligations.filter (fun ob => ob.proofStatus != .proved)
  let unsafeReasons := dedupPreserveSpec (stmtListUnsafeReasonsStructural stmts)
  mechanics.length + unprovedObligations.length + unsafeReasons.length

/-! ## 2. Declarative Security-Guard Witness Descriptor (`GuardBoundaryCase`) -/

/-- Compact declarative descriptor for an EVM security guard and its boundary witnesses. -/
structure GuardBoundaryCase where
  /-- Threshold parameter (`0` for equality-to-zero guards; `minWords` for calldata bounds). -/
  threshold : Nat := 0
  /-- Accepted boundary input (`guard txOk = true`). -/
  txOk : Nat := 0
  /-- Rejected boundary input (`guard txBlocked = false`). -/
  txBlocked : Nat := 1
  /-- When `true`, guard checks `tx ≥ threshold`; when `false`, guard checks `tx == threshold`. -/
  isLowerBound : Bool := false
  deriving DecidableEq, Repr

/-- Evaluate the boolean security guard described by `g` on input `tx`. -/
def evalDeclarativeGuard (g : GuardBoundaryCase) (tx : Nat) : Bool :=
  if g.isLowerBound then
    decide (tx ≥ g.threshold)
  else
    tx == g.threshold

/-- Evaluate guarded execution under toggle `guardEnabled` for `g`. -/
def evalDeclarativeGuardExec
    (g : GuardBoundaryCase) (guardEnabled : Bool) (tx : Nat) : GuardVerdict :=
  if guardEnabled && !evalDeclarativeGuard g tx then
    .reverted
  else
    .allowed tx

/-- Executable check certifying that `g` is a valid `DifferentialGuardMetaSpec`. -/
def checkGuardBoundary (g : GuardBoundaryCase) : Bool :=
  evalDeclarativeGuard g g.txOk &&
    !evalDeclarativeGuard g g.txBlocked &&
    (evalDeclarativeGuardExec g true g.txBlocked !=
      evalDeclarativeGuardExec g false g.txBlocked)

/-- Soundness bridge: if `checkGuardBoundary g = true`, then `g` inhabits
`DifferentialGuardMetaSpec`. -/
theorem differentialGuardMetaSpec_of_checkGuardBoundary_eq_true
    {g : GuardBoundaryCase} (h : checkGuardBoundary g = true) :
    Nonempty (DifferentialGuardMetaSpec Nat GuardVerdict
      (evalDeclarativeGuard g) (evalDeclarativeGuardExec g)) := by
  simp only [checkGuardBoundary, Bool.and_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at h
  exact ⟨⟨g.txOk, g.txBlocked, h.1.1, h.1.2, h.2⟩⟩

/-! ## 3. Table-Driven Compiler Invariant Harness (`CompilerInvariantCase`) -/

/-- Canonical internal-helper effect lookup table for the invariant harness:
`_mint` reads and writes storage (`hasExternalInteraction = false`), while pure
helpers such as `_checkBounds` default to `EffectSummary.pure`. -/
def defaultHelperEffects (helperName : String) : EffectSummary :=
  if helperName == "_mint" then
    { readsStorage := true, writesStorage := true }
  else
    EffectSummary.pure

/-- A single row in the declarative table-driven compiler invariant suite. -/
structure CompilerInvariantCase where
  /-- Feature identifier for audit reporting. -/
  name : String
  /-- Representative `CompilationModel.Stmt` list exercising the feature. -/
  stmts : List Stmt
  /-- Site-local obligations attached to the feature test. -/
  localObligations : List LocalObligation := []
  /-- Expected `stmtListSurfaceMask` bitmask. -/
  expectedSurfaceMask : SurfaceMask
  /-- Capability profile mask against which this feature is audited. -/
  allowedProfileMask : SurfaceMask
  /-- Expected result of `maskSubset (stmtListSurfaceMask stmts) allowedProfileMask`. -/
  expectWithinAllowedProfile : Bool
  /-- Expected count of undischarged trust-surface entries. -/
  expectedUndischargedCount : Nat
  /-- Expected result of `stmtListRequiresFreePointerInit stmts` (Meta-Spec 5). -/
  expectRequiresFreePointer : Bool := false
  /-- Expected `EffectSummary` under `defaultHelperEffects` (Meta-Spec 6). -/
  expectedEffects : EffectSummary := EffectSummary.pure
  /-- Boundary witness pair certifying guard mutation sensitivity. -/
  guardWitness : GuardBoundaryCase

/-- Propositional invariant bundle certified for a single `CompilerInvariantCase`. -/
structure CompilerInvariantCaseHolds (c : CompilerInvariantCase) : Prop where
  /-- The computed `stmtListSurfaceMask` equals `expectedSurfaceMask`. -/
  surface_mask_eq :
    stmtListSurfaceMask c.stmts = c.expectedSurfaceMask
  /-- Profile inclusion `maskSubset` matches `expectWithinAllowedProfile`. -/
  profile_subset_eq :
    maskSubset (stmtListSurfaceMask c.stmts) c.allowedProfileMask =
      c.expectWithinAllowedProfile
  /-- Complement-mask flag check equals `!expectWithinAllowedProfile` (zero silent gap). -/
  complement_flag_eq :
    hasMask (stmtListSurfaceMask c.stmts) (~~~c.allowedProfileMask) =
      !c.expectWithinAllowedProfile
  /-- Structural undischarged trust-report count matches `expectedUndischargedCount`. -/
  undischarged_count_eq :
    structuralSiteUndischargedCount c.localObligations c.stmts =
      c.expectedUndischargedCount
  /-- Free-pointer prologue requirement matches `expectRequiresFreePointer` (Meta-Spec 5). -/
  free_pointer_req_eq :
    stmtListRequiresFreePointerInit c.stmts = c.expectRequiresFreePointer
  /-- Computed 6-flag `EffectSummary` matches `expectedEffects` (Meta-Spec 6). -/
  effect_summary_eq :
    stmtListEffectSummary defaultHelperEffects c.stmts = c.expectedEffects
  /-- The attached security guard satisfies `DifferentialGuardMetaSpec`. -/
  guard_meta_spec :
    Nonempty (DifferentialGuardMetaSpec Nat GuardVerdict
      (evalDeclarativeGuard c.guardWitness) (evalDeclarativeGuardExec c.guardWitness))

/-- Executable boolean checker for a single `CompilerInvariantCase`. -/
def checkCompilerInvariantCase (c : CompilerInvariantCase) : Bool :=
  let m := stmtListSurfaceMask c.stmts
  (m == c.expectedSurfaceMask) &&
    (maskSubset m c.allowedProfileMask == c.expectWithinAllowedProfile) &&
    (hasMask m (~~~c.allowedProfileMask) == !c.expectWithinAllowedProfile) &&
    (structuralSiteUndischargedCount c.localObligations c.stmts ==
      c.expectedUndischargedCount) &&
    (stmtListRequiresFreePointerInit c.stmts == c.expectRequiresFreePointer) &&
    (stmtListEffectSummary defaultHelperEffects c.stmts == c.expectedEffects) &&
    checkGuardBoundary c.guardWitness

/-- Executable boolean checker for an entire `List CompilerInvariantCase` suite. -/
def checkCompilerInvariantSuite (suite : List CompilerInvariantCase) : Bool :=
  suite.all checkCompilerInvariantCase

/-- Single-row soundness: `checkCompilerInvariantCase c = true` implies
`CompilerInvariantCaseHolds c`. -/
theorem compilerInvariantCaseHolds_of_check_eq_true
    {c : CompilerInvariantCase} (h : checkCompilerInvariantCase c = true) :
    CompilerInvariantCaseHolds c := by
  simp only [checkCompilerInvariantCase, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hmask, hsub⟩, hcompl⟩, htrust⟩, hfmp⟩, heff⟩, hguard⟩
  exact ⟨hmask, hsub, hcompl, htrust, hfmp, heff,
    differentialGuardMetaSpec_of_checkGuardBoundary_eq_true hguard⟩

/-- **Suite Soundness Theorem (`all_cases_hold_of_checkCompilerInvariantSuite_eq_true`)**:
If `checkCompilerInvariantSuite suite = true`, then every case `c ∈ suite`
satisfies all seven invariants of `CompilerInvariantCaseHolds c`. -/
theorem all_cases_hold_of_checkCompilerInvariantSuite_eq_true
    {suite : List CompilerInvariantCase}
    (h : checkCompilerInvariantSuite suite = true) :
    ∀ c ∈ suite, CompilerInvariantCaseHolds c := by
  intro c hc
  unfold checkCompilerInvariantSuite at h
  rw [List.all_eq_true] at h
  exact compilerInvariantCaseHolds_of_check_eq_true (h c hc)

/-! ## 4. Canonical 12-Feature Compiler Invariant Suite (`canonicalCompilerFeatureSuite`) -/

/-- Representative 12-case compiler feature suite covering storage reads/writes,
mappings, events, internal calls, ECM modules, `mulDiv512`, ADTs, `forEachSetBit`,
payable guards, callback bridges, inline Yul blocks, and low-level call mechanics. -/
def canonicalCompilerFeatureSuite : List CompilerInvariantCase :=
  [ -- 1. Scalar storage read and write
    { name := "storage_read_write"
      stmts := [Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1))]
      expectedSurfaceMask := bitStateRead
      allowedProfileMask := bitStateRead ||| bitConstructorRaw
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { readsStorage := true, writesStorage := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 2. Singleton mapping slot write
    { name := "mapping_slot_write"
      stmts := [Stmt.setMapping "balances" Expr.caller (Expr.literal 100)]
      expectedSurfaceMask := bitMappingWrite
      allowedProfileMask := bitStateRead ||| bitMappingWrite
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { writesStorage := true }
      guardWitness := { threshold := 1, txOk := 1, txBlocked := 0, isLowerBound := true } }
  , -- 3. Contract event emission
    { name := "event_emission"
      stmts := [Stmt.emit "Transfer" [Expr.caller, Expr.literal 100]]
      expectedSurfaceMask := bitEventEmit
      allowedProfileMask := bitStateRead ||| bitEventEmit
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { touchesMemory := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 4. Direct internal helper call with return assignment
    { name := "internal_helper_call"
      stmts := [Stmt.internalCallAssign ["out"] "_mint" [Expr.caller, Expr.literal 50]]
      expectedSurfaceMask := bitInternalCall
      allowedProfileMask := bitStateRead ||| bitInternalCall
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { readsStorage := true, writesStorage := true }
      guardWitness := { threshold := 2, txOk := 2, txBlocked := 0, isLowerBound := true } }
  , -- 5. Canonical External Call Module (`Stmt.ecm`)
    { name := "ecm_external_call"
      stmts := [Stmt.ecm (ECM.SolidityStaticCall.uint256Module "bal" 0x70a08231 1)
        [Expr.param "token", Expr.caller]]
      expectedSurfaceMask := bitExternalCall
      allowedProfileMask := bitStateRead ||| bitExternalCall
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := true
      expectedEffects := { readsStorage := true, touchesMemory := true, mayRevert := true }
      guardWitness := { threshold := 1, txOk := 1, txBlocked := 0, isLowerBound := true } }
  , -- 6. Full-precision 512-bit multiply-divide (`mulDiv512Down`)
    { name := "mulDiv512_full_precision"
      stmts := [Stmt.letVar "q"
        (Expr.mulDiv512Down (Expr.param "x") (Expr.param "y") (Expr.literal 1000))]
      expectedSurfaceMask := bitCoreGap ||| bitMulDiv512
      allowedProfileMask := bitCoreGap ||| bitMulDiv512
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := EffectSummary.pure
      guardWitness := { threshold := 1, txOk := 3, txBlocked := 0, isLowerBound := true } }
  , -- 7. Algebraic data type construction and pattern match (`matchAdt`)
    { name := "adt_construct_and_match"
      stmts := [Stmt.matchAdt "OptionUint"
        (Expr.adtConstruct "OptionUint" "Some" [Expr.literal 42])
        [("Some", ["v"], [Stmt.return (Expr.localVar "v")]),
         ("None", [], [Stmt.return (Expr.literal 0)])]]
      expectedSurfaceMask := bitCoreGap ||| bitStateRead ||| bitAdtSurface
      allowedProfileMask := bitCoreGap ||| bitStateRead ||| bitAdtSurface
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { readsStorage := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 8. Bitmap set-bit iteration (`forEachSetBit`)
    { name := "forEachSetBit_loop"
      stmts := [Stmt.forEachSetBit "bitIdx" (Expr.param "bitmap")
        [Stmt.assignVar "acc" (Expr.add (Expr.localVar "acc") (Expr.localVar "bitIdx"))]]
      expectedSurfaceMask := bitCoreGap ||| bitForEachSetBit
      allowedProfileMask := bitCoreGap ||| bitForEachSetBit
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := EffectSummary.pure
      guardWitness := { threshold := 1, txOk := 1, txBlocked := 0, isLowerBound := true } }
  , -- 9. Payable / `msg.value` guard surface
    { name := "payable_msgValue"
      stmts := [Stmt.require (Expr.eq Expr.msgValue (Expr.literal 0)) "non-payable",
                Stmt.return Expr.msgValue]
      expectedSurfaceMask := 0
      allowedProfileMask := bitStateRead
      expectWithinAllowedProfile := true
      expectedUndischargedCount := 0
      expectRequiresFreePointer := false
      expectedEffects := { mayRevert := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 10. External callback bridge (`externalCallBind` + local obligation)
    { name := "callback_bridge"
      stmts := [Stmt.externalCallBind ["cbOk"] "onFlashLoan" [Expr.caller, Expr.msgValue]]
      localObligations :=
        [{ name := "callback_reentrancy_frame"
           obligation := "Callback preserves lock invariant"
           proofStatus := .assumed }]
      expectedSurfaceMask := bitExternalCall
      allowedProfileMask := bitStateRead
      expectWithinAllowedProfile := false
      expectedUndischargedCount := 1
      expectRequiresFreePointer := false
      expectedEffects := { touchesMemory := true, hasExternalInteraction := true, mayRevert := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 11. Inline Yul / `unsafeBlock` escape hatch
    { name := "inline_yul_escape"
      stmts := [Stmt.unsafeBlock "manual-memory-zero"
        [Stmt.mstore (Expr.literal 0) (Expr.literal 0)]]
      expectedSurfaceMask := bitCoreGap ||| bitInlineYul
      allowedProfileMask := bitStateRead
      expectWithinAllowedProfile := false
      expectedUndischargedCount := 2
      expectRequiresFreePointer := true
      expectedEffects := { touchesMemory := true }
      guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
  , -- 12. Low-level EVM `staticcall` mechanics
    { name := "low_level_call_mechanics"
      stmts := [Stmt.letVar "ok"
        (Expr.staticcall (Expr.literal 50000) (Expr.param "target")
          (Expr.literal 0) (Expr.literal 32) (Expr.literal 0) (Expr.literal 32))]
      expectedSurfaceMask := bitCoreGap ||| bitLowLevelMem
      allowedProfileMask := bitStateRead
      expectWithinAllowedProfile := false
      expectedUndischargedCount := 1
      expectRequiresFreePointer := false
      expectedEffects := EffectSummary.pure
      guardWitness := { threshold := 4, txOk := 4, txBlocked := 0, isLowerBound := true } }
  ]

/-- The canonical feature suite contains exactly 12 modular feature cases. -/
theorem canonicalCompilerFeatureSuite_length :
    canonicalCompilerFeatureSuite.length = 12 := rfl

/-- Kernel-checked (`by decide`, `0 native_decide`) verification of all 12 feature cases. -/
theorem checkCompilerInvariantSuite_canonical_eq_true :
    checkCompilerInvariantSuite canonicalCompilerFeatureSuite = true := by
  decide

/-- Every case in the 12-feature canonical suite satisfies `CompilerInvariantCaseHolds`. -/
theorem canonicalCompilerFeatureSuite_all_hold :
    ∀ c ∈ canonicalCompilerFeatureSuite, CompilerInvariantCaseHolds c :=
  all_cases_hold_of_checkCompilerInvariantSuite_eq_true
    checkCompilerInvariantSuite_canonical_eq_true

/-! ## 5. Extended 16-Case Anti-Bug Effect & Prologue Suite (`canonicalEffectAndPrologueSuite`) -/

/-- Extended 16-case compiler invariant suite uniting the 12 canonical features
with 4 dedicated anti-bug regression cases covering `#2515`/`#2573` (`boolModule`
and `returnValues` free-pointer prologue synthesis), `#2422` (reverting view
functions with `writesStorage = false`), and `#2435` (internal helpers with
`hasExternalInteraction = false`). -/
def canonicalEffectAndPrologueSuite : List CompilerInvariantCase :=
  canonicalCompilerFeatureSuite ++
    [ -- 13. Staticcall bool ECM requires free-pointer prologue (#2515 / #2573)
      { name := "ecm_staticcall_bool"
        stmts := [Stmt.ecm (ECM.SolidityStaticCall.boolModule "ok" 0xa9059cbb 2)
          [Expr.param "token", Expr.caller, Expr.literal 1]]
        expectedSurfaceMask := bitExternalCall
        allowedProfileMask := bitStateRead ||| bitExternalCall
        expectWithinAllowedProfile := true
        expectedUndischargedCount := 0
        expectRequiresFreePointer := true
        expectedEffects := { readsStorage := true, touchesMemory := true, mayRevert := true }
        guardWitness := { threshold := 1, txOk := 1, txBlocked := 0, isLowerBound := true } }
    , -- 14. Reverting view function preserves storage (`writesStorage = false`, #2422)
      { name := "view_require_revert_no_storage_write"
        stmts := [Stmt.require (Expr.gt (Expr.storage "count") (Expr.literal 0)) "empty",
                  Stmt.return (Expr.storage "count")]
        expectedSurfaceMask := bitStateRead
        allowedProfileMask := bitStateRead
        expectWithinAllowedProfile := true
        expectedUndischargedCount := 0
        expectRequiresFreePointer := false
        expectedEffects := { readsStorage := true, writesStorage := false, mayRevert := true }
        guardWitness := { threshold := 1, txOk := 1, txBlocked := 0, isLowerBound := true } }
    , -- 15. Internal pure helper does not trigger CEI interaction (#2435)
      { name := "internal_pure_helper_no_cei"
        stmts := [Stmt.internalCall "_checkBounds" [Expr.param "x"]]
        expectedSurfaceMask := bitInternalCall
        allowedProfileMask := bitInternalCall
        expectWithinAllowedProfile := true
        expectedUndischargedCount := 0
        expectRequiresFreePointer := false
        expectedEffects := EffectSummary.pure
        guardWitness := { threshold := 0, txOk := 0, txBlocked := 1, isLowerBound := false } }
    , -- 16. Multi-word `returnValues` requires free-pointer prologue (#2515)
      { name := "returnValues_free_pointer_prologue"
        stmts := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
        expectedSurfaceMask := bitCoreGap
        allowedProfileMask := bitCoreGap
        expectWithinAllowedProfile := true
        expectedUndischargedCount := 0
        expectRequiresFreePointer := true
        expectedEffects := { touchesMemory := true }
        guardWitness := { threshold := 2, txOk := 2, txBlocked := 0, isLowerBound := true } }
    ]

/-- The extended anti-bug effect and prologue suite contains 16 cases. -/
theorem canonicalEffectAndPrologueSuite_length :
    canonicalEffectAndPrologueSuite.length = 16 := rfl

/-- Kernel-checked (`by decide`, `0 native_decide`) verification of all 16 cases. -/
theorem checkCompilerInvariantSuite_effectAndPrologue_eq_true :
    checkCompilerInvariantSuite canonicalEffectAndPrologueSuite = true := by
  decide

/-- Every case in the 16-case `canonicalEffectAndPrologueSuite` satisfies `CompilerInvariantCaseHolds`. -/
theorem canonicalEffectAndPrologueSuite_all_hold :
    ∀ c ∈ canonicalEffectAndPrologueSuite, CompilerInvariantCaseHolds c :=
  all_cases_hold_of_checkCompilerInvariantSuite_eq_true
    checkCompilerInvariantSuite_effectAndPrologue_eq_true

/-- Executable checker for the four concrete `VerifiedCompilerShim` instances (Meta-Spec 7). -/
def checkVerifiedCompilerShimSuite : Bool :=
  (mulDiv512VerifiedShim.shimImpl (6, 7, 2) 128 ==
    mulDiv512VerifiedShim.denoteSpec (6, 7, 2) 128) &&
  (scratchKeccakPairVerifiedShim.shimImpl (10, 20) 128 ==
    scratchKeccakPairVerifiedShim.denoteSpec (10, 20) 128) &&
  (transientLockVerifiedShim.shimImpl () (0, 999) ==
    transientLockVerifiedShim.denoteSpec () (0, 999)) &&
  (staticCallWordVerifiedShim.shimImpl (0xdead, 42) (128, 777) ==
    staticCallWordVerifiedShim.denoteSpec (0xdead, 42) (128, 777)) &&
  !mulDiv512VerifiedShim.effects.writesStorage &&
  !scratchKeccakPairVerifiedShim.effects.writesStorage &&
  !transientLockVerifiedShim.effects.writesStorage &&
  !staticCallWordVerifiedShim.effects.writesStorage

/-- Kernel-checked (`by decide`, `0 native_decide`) verification of the `VerifiedCompilerShim` suite. -/
theorem checkVerifiedCompilerShimSuite_eq_true :
    checkVerifiedCompilerShimSuite = true := by
  decide

end Compiler.Proofs.SpecHarness
