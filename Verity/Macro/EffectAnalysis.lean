/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.CompilationModel.Types
import Verity.Core

namespace Verity.Macro

open Compiler
open Compiler.CompilationModel

/-!
# Macro-Level Compositional Effect Summary Lattice (`MacroEffectSummary`)

Wires Meta-Spec 6 (`EffectSummary`) into `Verity/Macro/` so macro elaboration,
`#check_contract`, and `SpecGen` rely on compositional effect summaries rather
than ad-hoc syntax heuristics:

1. **6-Flag Join-Semilattice (`MacroEffectSummary`)**:
   Tracks `readsStorage`, `writesStorage`, `writesTransient`, `touchesMemory`,
   `hasExternalInteraction`, and `mayRevert` with verified semilattice laws
   (`join_comm`, `join_assoc`, `join_idem`, `join_bottom_left`, `join_bottom_right`).
2. **Inter-Procedural Fixpoint (`computeHelperEffectSummaries`)**:
   Propagates effect summaries across internal helper call graphs so pure,
   view, and storage-only helpers (`_requireOwner`, `_add`, `_burn`) do not
   falsely trigger `allow_post_interaction_writes` CEI barriers (`#2435`),
   while helpers transitively performing external calls strictly enforce CEI.
3. **View-Frame & CEI Soundness (`view_frame_of_writesStorage_false`,
   `internal_helper_not_cei_interaction`)**:
   Discharges storage-preservation obligations for reverting/branching view
   functions (`#2422`, `#1994`, `#1895`) and certifies internal-helper CEI
   precision (`#2435`).
-/

/-- Six-flag static effect summary join-semilattice over `CompilationModel` ASTs. -/
structure MacroEffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  writesTransient : Bool := false
  touchesMemory : Bool := false
  hasExternalInteraction : Bool := false
  mayRevert : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

namespace MacroEffectSummary

/-- Bottom element of the `MacroEffectSummary` join-semilattice (no effects). -/
def bottom : MacroEffectSummary := {}

/-- Alias for `bottom` matching `EffectSummary.pure` in Meta-Spec 6. -/
def pure : MacroEffectSummary := bottom

/-- Pointwise boolean join of two `MacroEffectSummary` values. -/
def join (a b : MacroEffectSummary) : MacroEffectSummary where
  readsStorage := a.readsStorage || b.readsStorage
  writesStorage := a.writesStorage || b.writesStorage
  writesTransient := a.writesTransient || b.writesTransient
  touchesMemory := a.touchesMemory || b.touchesMemory
  hasExternalInteraction := a.hasExternalInteraction || b.hasExternalInteraction
  mayRevert := a.mayRevert || b.mayRevert

/-- Alias for `join` matching `EffectSummary.merge` in Meta-Spec 6. -/
def merge (a b : MacroEffectSummary) : MacroEffectSummary :=
  join a b

@[simp]
theorem join_bottom_left (a : MacroEffectSummary) :
    join bottom a = a := by
  cases a
  rfl

@[simp]
theorem join_bottom_right (a : MacroEffectSummary) :
    join a bottom = a := by
  cases a
  simp [join, bottom]

theorem join_comm (a b : MacroEffectSummary) :
    join a b = join b a := by
  cases a
  cases b
  simp [join, Bool.or_comm]

theorem join_assoc (a b c : MacroEffectSummary) :
    join (join a b) c = join a (join b c) := by
  cases a
  cases b
  cases c
  simp [join, Bool.or_assoc]

@[simp]
theorem join_idem (a : MacroEffectSummary) :
    join a a = a := by
  cases a
  simp [join]

@[simp]
theorem join_writesStorage_eq_false_iff (a b : MacroEffectSummary) :
    (join a b).writesStorage = false ↔
      (a.writesStorage = false ∧ b.writesStorage = false) := by
  simp [join, Bool.or_eq_false_iff]

@[simp]
theorem join_writesTransient_eq_false_iff (a b : MacroEffectSummary) :
    (join a b).writesTransient = false ↔
      (a.writesTransient = false ∧ b.writesTransient = false) := by
  simp [join, Bool.or_eq_false_iff]

@[simp]
theorem join_hasExternalInteraction_eq_false_iff (a b : MacroEffectSummary) :
    (join a b).hasExternalInteraction = false ↔
      (a.hasExternalInteraction = false ∧ b.hasExternalInteraction = false) := by
  simp [join, Bool.or_eq_false_iff]

end MacroEffectSummary

export MacroEffectSummary (bottom join join_comm join_assoc join_idem)

/-- Check whether an External Call Module touches the EVM free-memory pointer (`0x40`). -/
def ecmTouchesMemory (mod : ECM.ExternalCallModule) : Bool :=
  mod.byteTransport.isSome

mutual
/-- Compositional effect summary of an `Expr` relative to `helperEffects`. -/
def exprEffectSummary (helperEffects : String → MacroEffectSummary) :
    Expr → MacroEffectSummary
  | .literal _ | .param _ | .constructorArg _ | .immutable _ | .localVar _
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue
  | .selfBalance | .blockTimestamp | .blockNumber | .blobbasefee
  | .baseFee | .gasPrice | .calldatasize | .returndataSize
  | .arrayLength _ | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ | .paramDynamicStaticComposite _ _
  | .dynamicBytesEq _ _ =>
      MacroEffectSummary.bottom
  | .storage _ | .storageAddr _ | .storageArrayLength _
  | .adtTag _ _ | .adtField _ _ _ _ _ =>
      { readsStorage := true }
  | .mapping _ k | .mappingWord _ k _ | .mappingPackedWord _ k _ _
  | .mappingUint _ k | .structMember _ k _ =>
      MacroEffectSummary.join { readsStorage := true } (exprEffectSummary helperEffects k)
  | .storageArrayElement _ k =>
      MacroEffectSummary.join
        { readsStorage := true, mayRevert := true }
        (exprEffectSummary helperEffects k)
  | .mapping2 _ k1 k2 | .mapping2Word _ k1 k2 _ | .structMember2 _ k1 k2 _ =>
      MacroEffectSummary.join { readsStorage := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects k1)
          (exprEffectSummary helperEffects k2))
  | .mappingChain _ keys =>
      MacroEffectSummary.join { readsStorage := true } (exprListEffectSummary helperEffects keys)
  | .mload o | .returndataOptionalBoolAt o =>
      MacroEffectSummary.join { touchesMemory := true } (exprEffectSummary helperEffects o)
  | .tload o | .calldataload o | .extcodesize o
  | .bitNot o | .logicalNot o =>
      exprEffectSummary helperEffects o
  | .keccak256 o s =>
      MacroEffectSummary.join { touchesMemory := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects o)
          (exprEffectSummary helperEffects s))
  | .call g t v io is oo os =>
      MacroEffectSummary.join
        { touchesMemory := true, hasExternalInteraction := true }
        (MacroEffectSummary.join (exprEffectSummary helperEffects g)
          (MacroEffectSummary.join (exprEffectSummary helperEffects t)
            (MacroEffectSummary.join (exprEffectSummary helperEffects v)
              (MacroEffectSummary.join (exprEffectSummary helperEffects io)
                (MacroEffectSummary.join (exprEffectSummary helperEffects is)
                  (MacroEffectSummary.join
                    (exprEffectSummary helperEffects oo)
                    (exprEffectSummary helperEffects os)))))))
  | .delegatecall g t io is oo os =>
      MacroEffectSummary.join
        { touchesMemory := true, hasExternalInteraction := true }
        (MacroEffectSummary.join (exprEffectSummary helperEffects g)
          (MacroEffectSummary.join (exprEffectSummary helperEffects t)
            (MacroEffectSummary.join (exprEffectSummary helperEffects io)
              (MacroEffectSummary.join (exprEffectSummary helperEffects is)
                (MacroEffectSummary.join
                  (exprEffectSummary helperEffects oo)
                  (exprEffectSummary helperEffects os))))))
  | .staticcall g t io is oo os =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (MacroEffectSummary.join (exprEffectSummary helperEffects g)
          (MacroEffectSummary.join (exprEffectSummary helperEffects t)
            (MacroEffectSummary.join (exprEffectSummary helperEffects io)
              (MacroEffectSummary.join (exprEffectSummary helperEffects is)
                (MacroEffectSummary.join
                  (exprEffectSummary helperEffects oo)
                  (exprEffectSummary helperEffects os))))))
  | .externalCall name args =>
      MacroEffectSummary.join
        { touchesMemory := true
          hasExternalInteraction := name != "__verity_exp"
          mayRevert := true }
        (exprListEffectSummary helperEffects args)
  | .internalCall fnName args =>
      MacroEffectSummary.join
        (helperEffects fnName)
        (exprListEffectSummary helperEffects args)
  | .intrinsic _ _ _ args | .adtConstruct _ _ args =>
      exprListEffectSummary helperEffects args
  | .arrayElement _ idx | .memoryArrayElement _ idx
  | .arrayElementWord _ idx _ _ | .arrayElementDynamicWord _ idx _
  | .arrayElementDynamicDataOffset _ idx
  | .arrayElementDynamicMemberLength _ idx _
  | .arrayElementDynamicMemberDataOffset _ idx _
  | .paramDynamicMemberElement _ _ idx =>
      MacroEffectSummary.join { mayRevert := true } (exprEffectSummary helperEffects idx)
  | .arrayElementDynamicMemberElement _ idx _ innerIdx =>
      MacroEffectSummary.join { mayRevert := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects idx)
          (exprEffectSummary helperEffects innerIdx))
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b
  | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b
  | .forkIfAtLeast _ a b =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects a)
        (exprEffectSummary helperEffects b)
  | .ite c t e | .mulDivDown c t e | .mulDivUp c t e =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects c)
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects t)
          (exprEffectSummary helperEffects e))
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      MacroEffectSummary.join { mayRevert := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects a)
          (MacroEffectSummary.join
            (exprEffectSummary helperEffects b)
            (exprEffectSummary helperEffects c)))

/-- Compositional effect summary over a list of expressions. -/
def exprListEffectSummary (helperEffects : String → MacroEffectSummary) :
    List Expr → MacroEffectSummary
  | [] => MacroEffectSummary.bottom
  | e :: es =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects e)
        (exprListEffectSummary helperEffects es)
end

mutual
/-- Single-pass compositional effect summary of a statement `s` relative to `helperEffects`. -/
def stmtEffectSummary (helperEffects : String → MacroEffectSummary) :
    Stmt → MacroEffectSummary
  | .setStorage _ v | .setStorageAddr _ v | .setStorageWord _ _ v
  | .storageArrayPush _ v =>
      MacroEffectSummary.join
        { writesStorage := true }
        (exprEffectSummary helperEffects v)
  | .storageArrayPop _ =>
      { readsStorage := true, writesStorage := true }
  | .setStorageArrayElement _ k v | .setMapping _ k v | .setMappingWord _ k _ v
  | .setMappingPackedWord _ k _ _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v =>
      MacroEffectSummary.join
        { writesStorage := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects k)
          (exprEffectSummary helperEffects v))
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v
  | .setStructMember2 _ k1 k2 _ v =>
      MacroEffectSummary.join
        { writesStorage := true }
        (exprListEffectSummary helperEffects [k1, k2, v])
  | .setMappingChain _ keys v =>
      MacroEffectSummary.join
        { writesStorage := true }
        (MacroEffectSummary.join
          (exprListEffectSummary helperEffects keys)
          (exprEffectSummary helperEffects v))
  | .tstore o v =>
      MacroEffectSummary.join
        { writesTransient := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects o)
          (exprEffectSummary helperEffects v))
  | .mstore o v =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects o)
          (exprEffectSummary helperEffects v))
  | .calldatacopy d s sz | .returndataCopy d s sz =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (exprListEffectSummary helperEffects [d, s, sz])
  | .returnValues vs =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (exprListEffectSummary helperEffects vs)
  | .returnBytes _ | .returnArray _ =>
      { touchesMemory := true }
  | .returnCodeData ptr =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (exprEffectSummary helperEffects ptr)
  | .returnStorageWords _ =>
      { readsStorage := true, touchesMemory := true }
  | .require cond _ =>
      MacroEffectSummary.join
        { mayRevert := true }
        (exprEffectSummary helperEffects cond)
  | .requireError cond _ args =>
      MacroEffectSummary.join
        { touchesMemory := true, mayRevert := true }
        (MacroEffectSummary.join
          (exprEffectSummary helperEffects cond)
          (exprListEffectSummary helperEffects args))
  | .revertError _ args =>
      MacroEffectSummary.join
        { touchesMemory := true, mayRevert := true }
        (exprListEffectSummary helperEffects args)
  | .panicCode code =>
      MacroEffectSummary.join
        { mayRevert := true }
        (exprEffectSummary helperEffects code)
  | .revertEmpty | .panic _ | .revertReturndata =>
      { mayRevert := true }
  | .internalCall h args | .internalCallAssign _ h args =>
      MacroEffectSummary.join
        (helperEffects h)
        (exprListEffectSummary helperEffects args)
  | .ecm mod args =>
      MacroEffectSummary.join
        { readsStorage := mod.readsState
          writesStorage := mod.writesState
          touchesMemory := ecmTouchesMemory mod
          hasExternalInteraction := mod.summaryMutability != .staticcall
          mayRevert := true }
        (exprListEffectSummary helperEffects args)
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args =>
      MacroEffectSummary.join
        { touchesMemory := true
          hasExternalInteraction := true
          mayRevert := true }
        (exprListEffectSummary helperEffects args)
  | .emit _ args =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (exprListEffectSummary helperEffects args)
  | .rawLog topics d s =>
      MacroEffectSummary.join
        { touchesMemory := true }
        (exprListEffectSummary helperEffects (d :: s :: topics))
  | .letVar _ v | .assignVar _ v | .return v | .setImmutable _ v =>
      exprEffectSummary helperEffects v
  | .stop =>
      MacroEffectSummary.bottom
  | .unsafeYul frag =>
      { writesStorage := !frag.scopeEffects.storageWrites.isEmpty
        writesTransient := frag.mechanics.contains .tstore
        touchesMemory := true
        hasExternalInteraction :=
          frag.mechanics.contains .call ||
            frag.mechanics.contains .delegatecall ||
            yulStmtListContainsExternalCall frag.stmts
        mayRevert := frag.controlFlow.mayRevert }
  | .ite cond thenB elseB =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects cond)
        (MacroEffectSummary.join
          (stmtListEffectSummary helperEffects thenB)
          (stmtListEffectSummary helperEffects elseB))
  | .forEach _ count body | .forEachSetBit _ count body =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects count)
        (stmtListEffectSummary helperEffects body)
  | .unsafeBlock _ body =>
      stmtListEffectSummary helperEffects body
  | .matchAdt _ scrutinee branches =>
      MacroEffectSummary.join
        (exprEffectSummary helperEffects scrutinee)
        (matchAdtBranchesEffectSummary helperEffects branches)

/-- Compositional effect summary over ADT match branches. -/
def matchAdtBranchesEffectSummary (helperEffects : String → MacroEffectSummary) :
    List (String × List String × List Stmt) → MacroEffectSummary
  | [] => MacroEffectSummary.bottom
  | (_, _, body) :: rest =>
      MacroEffectSummary.join
        (stmtListEffectSummary helperEffects body)
        (matchAdtBranchesEffectSummary helperEffects rest)

/-- Single-pass compositional effect summary of a statement list. -/
def stmtListEffectSummary (helperEffects : String → MacroEffectSummary) :
    List Stmt → MacroEffectSummary
  | [] => MacroEffectSummary.bottom
  | s :: ss =>
      MacroEffectSummary.join
        (stmtEffectSummary helperEffects s)
        (stmtListEffectSummary helperEffects ss)
end

/-! ## Inter-Procedural Fixpoint Computation Across Internal Helpers -/

/-- Look up a helper's `MacroEffectSummary` by name (checking direct,
`internal_`-prefixed, and `_internal_`-prefixed names), defaulting to `bottom`
when absent. -/
def lookupHelperEffectSummary
    (summaries : List (String × MacroEffectSummary)) (name : String) :
    MacroEffectSummary :=
  match summaries.find? (fun entry => entry.1 == name) with
  | some (_, summary) => summary
  | none =>
      let internalPrefixed := "internal_" ++ name
      match summaries.find? (fun entry => entry.1 == internalPrefixed) with
      | some (_, summary) => summary
      | none =>
          let underscorePrefixed := "_internal_" ++ name
          match summaries.find? (fun entry => entry.1 == underscorePrefixed) with
          | some (_, summary) => summary
          | none => MacroEffectSummary.bottom

/-- One Bellman-Ford / Kleene monotone iteration step over `functions`. -/
def computeHelperEffectSummariesStep
    (functions : List FunctionSpec)
    (summaries : List (String × MacroEffectSummary)) :
    List (String × MacroEffectSummary) :=
  let lookup := lookupHelperEffectSummary summaries
  functions.map fun fn =>
    (fn.name, stmtListEffectSummary lookup fn.body)

/-- Iterate `computeHelperEffectSummariesStep` for `fuel` rounds. -/
def iterateHelperEffectSummaries
    (functions : List FunctionSpec) :
    Nat → List (String × MacroEffectSummary) → List (String × MacroEffectSummary)
  | 0, summaries => summaries
  | fuel + 1, summaries =>
      iterateHelperEffectSummaries functions fuel
        (computeHelperEffectSummariesStep functions summaries)

/-- Compute the inter-procedural fixpoint of `MacroEffectSummary` across all
functions and internal helpers in `functions`. -/
def computeHelperEffectSummaries
    (functions : List FunctionSpec) : List (String × MacroEffectSummary) :=
  let initial := functions.map fun fn => (fn.name, MacroEffectSummary.bottom)
  iterateHelperEffectSummaries functions (functions.length + 1) initial

/-- Compute the inter-procedural `MacroEffectSummary` of a single `FunctionSpec`
within the contract function table `functions`. -/
def functionEffectSummary
    (functions : List FunctionSpec) (fn : FunctionSpec) : MacroEffectSummary :=
  let summaries := computeHelperEffectSummaries functions
  stmtListEffectSummary (lookupHelperEffectSummary summaries) fn.body

/-- Query whether helper `helperName` transitively performs a mutable external interaction. -/
def helperHasExternalInteraction
    (functions : List FunctionSpec) (helperName : String) : Bool :=
  let summaries := computeHelperEffectSummaries functions
  (lookupHelperEffectSummary summaries helperName).hasExternalInteraction

mutual
/-- Inter-procedural CEI violation check parameterized by `helperEffects`:
unlike the single-function syntax heuristic, internal helper calls only set the
`seenCall` interaction barrier if `(helperEffects h).hasExternalInteraction = true`,
and only count as state writes if `(helperEffects h).writesStorage` or
`(helperEffects h).writesTransient` holds (`#2435`). -/
def stmtListPreciseCEIViolation
    (helperEffects : String → MacroEffectSummary) :
    List Stmt → Bool → Option String
  | [], _ => none
  | s :: rest, seenCall =>
      match stmtInternalPreciseCEIViolation helperEffects s seenCall with
      | some msg => some msg
      | none =>
          let isCompound := match s with
            | .ite _ _ _ | .forEach _ _ _ | .forEachSetBit _ _ _
            | .unsafeBlock _ _ | .matchAdt _ _ _ => true
            | _ => false
          let isInternalHelperCall := match s with
            | .internalCall _ _ | .internalCallAssign _ _ _ => true
            | _ => false
          let eff := stmtEffectSummary helperEffects s
          let writesState := eff.writesStorage || eff.writesTransient
          let hasCall := eff.hasExternalInteraction
          if !isCompound && seenCall && writesState then
            some "state write after external call"
          else if !isCompound && !isInternalHelperCall && hasCall && writesState then
            some "state write in same statement as external call"
          else
            stmtListPreciseCEIViolation helperEffects rest (seenCall || hasCall)

/-- Compound-statement helper for `stmtListPreciseCEIViolation`. -/
def stmtInternalPreciseCEIViolation
    (helperEffects : String → MacroEffectSummary) :
    Stmt → Bool → Option String
  | .ite cond thenB elseB, seenCall =>
      let condCall := seenCall || (exprEffectSummary helperEffects cond).hasExternalInteraction
      match stmtListPreciseCEIViolation helperEffects thenB condCall with
      | some msg => some s!"in if-then branch: {msg}"
      | none =>
          match stmtListPreciseCEIViolation helperEffects elseB condCall with
          | some msg => some s!"in if-else branch: {msg}"
          | none => none
  | .forEach _ count body, seenCall | .forEachSetBit _ count body, seenCall =>
      let bodyEff := stmtListEffectSummary helperEffects body
      if bodyEff.hasExternalInteraction && (bodyEff.writesStorage || bodyEff.writesTransient) then
        some "loop body contains both external call and state write (subsequent iterations would violate CEI)"
      else
        let countCall := seenCall || (exprEffectSummary helperEffects count).hasExternalInteraction
        match stmtListPreciseCEIViolation helperEffects body countCall with
        | some msg => some s!"in loop body: {msg}"
        | none => none
  | .unsafeBlock _ body, seenCall =>
      match stmtListPreciseCEIViolation helperEffects body seenCall with
      | some msg => some s!"in unsafe block: {msg}"
      | none => none
  | .matchAdt _ scrutinee branches, seenCall =>
      let scrutCall := seenCall || (exprEffectSummary helperEffects scrutinee).hasExternalInteraction
      matchBranchesPreciseCEIViolation helperEffects branches scrutCall
  | .unsafeYul frag, seenCall =>
      let eff := stmtEffectSummary helperEffects (.unsafeYul frag)
      if (seenCall || eff.hasExternalInteraction) && (eff.writesStorage || eff.writesTransient) then
        some "raw Yul fragment writes state after an external call"
      else
        none
  | _, _ => none

/-- Branch-list helper for `stmtListPreciseCEIViolation`. -/
def matchBranchesPreciseCEIViolation
    (helperEffects : String → MacroEffectSummary) :
    List (String × List String × List Stmt) → Bool → Option String
  | [], _ => none
  | (variantName, _, body) :: rest, seenCall =>
      match stmtListPreciseCEIViolation helperEffects body seenCall with
      | some msg => some s!"in match branch '{variantName}': {msg}"
      | none => matchBranchesPreciseCEIViolation helperEffects rest seenCall
end

/-- Check whether `fn` is inter-procedurally CEI-compliant under `functions`
(i.e. `stmtListPreciseCEIViolation` finds `none`). -/
def functionIsInterprocedurallyCEICompliant
    (functions : List FunctionSpec) (fn : FunctionSpec) : Bool :=
  let summaries := computeHelperEffectSummaries functions
  let lookup := lookupHelperEffectSummary summaries
  (stmtListPreciseCEIViolation lookup fn.body false).isNone

/-- Conservative single-function helper effect summary that treats every internal
helper call as potentially reading/writing storage and performing an external call.
Matches the single-function assumption of `stmtListCEIViolation` in `Validation.lean`. -/
def conservativeHelperEffects (_ : String) : MacroEffectSummary :=
  { readsStorage := true
    writesStorage := true
    hasExternalInteraction := true }

/-- Resolve single-function conservative CEI false positives on `fn` using
inter-procedural `MacroEffectSummary` summaries (`#2435`): if `fn` would be
rejected by conservative single-function CEI solely because of internal helper
calls whose `hasExternalInteraction = false` (or `writesStorage = false`),
while `stmtListPreciseCEIViolation` with `lookupHelperEffectSummary summaries`
proves `fn` is inter-procedurally CEI-compliant, discharge the single-function
barrier on `fn`. Functions that genuinely violate CEI (e.g. writing storage
after a helper with `hasExternalInteraction = true`) are left untouched so
`#check_contract` still rejects them. -/
def resolveInternalHelperCEIFunction
    (summaries : List (String × MacroEffectSummary)) (fn : FunctionSpec) :
    FunctionSpec :=
  let lookup := lookupHelperEffectSummary summaries
  let conservativeViolation :=
    (stmtListPreciseCEIViolation conservativeHelperEffects fn.body false).isSome
  let preciseCompliant :=
    (stmtListPreciseCEIViolation lookup fn.body false).isNone
  if !fn.allowPostInteractionWrites && conservativeViolation && preciseCompliant then
    { fn with allowPostInteractionWrites := true }
  else
    fn

/-- Apply `resolveInternalHelperCEIFunction` across all functions in `functions`. -/
def resolveInternalHelperCEIFunctions
    (functions : List FunctionSpec) : List FunctionSpec :=
  let summaries := computeHelperEffectSummaries functions
  functions.map (resolveInternalHelperCEIFunction summaries)

/-- Upgrade a `CompilationModel` with inter-procedural `MacroEffectSummary`
CEI resolution across internal helper calls (`#2435`). -/
def resolveInternalHelperCEI (spec : CompilationModel) : CompilationModel :=
  { spec with functions := resolveInternalHelperCEIFunctions spec.functions }

/-! ## Formal Soundness Theorems -/

/-- Soundness contract connecting a static `MacroEffectSummary` to an abstract
state transition `step : State → State` and storage projection `storageOf : State → Storage`. -/
structure MacroEffectSoundness
    {State Storage : Type}
    (eff : MacroEffectSummary)
    (storageOf : State → Storage)
    (step : State → State) : Prop where
  /-- Absence of `writesStorage` guarantees storage preservation on all states. -/
  no_write_preserves_storage :
    eff.writesStorage = false → ∀ s : State, storageOf (step s) = storageOf s

/-- **Universal View-Frame Soundness (`view_frame_of_writesStorage_false`)**:
Whenever `MacroEffectSoundness eff storageOf step` holds and `eff.writesStorage = false`,
`storageOf (step s) = storageOf s` holds unconditionally, even when `eff.mayRevert = true`
or `staticcall` modules execute (`#2422`, `#1994`, `#1895`). -/
theorem view_frame_of_writesStorage_false
    {State Storage : Type}
    {eff : MacroEffectSummary}
    {storageOf : State → Storage}
    {step : State → State}
    (hsound : MacroEffectSoundness eff storageOf step)
    (hview : eff.writesStorage = false)
    (s : State) :
    storageOf (step s) = storageOf s :=
  hsound.no_write_preserves_storage hview s

/-- Sequential composition of `MacroEffectSoundness` across `MacroEffectSummary.join`. -/
theorem MacroEffectSoundness.seq
    {State Storage : Type}
    {eff₁ eff₂ : MacroEffectSummary}
    {storageOf : State → Storage}
    {step₁ step₂ : State → State}
    (h₁ : MacroEffectSoundness eff₁ storageOf step₁)
    (h₂ : MacroEffectSoundness eff₂ storageOf step₂) :
    MacroEffectSoundness (MacroEffectSummary.join eff₁ eff₂) storageOf (fun s => step₂ (step₁ s)) where
  no_write_preserves_storage hno s := by
    obtain ⟨hno₁, hno₂⟩ := (MacroEffectSummary.join_writesStorage_eq_false_iff eff₁ eff₂).mp hno
    exact (h₂.no_write_preserves_storage hno₂ (step₁ s)).trans
      (h₁.no_write_preserves_storage hno₁ s)

/-- Lift a state-equality witness `step s = s` into `MacroEffectSoundness`
for any `eff` and `storageOf` (`#2422`). -/
theorem MacroEffectSoundness.of_step_eq
    {State Storage : Type}
    (eff : MacroEffectSummary)
    (storageOf : State → Storage)
    (step : State → State)
    (heq : ∀ s : State, step s = s) :
    MacroEffectSoundness eff storageOf step where
  no_write_preserves_storage _ s := by
    rw [heq s]

/-- **CEI Precision for Internal Helpers (`internal_helper_not_cei_interaction`)**:
If `(helperEffects h).hasExternalInteraction = false` and `args` have no
external interactions, then `stmtEffectSummary helperEffects (.internalCall h args)`
has `hasExternalInteraction = false` (closing `#2435`). -/
theorem internal_helper_not_cei_interaction
    (helperEffects : String → MacroEffectSummary)
    (h : String) (args : List Expr)
    (hno : (helperEffects h).hasExternalInteraction = false)
    (hargs : (exprListEffectSummary helperEffects args).hasExternalInteraction = false := by rfl) :
    (stmtEffectSummary helperEffects (.internalCall h args)).hasExternalInteraction = false := by
  simp [stmtEffectSummary, MacroEffectSummary.join, hno, hargs]

/-- Companion CEI precision theorem for `Stmt.internalCallAssign`. -/
theorem internal_helper_assign_not_cei_interaction
    (helperEffects : String → MacroEffectSummary)
    (names : List String) (h : String) (args : List Expr)
    (hno : (helperEffects h).hasExternalInteraction = false)
    (hargs : (exprListEffectSummary helperEffects args).hasExternalInteraction = false := by rfl) :
    (stmtEffectSummary helperEffects (.internalCallAssign names h args)).hasExternalInteraction = false := by
  simp [stmtEffectSummary, MacroEffectSummary.join, hno, hargs]

/-! ## Executable `by decide` Witnesses -/

/-- Canonical internal helper table covering `#2435` (`_requireOwner`, `_add`, `_burn`)
and a genuine external-calling helper (`_notifyExternal`). -/
def canonicalHelperSpecs : List FunctionSpec :=
  [ { name := "_internal__requireOwner"
      params := []
      returnType := none
      returns := []
      isInternal := true
      body :=
        [ Stmt.require (Expr.eq Expr.caller (Expr.storageAddr "owner")) "not owner"
        , Stmt.stop ] }
  , { name := "_internal__add"
      params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
      returnType := some .uint256
      returns := [.uint256]
      isInternal := true
      body := [Stmt.return (Expr.add (Expr.param "a") (Expr.param "b"))] }
  , { name := "_internal__burn"
      params := [{ name := "amount", ty := .uint256 }]
      returnType := none
      returns := []
      isInternal := true
      body :=
        [ Stmt.internalCall "_internal__requireOwner" []
        , Stmt.setStorage "totalSupply"
            (Expr.sub (Expr.storage "totalSupply") (Expr.param "amount"))
        , Stmt.stop ] }
  , { name := "guardedBurnThenWrite"
      params := [{ name := "amount", ty := .uint256 }]
      returnType := none
      returns := []
      isInternal := false
      body :=
        [ Stmt.internalCall "_internal__requireOwner" []
        , Stmt.internalCallAssign ["next"] "_internal__add"
            [Expr.param "amount", Expr.literal 1]
        , Stmt.internalCall "_internal__burn" [Expr.localVar "next"]
        , Stmt.setStorage "counter" (Expr.localVar "next")
        , Stmt.stop ] }
  , { name := "_internal__notifyExternal"
      params := [{ name := "x", ty := .uint256 }]
      returnType := none
      returns := []
      isInternal := true
      body :=
        [ Stmt.externalCallBind ["echoed"] "echo" [Expr.param "x"]
        , Stmt.stop ] }
  , { name := "callHelperThenWriteViolatesCEI"
      params := [{ name := "x", ty := .uint256 }]
      returnType := none
      returns := []
      isInternal := false
      body :=
        [ Stmt.internalCall "_internal__notifyExternal" [Expr.param "x"]
        , Stmt.setStorage "counter" (Expr.param "x")
        , Stmt.stop ] }
  ]

/-- Kernel-checked (`by decide`) witness: `_requireOwner`, `_add`, and `_burn`
do NOT have external interactions, whereas `_notifyExternal` does (`#2435`). -/
theorem canonicalHelperSpecs_interaction_precision :
    helperHasExternalInteraction canonicalHelperSpecs "_internal__requireOwner" = false ∧
    helperHasExternalInteraction canonicalHelperSpecs "_internal__add" = false ∧
    helperHasExternalInteraction canonicalHelperSpecs "_internal__burn" = false ∧
    helperHasExternalInteraction canonicalHelperSpecs "_internal__notifyExternal" = true := by
  decide

/-- Kernel-checked (`by decide`) witness: calling `_requireOwner`, `_add`, and `_burn`
before `setStorage` is inter-procedurally CEI-compliant, while calling
`_notifyExternal` before `setStorage` is rejected as a CEI violation (`#2435`). -/
theorem canonicalHelperSpecs_cei_classification :
    let summaries := computeHelperEffectSummaries canonicalHelperSpecs
    let lookup := lookupHelperEffectSummary summaries
    stmtListPreciseCEIViolation lookup
      [ Stmt.internalCall "_internal__requireOwner" []
      , Stmt.internalCallAssign ["next"] "_internal__add" [Expr.param "amount", Expr.literal 1]
      , Stmt.internalCall "_internal__burn" [Expr.localVar "next"]
      , Stmt.setStorage "counter" (Expr.localVar "next") ] false = none ∧
    stmtListPreciseCEIViolation lookup
      [ Stmt.internalCall "_internal__notifyExternal" [Expr.param "x"]
      , Stmt.setStorage "counter" (Expr.param "x") ] false =
        some "state write after external call" := by
  decide

/-- Kernel-checked (`by decide`) witness: `resolveInternalHelperCEIFunctions`
discharges the conservative single-function CEI barrier on `guardedBurnThenWrite`
while preserving the CEI rejection on `callHelperThenWriteViolatesCEI` (`#2435`). -/
theorem canonicalHelperSpecs_resolve_cei :
    let resolved := resolveInternalHelperCEIFunctions canonicalHelperSpecs
    (resolved.find? (fun fn => fn.name == "guardedBurnThenWrite")).map
      (·.allowPostInteractionWrites) = some true ∧
    (resolved.find? (fun fn => fn.name == "callHelperThenWriteViolatesCEI")).map
      (·.allowPostInteractionWrites) = some false := by
  decide

/-- Kernel-checked (`by decide`) witness: a view body containing `require`,
`letVar`, and `return` has `writesStorage = false` and `mayRevert = true` (`#2422`). -/
theorem view_require_let_writesStorage_false :
    let eff := stmtListEffectSummary (fun _ => MacroEffectSummary.bottom)
      [ Stmt.letVar "cur" (Expr.storage "counter")
      , Stmt.require (Expr.gt (Expr.localVar "cur") (Expr.literal 0)) "empty"
      , Stmt.return (Expr.localVar "cur") ]
    eff.writesStorage = false ∧ eff.mayRevert = true := by
  decide

/-! ## Compact Algebraic `FootprintBitmask` & Universal Auto-Frame by `decide` -/

/-- Compact bitmask representation of a set of storage slot indices. -/
abbrev FootprintBitmask := Nat

/-- Encode a list of storage slot indices into a single `FootprintBitmask` (`Nat`). -/
def slotsToBitmask (slots : List Nat) : Nat :=
  slots.foldl (fun acc s => acc ||| (1 <<< s)) 0

/-- Check whether two footprint bitmasks are disjoint (`(maskA &&& maskB) == 0`). -/
def bitmaskDisjoint (maskA maskB : Nat) : Bool :=
  (maskA &&& maskB) == 0

/-- Check whether a single storage `slot` is disjoint from `writesMask`. -/
def slotBitDisjoint (writesMask : Nat) (slot : Nat) : Bool :=
  (writesMask &&& (1 <<< slot)) == 0

/-- Check whether a single storage `slot` bit is set inside `mask`. -/
def slotInBitmask (mask : Nat) (slot : Nat) : Bool :=
  (mask &&& (1 <<< slot)) == (1 <<< slot)

/-- Semantic footprint bound: whenever `op.run s = .success val s'`, every storage
`slot` whose bit is disjoint from `writesMask` is preserved (`s'.storage slot = s.storage slot`). -/
def StatementFootprintBound {α : Type} (writesMask : Nat) (op : Verity.Contract α) : Prop :=
  ∀ s val s', op.run s = .success val s' →
    ∀ slot, slotBitDisjoint writesMask slot = true → s'.storage slot = s.storage slot

/-- Pure computations satisfy `StatementFootprintBound` for any `writesMask`. -/
theorem StatementFootprintBound_pure {α : Type} (writesMask : Nat) (a : α) :
    StatementFootprintBound writesMask (Verity.pure a) := by
  intro s val s' hrun slot _
  cases hrun
  rfl

/-- Sequential `Verity.bind` composition preserves `StatementFootprintBound`. -/
theorem StatementFootprintBound_bind {α β : Type}
    {writesMask : Nat} {op₁ : Verity.Contract α} {op₂ : α → Verity.Contract β}
    (h₁ : StatementFootprintBound writesMask op₁)
    (h₂ : ∀ a, StatementFootprintBound writesMask (op₂ a)) :
    StatementFootprintBound writesMask (Verity.bind op₁ op₂) := by
  intro s val s' hrun slot hdisj
  have hbind := Verity.Contract.eq_of_run_success hrun
  unfold Verity.bind at hbind
  cases hop₁ : op₁ s with
  | revert msg s₁ =>
    simp [hop₁] at hbind
  | success a s₁ =>
    simp only [hop₁] at hbind
    have hrun₁ : op₁.run s = .success a s₁ := by simp [Verity.Contract.run, hop₁]
    have hrun₂ : (op₂ a).run s₁ = .success val s' := by simp [Verity.Contract.run, hbind]
    exact (h₂ a s₁ val s' hrun₂ slot hdisj).trans (h₁ s a s₁ hrun₁ slot hdisj)

/-- Monotonicity of `StatementFootprintBound` when `mask₂` covers `mask₁`. -/
theorem StatementFootprintBound_monotone {α : Type}
    {mask₁ mask₂ : Nat} {op : Verity.Contract α}
    (hsub : ∀ slot, slotBitDisjoint mask₂ slot = true → slotBitDisjoint mask₁ slot = true)
    (hbound : StatementFootprintBound mask₁ op) :
    StatementFootprintBound mask₂ op := by
  intro s val s' hrun slot hdisj
  exact hbound s val s' hrun slot (hsub slot hdisj)

/-- Storage reads preserve all slots under any `writesMask`. -/
theorem StatementFootprintBound_getStorage
    (writesMask : Nat) (slotDecl : Verity.StorageSlot Verity.Uint256) :
    StatementFootprintBound writesMask (Verity.getStorage slotDecl) := by
  intro s val s' hrun slot _
  cases hrun
  rfl

/-- Address storage reads preserve all word slots under any `writesMask`. -/
theorem StatementFootprintBound_getStorageAddr
    (writesMask : Nat) (slotDecl : Verity.StorageSlot Verity.Address) :
    StatementFootprintBound writesMask (Verity.getStorageAddr slotDecl) := by
  intro s val s' hrun slot _
  cases hrun
  rfl

/-- Address storage writes preserve all word slots under any `writesMask`. -/
theorem StatementFootprintBound_setStorageAddr
    (writesMask : Nat) (slotDecl : Verity.StorageSlot Verity.Address) (val : Verity.Address) :
    StatementFootprintBound writesMask (Verity.setStorageAddr slotDecl val) := by
  intro s _ s' hrun slot _
  cases hrun
  simp [Verity.ContractState.storage_writeAddrSlot]

/-- Mapping reads preserve all word slots under any `writesMask`. -/
theorem StatementFootprintBound_getMapping
    (writesMask : Nat) (slotDecl : Verity.StorageSlot (Verity.Address → Verity.Uint256))
    (key : Verity.Address) :
    StatementFootprintBound writesMask (Verity.getMapping slotDecl key) := by
  intro s val s' hrun slot _
  cases hrun
  rfl

/-- Mapping writes preserve all word slots under any `writesMask`. -/
theorem StatementFootprintBound_setMapping
    (writesMask : Nat) (slotDecl : Verity.StorageSlot (Verity.Address → Verity.Uint256))
    (key : Verity.Address) (val : Verity.Uint256) :
    StatementFootprintBound writesMask (Verity.setMapping slotDecl key val) := by
  intro s _ s' hrun slot _
  cases hrun
  simp [Verity.ContractState.storage, Verity.ContractState.writeMap]

/-- `Verity.require` guards preserve all word slots under any `writesMask`. -/
theorem StatementFootprintBound_require
    (writesMask : Nat) (cond : Bool) (msg : String) :
    StatementFootprintBound writesMask (Verity.require cond msg) := by
  intro s val s' hrun slot _
  have hreq := Verity.Contract.eq_of_run_success hrun
  unfold Verity.require at hreq
  split at hreq <;> simp_all

/-- Writing to `slotDecl` satisfies `StatementFootprintBound writesMask` whenever
`slotBitDisjoint writesMask slotDecl.slot = false` (discharged by `by decide`). -/
theorem StatementFootprintBound_setStorage
    (writesMask : Nat) (slotDecl : Verity.StorageSlot Verity.Uint256) (val : Verity.Uint256)
    (hmem : slotBitDisjoint writesMask slotDecl.slot = false := by decide) :
    StatementFootprintBound writesMask (Verity.setStorage slotDecl val) := by
  intro s _ s' hrun slot hdisj
  cases hrun
  have hne : slot ≠ slotDecl.slot := by
    intro heq
    rw [heq] at hdisj
    exact Bool.noConfusion (hmem.symm.trans hdisj)
  exact Verity.ContractState.storage_writeSlot_other s hne val

/-- Algebraic bitmask disjointness bridge: if `bitmaskDisjoint writesMask preservesMask = true`
and `slot` belongs to `preservesMask`, then `slotBitDisjoint writesMask slot = true`. -/
theorem slotBitDisjoint_of_bitmaskDisjoint
    {writesMask preservesMask slot : Nat}
    (hdisj : bitmaskDisjoint writesMask preservesMask = true)
    (hin : slotInBitmask preservesMask slot = true) :
    slotBitDisjoint writesMask slot = true := by
  unfold bitmaskDisjoint at hdisj
  unfold slotInBitmask at hin
  unfold slotBitDisjoint
  have h0 : writesMask &&& preservesMask = 0 := beq_iff_eq.mp hdisj
  have h1 : preservesMask &&& (1 <<< slot) = 1 <<< slot := beq_iff_eq.mp hin
  rw [beq_iff_eq, ← h1, ← Nat.and_assoc, h0, Nat.zero_and]

/-- **Universal Auto-Frame for Untouched Slot (`eval_preserves_untouched_slot_of_bitmask_disjoint`)**:
Whenever `StatementFootprintBound writesMask op` holds and `slotBitDisjoint writesMask slot = true`
(discharged automatically by `by decide`), `s'.storage slot = s.storage slot`. -/
theorem eval_preserves_untouched_slot_of_bitmask_disjoint
    {α : Type} {writesMask : Nat} {op : Verity.Contract α}
    {s : Verity.ContractState} {val : α} {s' : Verity.ContractState}
    (hbound : StatementFootprintBound writesMask op)
    (hrun : op.run s = .success val s')
    (slot : Nat)
    (hdisj : slotBitDisjoint writesMask slot = true := by decide) :
    s'.storage slot = s.storage slot :=
  hbound s val s' hrun slot hdisj

/-- Unconditional `.snd` projection variant of `eval_preserves_untouched_slot_of_bitmask_disjoint`
(covering both `.success` and `.revert` outcomes). -/
theorem eval_preserves_untouched_slot_snd_of_bitmask_disjoint
    {α : Type} {writesMask : Nat} {op : Verity.Contract α}
    (hbound : StatementFootprintBound writesMask op)
    (s : Verity.ContractState) (slot : Nat)
    (hdisj : slotBitDisjoint writesMask slot = true := by decide) :
    ((op.run s).snd).storage slot = s.storage slot := by
  unfold Verity.Contract.run
  cases hop : op s with
  | revert msg _ => rfl
  | success val s' =>
    have hrun : op.run s = .success val s' := by simp [Verity.Contract.run, hop]
    exact hbound s val s' hrun slot hdisj

/-- **Universal Auto-Frame for Preserved Bitmask (`eval_preserves_preserved_mask_of_bitmask_disjoint`)**:
Whenever `StatementFootprintBound writesMask op` holds and
`bitmaskDisjoint writesMask preservesMask = true` (discharged by `by decide`),
every `slot` in `preservesMask` is invariant (`s'.storage slot = s.storage slot`). -/
theorem eval_preserves_preserved_mask_of_bitmask_disjoint
    {α : Type} {writesMask preservesMask : Nat} {op : Verity.Contract α}
    {s : Verity.ContractState} {val : α} {s' : Verity.ContractState}
    (hbound : StatementFootprintBound writesMask op)
    (hrun : op.run s = .success val s')
    (hdisj : bitmaskDisjoint writesMask preservesMask = true := by decide) :
    ∀ slot, slotInBitmask preservesMask slot = true →
      s'.storage slot = s.storage slot := by
  intro slot hin
  exact hbound s val s' hrun slot (slotBitDisjoint_of_bitmaskDisjoint hdisj hin)

/-- Unconditional `.snd` projection variant of `eval_preserves_preserved_mask_of_bitmask_disjoint`
(covering both `.success` and `.revert` outcomes). -/
theorem eval_preserves_preserved_mask_snd_of_bitmask_disjoint
    {α : Type} {writesMask preservesMask : Nat} {op : Verity.Contract α}
    (hbound : StatementFootprintBound writesMask op)
    (s : Verity.ContractState)
    (hdisj : bitmaskDisjoint writesMask preservesMask = true := by decide)
    (slot : Nat)
    (hin : slotInBitmask preservesMask slot = true := by decide) :
    ((op.run s).snd).storage slot = s.storage slot :=
  eval_preserves_untouched_slot_snd_of_bitmask_disjoint
    hbound s slot (slotBitDisjoint_of_bitmaskDisjoint hdisj hin)

/-!
## 11. CEI Write-After-External-Call and Read-Only Reentrancy Effect Checkers

`hasWriteAfterExternalCall` and `hasExternalCallBeforeStorageRead` provide composable
effect-analysis predicates for detecting post-interaction storage writes (standard CEI
violations) and post-interaction storage reads (read-only reentrancy / stale-view hazards).
-/

mutual
  /-- Check whether a single statement internally performs a storage write after an external call. -/
  def stmtWritesStorageAfterExternalCall
      (helperEffects : String → MacroEffectSummary) : Stmt → Bool
    | .ite cond thenBranch elseBranch =>
      let condEff := exprEffectSummary helperEffects cond
      let (_, thenViol) := stmtListWriteAfterCallScan helperEffects thenBranch condEff.hasExternalInteraction
      let (_, elseViol) := stmtListWriteAfterCallScan helperEffects elseBranch condEff.hasExternalInteraction
      thenViol || elseViol
    | .forEach _ count body | .forEachSetBit _ count body =>
      let countEff := exprEffectSummary helperEffects count
      let (bodyCalls, bodyViol) := stmtListWriteAfterCallScan helperEffects body countEff.hasExternalInteraction
      let bodyEff := stmtListEffectSummary helperEffects body
      bodyViol || (bodyCalls && (bodyEff.writesStorage || bodyEff.writesTransient))
    | .unsafeBlock _ body =>
      (stmtListWriteAfterCallScan helperEffects body false).2
    | .internalCall functionName args | .internalCallAssign _ functionName args =>
      let argsEff := exprListEffectSummary helperEffects args
      let calleeEff := helperEffects functionName
      argsEff.hasExternalInteraction && (calleeEff.writesStorage || calleeEff.writesTransient)
    | _ => false

  /-- Sequential scan over a statement list tracking `(seenExternalCall, writeAfterExternalCall)`. -/
  def stmtListWriteAfterCallScan
      (helperEffects : String → MacroEffectSummary) : List Stmt → Bool → Bool × Bool
    | [], seenCall => (seenCall, false)
    | stmt :: rest, seenCall =>
      let stmtEff := stmtEffectSummary helperEffects stmt
      let violHere :=
        (seenCall && (stmtEff.writesStorage || stmtEff.writesTransient)) ||
          stmtWritesStorageAfterExternalCall helperEffects stmt
      let seenCall' := seenCall || stmtEff.hasExternalInteraction
      let (seenCallFinal, violRest) := stmtListWriteAfterCallScan helperEffects rest seenCall'
      (seenCallFinal, violHere || violRest)
end

/-- Check whether `stmts` performs a storage write after an external call (or inside a
    compound statement following an external call). -/
def hasWriteAfterExternalCall
    (helperEffects : String → MacroEffectSummary) (stmts : List Stmt) : Bool :=
  (stmtListWriteAfterCallScan helperEffects stmts false).2

mutual
  /-- Check whether a single statement internally performs a storage read after an external call. -/
  def stmtReadsStorageAfterExternalCall
      (helperEffects : String → MacroEffectSummary) : Stmt → Bool
    | .ite cond thenBranch elseBranch =>
      let condEff := exprEffectSummary helperEffects cond
      let (_, thenViol) := stmtListReadAfterCallScan helperEffects thenBranch condEff.hasExternalInteraction
      let (_, elseViol) := stmtListReadAfterCallScan helperEffects elseBranch condEff.hasExternalInteraction
      thenViol || elseViol
    | .forEach _ count body | .forEachSetBit _ count body =>
      let countEff := exprEffectSummary helperEffects count
      let (bodyCalls, bodyViol) := stmtListReadAfterCallScan helperEffects body countEff.hasExternalInteraction
      let bodyEff := stmtListEffectSummary helperEffects body
      bodyViol || (bodyCalls && bodyEff.readsStorage)
    | .unsafeBlock _ body =>
      (stmtListReadAfterCallScan helperEffects body false).2
    | .internalCall functionName args | .internalCallAssign _ functionName args =>
      let argsEff := exprListEffectSummary helperEffects args
      let calleeEff := helperEffects functionName
      argsEff.hasExternalInteraction && calleeEff.readsStorage
    | _ => false

  /-- Sequential scan over a statement list tracking `(seenExternalCall, readAfterExternalCall)`. -/
  def stmtListReadAfterCallScan
      (helperEffects : String → MacroEffectSummary) : List Stmt → Bool → Bool × Bool
    | [], seenCall => (seenCall, false)
    | stmt :: rest, seenCall =>
      let stmtEff := stmtEffectSummary helperEffects stmt
      let violHere := (seenCall && stmtEff.readsStorage) ||
        stmtReadsStorageAfterExternalCall helperEffects stmt
      let seenCall' := seenCall || stmtEff.hasExternalInteraction
      let (seenCallFinal, violRest) := stmtListReadAfterCallScan helperEffects rest seenCall'
      (seenCallFinal, violHere || violRest)
end

/-- Check whether `stmts` performs a storage read after an external call
    (read-only reentrancy / post-interaction storage read detector). -/
def hasExternalCallBeforeStorageRead
    (helperEffects : String → MacroEffectSummary) (stmts : List Stmt) : Bool :=
  (stmtListReadAfterCallScan helperEffects stmts false).2

@[simp] theorem hasWriteAfterExternalCall_nil
    (helperEffects : String → MacroEffectSummary) :
    hasWriteAfterExternalCall helperEffects [] = false := rfl

/-- If `s1` performs an external interaction and `s2` writes to storage, then `[s1, s2]`
    is flagged by `hasWriteAfterExternalCall`. -/
theorem hasWriteAfterExternalCall_pair_of_call_then_write
    (helperEffects : String → MacroEffectSummary) (s1 s2 : Stmt)
    (hcall : (stmtEffectSummary helperEffects s1).hasExternalInteraction = true)
    (hwrite : (stmtEffectSummary helperEffects s2).writesStorage = true) :
    hasWriteAfterExternalCall helperEffects [s1, s2] = true := by
  unfold hasWriteAfterExternalCall
  simp [stmtListWriteAfterCallScan, hcall, hwrite]

@[simp] theorem hasExternalCallBeforeStorageRead_nil
    (helperEffects : String → MacroEffectSummary) :
    hasExternalCallBeforeStorageRead helperEffects [] = false := rfl

/-- If `s1` performs an external interaction and `s2` reads from storage, then `[s1, s2]`
    is flagged by `hasExternalCallBeforeStorageRead`. -/
theorem hasExternalCallBeforeStorageRead_pair_of_call_then_read
    (helperEffects : String → MacroEffectSummary) (s1 s2 : Stmt)
    (hcall : (stmtEffectSummary helperEffects s1).hasExternalInteraction = true)
    (hread : (stmtEffectSummary helperEffects s2).readsStorage = true) :
    hasExternalCallBeforeStorageRead helperEffects [s1, s2] = true := by
  unfold hasExternalCallBeforeStorageRead
  simp [stmtListReadAfterCallScan, hcall, hread]

/-!
## 12. Poka-Yoke Static Write-Set Completeness & Slot-Drift Guards

Compile-time guards verifying that declared write-sets cover all actual written storage
fields and that contract storage slot indices do not drift from specification slot layouts.
-/

/-- Check whether `declaredFields` covers every field in `actualWrittenFields`. -/
def checkDeclaredWritesCoverActual (declaredFields actualWrittenFields : List String) : Bool :=
  actualWrittenFields.all (fun f => declaredFields.contains f)

/-- Return the list of fields in `actualWrittenFields` not declared in `declaredFields`. -/
def undeclaredWrittenFields (declaredFields actualWrittenFields : List String) : List String :=
  actualWrittenFields.filter (fun f => !declaredFields.contains f)

/-- Check that `contractSlots` and `specSlots` have identical `(fieldName, slotIndex)` layouts. -/
def checkNoSlotDrift (contractSlots specSlots : List (String × Nat)) : Bool :=
  decide (contractSlots = specSlots)

/-- Return all `(fieldName, slotIndex)` entries in `contractSlots` missing from `specSlots`. -/
def findDriftedSlots (contractSlots specSlots : List (String × Nat)) : List (String × Nat) :=
  contractSlots.filter (fun p => !specSlots.contains p)

@[simp] theorem checkDeclaredWritesCoverActual_nil (declared : List String) :
    checkDeclaredWritesCoverActual declared [] = true := rfl

@[simp] theorem checkDeclaredWritesCoverActual_cons
    (declared : List String) (f : String) (rest : List String) :
    checkDeclaredWritesCoverActual declared (f :: rest) =
      (declared.contains f && checkDeclaredWritesCoverActual declared rest) := rfl

@[simp] theorem undeclaredWrittenFields_nil (declared : List String) :
    undeclaredWrittenFields declared [] = [] := rfl

theorem undeclaredWrittenFields_eq_nil_iff (declared actual : List String) :
    undeclaredWrittenFields declared actual = [] ↔
      checkDeclaredWritesCoverActual declared actual = true := by
  induction actual with
  | nil =>
    simp only [undeclaredWrittenFields, checkDeclaredWritesCoverActual, List.filter, List.all]
  | cons f rest ih =>
    simp only [undeclaredWrittenFields, checkDeclaredWritesCoverActual, List.filter, List.all]
    cases h : declared.contains f
    · simp only [Bool.not_false, Bool.false_and, reduceCtorEq, Bool.false_eq_true]
    · simp only [Bool.not_true, Bool.true_and]
      exact ih

@[simp] theorem checkNoSlotDrift_refl (slots : List (String × Nat)) :
    checkNoSlotDrift slots slots = true := by
  simp only [checkNoSlotDrift, decide_true]

theorem checkNoSlotDrift_eq_true_iff (c s : List (String × Nat)) :
    checkNoSlotDrift c s = true ↔ c = s := by
  simp only [checkNoSlotDrift, decide_eq_true_eq]

theorem checkNoSlotDrift_symm (c s : List (String × Nat)) :
    checkNoSlotDrift c s = checkNoSlotDrift s c := by
  simp only [checkNoSlotDrift]
  by_cases h : c = s
  · subst h
    rfl
  · have h' : ¬(s = c) := fun hsc => h hsc.symm
    simp only [h, h', decide_false]

@[simp] theorem findDriftedSlots_nil_left (s : List (String × Nat)) :
    findDriftedSlots [] s = [] := rfl

theorem findDriftedSlots_eq_nil_of_all_contains (c s : List (String × Nat))
    (h : ∀ p ∈ c, s.contains p = true) :
    findDriftedSlots c s = [] := by
  induction c with
  | nil => rfl
  | cons p rest ih =>
    have hp : s.contains p = true := h p (.head rest)
    have hrest : ∀ q ∈ rest, s.contains q = true := fun q hq => h q (.tail p hq)
    unfold findDriftedSlots
    simp only [List.filter, hp, Bool.not_true]
    exact ih hrest

theorem findDriftedSlots_self_of_mem (slots : List (String × Nat))
    (h : ∀ p ∈ slots, slots.contains p = true) :
    findDriftedSlots slots slots = [] :=
  findDriftedSlots_eq_nil_of_all_contains slots slots h

end Verity.Macro
