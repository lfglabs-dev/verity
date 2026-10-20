import Compiler.Proofs.IRGeneration.GenericInduction.EventBridge
import Compiler.Proofs.IRGeneration.GenericInduction.Loops

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Extra Tier 2 assumptions needed to turn the singleton mapping-write
constructors in `SupportedStmtList` into real compiled-step proofs. These are
kept separate from the surface predicate because the remaining obligation is a
layout-specific slot-safety fact, not a syntactic fragment question. -/
structure SupportedStmtListMappingWriteSlotSafety (fields : List Field) : Prop where
  setMappingUintSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  setMappingChainSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {keys : List Expr}
      {value : Expr}
      {slot : Nat},
      (∀ expr ∈ keys, FunctionBody.ExprCompileCore expr) →
      (∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope) →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
  setMappingSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  setMappingWordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
  setMappingPackedWordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat}
      {packed : PackedBits},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      "__compat_value" ∉ scope →
      "__compat_packed" ∉ scope →
      "__compat_slot_word" ∉ scope →
      "__compat_slot_cleared" ∉ scope →
      packedBitsValid packed = true →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
  setStructMemberSingle :
    ∀ {scope : List String}
      {fieldName memberName : String}
      {key value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      isMapping fields fieldName = true ∧
      isMapping2 fields fieldName = false ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
  setMapping2Single :
    ∀ {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
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
  setMapping2WordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {wordOffset slot : Nat},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
  setStructMember2Single :
    ∀ {scope : List String}
      {fieldName memberName : String}
      {key1 key2 value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)

private theorem stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingUint fieldName key value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {keys : List Expr}
    {value : Expr}
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingChain fieldName keys value] := by
  rcases compileExprList_core_ok (fields := fields) hcoreKeys with ⟨keyIRs, hkeyIRs⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKeys := hcoreKeys)
      (hinScopeKeys := hinScopeKeys)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIRs := hkeyIRs)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMappingSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping fieldName key value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingWord fieldName key wordOffset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {packed : PackedBits}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingPackedWord fieldName key wordOffset packed value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hcompatValue := hcompatValue)
      (hcompatPacked := hcompatPacked)
      (hcompatSlotWord := hcompatSlotWord)
      (hcompatSlotCleared := hcompatSlotCleared)
      (hpacked := hpacked)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {slot wordOffset : Nat}
    {key value : Expr}
    {members : List StructMember}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hnotMapping2 : isMapping2 fields fieldName = false)
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
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember fieldName key memberName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStructMember_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hnotMapping2 := hnotMapping2)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hmembers := hmembers)
      (hmember := hmember)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key1 key2 value : Expr}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
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
              keyNat2) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping2 fieldName key1 key2 value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping2_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {key1 key2 value : Expr}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
    {fields : List Field} {scope : List String} {fieldName memberName : String}
    {slot wordOffset : Nat} {key1 key2 value : Expr} {members : List StructMember}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember2 fieldName key1 key2 memberName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hmembers := hmembers)
      (hmember := hmember)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem false_of_supportedStmtList_singleton_stmt_surface
    {stmt : Stmt}
    (hunsupported : stmtTouchesUnsupportedContractSurface stmt = true)
    (hsurface : stmtListTouchesUnsupportedContractSurface [stmt] = false) :
    False := by
  have hhead : stmtTouchesUnsupportedContractSurface stmt = false := by
    simpa [stmtListTouchesUnsupportedContractSurface] using hsurface
  rw [hunsupported] at hhead
  contradiction

private theorem stmtListGenericCore_of_supportedStmtList_letStorageField_of_surface
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.letVar tmp (Expr.storage fieldName)] :=
  stmtListGenericCore_singleton_letStorageField hnoConflict hfind hfieldInScope

private theorem stmtListGenericCore_of_supportedStmtList_letStorageAddrField_of_surface
    {fields : List Field}
    {scope : List String}
    {tmp fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.letVar tmp (Expr.storageAddr fieldName)] :=
  stmtListGenericCore_singleton_letStorageAddrField hnoConflict hfind hfieldInScope

private theorem stmtListGenericCore_of_supportedStmtList_assignStorageField_of_surface
    {fields : List Field}
    {scope : List String}
    {name fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.assignVar name (Expr.storage fieldName)] :=
  stmtListGenericCore_singleton_assignStorageField hnoConflict hfind hfieldInScope

private theorem stmtListGenericCore_of_supportedStmtList_assignStorageAddrField_of_surface
    {fields : List Field}
    {scope : List String}
    {name fieldName : String}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hfieldInScope : fieldName ∈ scope) :
    StmtListGenericCore fields scope [Stmt.assignVar name (Expr.storageAddr fieldName)] :=
  stmtListGenericCore_singleton_assignStorageAddrField hnoConflict hfind hfieldInScope

private theorem stmtListGenericCore_of_supportedStmtList_iteTerminal_of_surface
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    StmtListGenericCore fields scope [Stmt.ite cond thenBranch elseBranch] :=
  stmtListGenericCore_singleton_iteTerminal hcond hinScope hthen helse

private theorem exprBoundNamesInScope_of_scopeNamesIncluded
    {expr : Expr}
    {scope largerScope : List String}
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.exprBoundNamesInScope expr largerScope := by
  intro name hname
  exact hincluded name (hinScope name hname)

private theorem scopeNamesIncluded_cons
    {name : String} {scope largerScope : List String}
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.scopeNamesIncluded (name :: scope) (name :: largerScope) := by
  intro n hn
  simp at hn ⊢
  rcases hn with rfl | hn
  · exact Or.inl rfl
  · exact Or.inr (hincluded n hn)

private theorem stmtListCompileCore_of_scopeNamesIncluded
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.StmtListCompileCore largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil => exact .nil
  | letVar hvalue hinScope hrest ih =>
      exact .letVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | assignVar hvalue hinScope hrest ih =>
      exact .assignVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | require_ hcond hinScope hrest ih =>
      exact .require_ hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | return_ hvalue hinScope hrest ih =>
      exact .return_ hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | stop hrest ih =>
      exact .stop (ih hincluded)
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      exact .mstore hcoreOffset
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
        hcoreValue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
        (ih hincluded)
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      exact .tstore hcoreOffset
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
        hcoreValue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
        (ih hincluded)

private theorem stmtListTerminalCore_of_scopeNamesIncluded
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.StmtListTerminalCore largerScope stmts := by
  induction hterminal generalizing largerScope with
  | letVar hvalue hinScope hrest ih =>
      exact .letVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | assignVar hvalue hinScope hrest ih =>
      exact .assignVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | require_ hcond hinScope hrest ih =>
      exact .require_ hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | return_ hvalue hinScope hrest =>
      exact .return_ hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)
  | stop hrest =>
      exact .stop (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      exact .mstore hcoreOffset
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
        hcoreValue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
        (ih hincluded)
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      exact .tstore hcoreOffset
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
        hcoreValue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
        (ih hincluded)
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      exact .ite hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ihThen hincluded)
        (ihElse hincluded)
        (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)

private theorem scopeNamesIncluded_scope_stmtNextScope
    {scope largerScope : List String}
    {stmt : Stmt}
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.scopeNamesIncluded scope (stmtNextScope largerScope stmt) :=
  FunctionBody.scopeNamesIncluded_append_right hincluded

/-- Prepend a compile-core `letVar` head, checked in a larger scope, to a generic-core tail. -/
private theorem stmtListGenericCore_letVar_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {name : String} {value : Expr}
    {rest : List Stmt}
    (hvalue : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields (name :: largerScope) rest) :
    StmtListGenericCore fields largerScope (.letVar name value :: rest) := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_letVar (hcore := hvalue)
      (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
      (hvalueIR := hvalueIR))
    (by simpa [stmtNextScope, collectStmtBindNames] using htail)

/-- Prepend a compile-core `assignVar` head, checked in a larger scope, to a generic-core
tail. -/
private theorem stmtListGenericCore_assignVar_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {name : String} {value : Expr}
    {rest : List Stmt}
    (hvalue : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields largerScope rest) :
    StmtListGenericCore fields largerScope (.assignVar name value :: rest) := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_assignVar (hcore := hvalue)
      (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
      (hvalueIR := hvalueIR))
    (by simpa [stmtNextScope, collectStmtBindNames] using htail)

/-- Prepend a compile-core `require` head, checked in a larger scope, to a generic-core
tail. -/
private theorem stmtListGenericCore_require_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {cond : Expr} {message : String}
    {rest : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields
      (stmtNextScope largerScope (.require cond message)) rest) :
    StmtListGenericCore fields largerScope (.require cond message :: rest) := by
  rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
    ⟨failCond, hfailCond⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_require (hcore := hcond)
      (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
      (hfailCompile := hfailCond))
    htail

/-- Prepend a compile-core `return` head, checked in a larger scope, to a generic-core
tail. -/
private theorem stmtListGenericCore_return_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {value : Expr} {rest : List Stmt}
    (hvalue : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields (stmtNextScope largerScope (.return value)) rest) :
    StmtListGenericCore fields largerScope (.return value :: rest) := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_return (hcore := hvalue)
      (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
      (hvalueIR := hvalueIR))
    htail

/-- Prepend a compile-core `mstore` head, checked in a larger scope, to a generic-core
tail. -/
private theorem stmtListGenericCore_mstore_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {offset value : Expr}
    {rest : List Stmt}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields (stmtNextScope largerScope (.mstore offset value)) rest) :
    StmtListGenericCore fields largerScope (.mstore offset value :: rest) := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_mstore_single (hcoreOffset := hcoreOffset)
      (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
      (hcoreValue := hcoreValue)
      (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
      (hoffsetIR := hoffsetIR) (hvalueIR := hvalueIR))
    htail

/-- Prepend a compile-core `tstore` head, checked in a larger scope, to a generic-core
tail. -/
private theorem stmtListGenericCore_tstore_cons_of_scopeNamesIncluded
    {fields : List Field} {scope largerScope : List String} {offset value : Expr}
    {rest : List Stmt}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope)
    (htail : StmtListGenericCore fields (stmtNextScope largerScope (.tstore offset value)) rest) :
    StmtListGenericCore fields largerScope (.tstore offset value :: rest) := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_tstore_single (hcoreOffset := hcoreOffset)
      (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
      (hcoreValue := hcoreValue)
      (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
      (hoffsetIR := hoffsetIR) (hvalueIR := hvalueIR))
    htail

private theorem stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil => exact StmtListGenericCore.nil
  | letVar hvalue hinScope _ ih =>
      exact stmtListGenericCore_letVar_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (ih (scopeNamesIncluded_cons hincluded))
  | assignVar hvalue hinScope _ ih =>
      exact stmtListGenericCore_assignVar_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (ih hincluded)
  | require_ hcond hinScope _ ih =>
      exact stmtListGenericCore_require_cons_of_scopeNamesIncluded hcond hinScope hincluded
        (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | return_ hvalue hinScope _ ih =>
      exact stmtListGenericCore_return_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | stop _ ih =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      exact stmtListGenericCore_mstore_cons_of_scopeNamesIncluded hcoreOffset hinScopeOffset
        hcoreValue hinScopeValue hincluded (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      exact stmtListGenericCore_tstore_cons_of_scopeNamesIncluded hcoreOffset hinScopeOffset
        hcoreValue hinScopeValue hincluded (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))

private theorem stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hterminal generalizing largerScope with
  | letVar hvalue hinScope _ ih =>
      exact stmtListGenericCore_letVar_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (ih (scopeNamesIncluded_cons hincluded))
  | assignVar hvalue hinScope _ ih =>
      exact stmtListGenericCore_assignVar_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (ih hincluded)
  | require_ hcond hinScope _ ih =>
      exact stmtListGenericCore_require_cons_of_scopeNamesIncluded hcond hinScope hincluded
        (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | return_ hvalue hinScope hrest =>
      exact stmtListGenericCore_return_cons_of_scopeNamesIncluded hvalue hinScope hincluded
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded hrest
          (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | stop hrest =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded hrest
          (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      exact stmtListGenericCore_mstore_cons_of_scopeNamesIncluded hcoreOffset hinScopeOffset
        hcoreValue hinScopeValue hincluded (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      exact stmtListGenericCore_tstore_cons_of_scopeNamesIncluded hcoreOffset hinScopeOffset
        hcoreValue hinScopeValue hincluded (ih (scopeNamesIncluded_scope_stmtNextScope hincluded))
  | ite hcond hinScope hthen helse hrest _ _ =>
      rcases compiledStmtStep_ite (fields := fields) hcond
          (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded hthen hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded helse hincluded) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded hrest
          (scopeNamesIncluded_scope_stmtNextScope hincluded))

theorem stmtListGenericCore_of_stmtListCompileCore
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    StmtListGenericCore fields scope stmts :=
  stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    hcore
    FunctionBody.scopeNamesIncluded_refl

theorem stmtListGenericCore_of_stmtListTerminalCore
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    StmtListGenericCore fields scope stmts :=
  stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    hterminal
    FunctionBody.scopeNamesIncluded_refl

theorem compileStmtList_ok_of_stmtListGenericCore
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtBindNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead htail⟩

theorem compileStmtList_ok_of_stmtListGenericWithHelpers
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope_with_surface
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtBindNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface hhead htail⟩

theorem compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope_with_surface
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtBindNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface hhead htail⟩

theorem stmtStepMatchesIRExec_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
  rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
  exact ⟨hruntime,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
    hbounded,
    FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩
  · exact hmatch
  · exact hmatch

theorem stmtStepMatchesIRExecWithInternals_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch : stmtStepMatchesIRExecWithInternals fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExecWithInternals] at hmatch ⊢
  rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
  exact ⟨hruntime,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
    hbounded,
    FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩
  · exact hmatch
  · exact hmatch

theorem stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields scope sourceResult irExec) :
    FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch <;>
    simp [FunctionBody.stmtResultMatchesIRExec, hmatch]

theorem stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch :
      stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec) :
    stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExecWithInternals, stmtResultMatchesIRExecWithInternals,
      FunctionBody.stmtResultMatchesIRExec] at hmatch ⊢ <;>
    try exact hmatch
  · exact hmatch.1

theorem yulStmtList_length_add_sizeOf_le_append
    (head tail : List YulStmt) :
    head.length + sizeOf tail ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil => simp
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega

private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil =>
      cases tail <;> simp <;> omega
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega

private theorem execIRStmts_append_of_continue
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead : execIRStmts fuel state head = .continue next) :
    execIRStmts fuel state (head ++ tail) =
      execIRStmts (fuel - head.length) next tail := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmts] at hhead
      cases hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmts] at hhead
      | succ fuel =>
          match hstmt : execIRStmt fuel state stmt with
          | .continue next' =>
              simp [execIRStmts, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmts, hstmt] using hhead

private theorem execIRStmts_append_of_not_continue
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResult)
    (hhead : execIRStmts fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmts fuel state (head ++ tail) = irExec := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmts] at hhead
      cases hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmts] using hhead
      | succ fuel =>
          match hstmt : execIRStmt fuel state stmt with
          | .continue next' =>
              simp [execIRStmts, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmts, hstmt] using hhead

private theorem execIRStmtsWithInternals_append_of_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) =
      execIRStmtsWithInternals runtimeContract (fuel - head.length) next tail := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmtsWithInternals] at hhead
      cases hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals] at hhead
      | succ fuel =>
          match hstmt : execIRStmtWithInternals runtimeContract fuel state stmt with
          | .continue next' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .leave state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead

private theorem execIRStmtsWithInternals_append_of_not_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResultWithInternals)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) = irExec := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmtsWithInternals] at hhead
      cases hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmtsWithInternals] using hhead
      | succ fuel =>
          match hstmt : execIRStmtWithInternals runtimeContract fuel state stmt with
          | .continue next' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .leave state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead

/-- Fuel left for a compiled head after reserving its length from the whole body. -/
private theorem headSlack_le_append (compiledIR tailIR : List YulStmt) (extraFuel : Nat) :
    sizeOf compiledIR - compiledIR.length ≤
      sizeOf (compiledIR ++ tailIR) - compiledIR.length + extraFuel := by
  have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
  omega

/-- Head slack plus a reserved IR fuel slack still fits in the head fuel. -/
private theorem headSlack_add_le_append
    (compiledIR tailIR : List YulStmt) {irFuelSlack extraFuel : Nat}
    (hreserve : irFuelSlack ≤ extraFuel) :
    sizeOf compiledIR - compiledIR.length + irFuelSlack ≤
      sizeOf (compiledIR ++ tailIR) - compiledIR.length + extraFuel := by
  have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
  omega

/-- The compiled head runs at exactly the fuel of the whole body. -/
private theorem headFuel_eq_append (compiledIR tailIR : List YulStmt) (extraFuel : Nat) :
    compiledIR.length + (sizeOf (compiledIR ++ tailIR) - compiledIR.length + extraFuel) + 1 =
      sizeOf (compiledIR ++ tailIR) + extraFuel + 1 := by
  have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
  omega

/-- After a continuing head, the tail receives its own size plus the remaining slack. -/
private theorem tailFuel_eq_append (compiledIR tailIR : List YulStmt) (extraFuel : Nat) :
    sizeOf (compiledIR ++ tailIR) + extraFuel + 1 - compiledIR.length =
      sizeOf tailIR +
        (sizeOf (compiledIR ++ tailIR) - compiledIR.length - sizeOf tailIR + extraFuel) + 1 := by
  have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
  omega

/-- Source unfolding of a statement list whose head continues. -/
private theorem execStmtList_cons_eq_of_continue
    {fields : List Field} {runtime next : SourceSemantics.RuntimeState}
    {stmt : Stmt} {rest : List Stmt}
    (hhead : SourceSemantics.execStmt fields runtime stmt = .continue next) :
    SourceSemantics.execStmtList fields runtime (stmt :: rest) =
      SourceSemantics.execStmtList fields next rest := by
  simp [SourceSemantics.execStmtList, hhead]

/-- Source unfolding of a statement list whose head halts. -/
private theorem execStmtList_cons_eq_of_halt
    {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {stmt : Stmt} {rest : List Stmt} {result : SourceSemantics.StmtResult}
    (hhead : SourceSemantics.execStmt fields runtime stmt = result)
    (hhalt : ∀ next, result ≠ .continue next) :
    SourceSemantics.execStmtList fields runtime (stmt :: rest) = result := by
  rw [SourceSemantics.execStmtList, hhead]
  cases result <;> first | rfl | exact absurd rfl (hhalt _)

/-- Helper-aware source unfolding of a statement list whose head continues. -/
private theorem execStmtListWithHelpers_cons_eq_of_continue
    {spec : CompilationModel} {fields : List Field} {helperFuel : Nat}
    {runtime next : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
    (hhead :
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = .continue next) :
    SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
      SourceSemantics.execStmtListWithHelpers spec fields helperFuel next rest := by
  simp [SourceSemantics.execStmtListWithHelpers, hhead]

/-- Helper-aware source unfolding of a statement list whose head halts. -/
private theorem execStmtListWithHelpers_cons_eq_of_halt
    {spec : CompilationModel} {fields : List Field} {helperFuel : Nat}
    {runtime : SourceSemantics.RuntimeState} {stmt : Stmt} {rest : List Stmt}
    {result : SourceSemantics.StmtResult}
    (hhead : SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = result)
    (hhalt : ∀ next, result ≠ .continue next) :
    SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
      result := by
  rw [SourceSemantics.execStmtListWithHelpers, hhead]
  cases result <;> first | rfl | exact absurd rfl (hhalt _)

/-- Transport a property of a successful compile result along a second compile equation. -/
private theorem of_exists_eq_ok_of_eq_ok {ε α : Type} {x : Except ε α} {a : α} {P : α → Prop}
    (hx : x = .ok a) (h : ∃ b, x = .ok b ∧ P b) : P a := by
  obtain ⟨b, hb, hP⟩ := h
  rw [hx] at hb
  cases hb
  exact hP

/-- Glue a compiled head step onto its tail for legacy `execIRStmts`: a continuing head
hands its post-state to the tail, any other head result is the result of the body. -/
private theorem stmtStepMatchesIRExec_append_of_head
    {fields : List Field} {headScope finalScope : List String}
    {compiledIR tailIR : List YulStmt} {state : IRState} {extraFuel : Nat}
    {source sourceHead : SourceSemantics.StmtResult} {irHead : IRExecResult}
    {tailSource : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (hheadExec : execIRStmts
      (compiledIR.length + (sizeOf (compiledIR ++ tailIR) - compiledIR.length + extraFuel) + 1)
      state compiledIR = irHead)
    (hheadMatch : stmtStepMatchesIRExec fields headScope sourceHead irHead)
    (hcont : ∀ next, sourceHead = .continue next → source = tailSource next)
    (hhalt : (∀ next, sourceHead ≠ .continue next) → source = sourceHead)
    (htail : ∀ next tailState,
      stmtStepMatchesIRExec fields headScope (.continue next) (.continue tailState) →
      stmtStepMatchesIRExec fields finalScope (tailSource next)
        (execIRStmts (sizeOf tailIR +
          (sizeOf (compiledIR ++ tailIR) - compiledIR.length - sizeOf tailIR + extraFuel) + 1)
          tailState tailIR)) :
    stmtStepMatchesIRExec fields finalScope source
      (execIRStmts (sizeOf (compiledIR ++ tailIR) + extraFuel + 1) state
        (compiledIR ++ tailIR)) := by
  rw [headFuel_eq_append] at hheadExec
  cases sourceHead <;> cases irHead <;>
    try (simp [stmtStepMatchesIRExec] at hheadMatch; done)
  · rw [hcont _ rfl, execIRStmts_append_of_continue _ _ _ _ _ hheadExec, tailFuel_eq_append]
    exact htail _ _ hheadMatch
  all_goals
    rw [hhalt (by simp), execIRStmts_append_of_not_continue _ _ _ _ _ hheadExec (by simp)]
    simpa [stmtStepMatchesIRExec] using hheadMatch

/-- Helper-aware counterpart of `stmtStepMatchesIRExec_append_of_head` for
`execIRStmtsWithInternals`. -/
private theorem stmtStepMatchesIRExecWithInternals_append_of_head
    {runtimeContract : IRContract} {fields : List Field} {headScope finalScope : List String}
    {compiledIR tailIR : List YulStmt} {state : IRState} {extraFuel : Nat}
    {source sourceHead : SourceSemantics.StmtResult} {irHead : IRExecResultWithInternals}
    {tailSource : SourceSemantics.RuntimeState → SourceSemantics.StmtResult}
    (hheadExec : execIRStmtsWithInternals runtimeContract
      (compiledIR.length + (sizeOf (compiledIR ++ tailIR) - compiledIR.length + extraFuel) + 1)
      state compiledIR = irHead)
    (hheadMatch : stmtStepMatchesIRExecWithInternals fields headScope sourceHead irHead)
    (hcont : ∀ next, sourceHead = .continue next → source = tailSource next)
    (hhalt : (∀ next, sourceHead ≠ .continue next) → source = sourceHead)
    (htail : ∀ next tailState,
      stmtStepMatchesIRExecWithInternals fields headScope (.continue next) (.continue tailState) →
      stmtStepMatchesIRExecWithInternals fields finalScope (tailSource next)
        (execIRStmtsWithInternals runtimeContract (sizeOf tailIR +
          (sizeOf (compiledIR ++ tailIR) - compiledIR.length - sizeOf tailIR + extraFuel) + 1)
          tailState tailIR)) :
    stmtStepMatchesIRExecWithInternals fields finalScope source
      (execIRStmtsWithInternals runtimeContract
        (sizeOf (compiledIR ++ tailIR) + extraFuel + 1) state (compiledIR ++ tailIR)) := by
  rw [headFuel_eq_append] at hheadExec
  cases sourceHead <;> cases irHead <;>
    try (simp [stmtStepMatchesIRExecWithInternals] at hheadMatch; done)
  · rw [hcont _ rfl, execIRStmtsWithInternals_append_of_continue _ _ _ _ _ _ hheadExec,
      tailFuel_eq_append]
    exact htail _ _ hheadMatch
  all_goals
    rw [hhalt (by simp),
      execIRStmtsWithInternals_append_of_not_continue _ _ _ _ _ _ hheadExec (by simp)]
    simpa [stmtStepMatchesIRExecWithInternals] using hheadMatch

theorem exec_compileStmtList_generic_sizeOf_extraFuel_step
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec fields (List.foldl stmtNextScope scope stmts) sourceResult irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · exact FunctionBody.compileStmtList_nil_eq_ok _ _ _ _ _ _ _ _
      · exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericCore hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      rcases hstep.preserves runtime state _ hexact hscope hbounded hruntime
          (headSlack_le_append compiledIR tailIR extraFuel) with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨compiledIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hstep.compileOk htailCompile,
        stmtStepMatchesIRExec_append_of_head hheadExec hheadMatch
          (fun _ h => execStmtList_cons_eq_of_continue (hsourceHead.trans h))
          (execStmtList_cons_eq_of_halt hsourceHead) ?_⟩
      rintro next tailState ⟨hruntime', hexact', hbounded', hscope'⟩
      exact (of_exists_eq_ok_of_eq_ok htailCompile <|
        ih (extraFuel := sizeOf (compiledIR ++ tailIR) - compiledIR.length -
          sizeOf tailIR + extraFuel) hscope' hexact' hbounded' hruntime' :)

private theorem foldl_stmtNextScope_eq_of_collectStmtListBindNames_nil
    {stmts : List Stmt} (scope : List String)
    (hbind : collectStmtListBindNames stmts = []) :
    List.foldl stmtNextScope scope stmts = scope := by
  induction stmts generalizing scope with
  | nil => rfl
  | cons stmt rest ih =>
      simp only [collectStmtListBindNames, List.append_eq_nil_iff] at hbind
      simp only [List.foldl_cons, stmtNextScope, hbind.1, List.nil_append]
      exact ih scope hbind.2

private theorem compileStmt_core_inScopeNames_irrelevant
    {fields : List Field} {s1 s2 : List String} {stmt : Stmt}
    (hcore : FunctionBody.StmtCompileCore stmt) :
    CompilationModel.compileStmt fields [] [] .calldata [] false s1 [] stmt =
      CompilationModel.compileStmt fields [] [] .calldata [] false s2 [] stmt := by
  cases hcore <;> rfl

private theorem stmtListCompileCore_cons_inv
    {scope : List String} {stmt : Stmt} {rest : List Stmt}
    (h : FunctionBody.StmtListCompileCore scope (stmt :: rest)) :
    FunctionBody.StmtCompileCore stmt ∧
      ∃ nextScope, FunctionBody.StmtListCompileCore nextScope rest := by
  cases h <;> exact ⟨by constructor <;> assumption, _, by assumption⟩

private theorem compileStmtList_core_ok_any_scope
    {fields : List Field} {scope s1 s2 : List String} {stmts : List Stmt} {bodyIR : List YulStmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hok : CompilationModel.compileStmtList fields [] [] .calldata [] false s1 [] stmts =
      Except.ok bodyIR) :
    CompilationModel.compileStmtList fields [] [] .calldata [] false s2 [] stmts =
      Except.ok bodyIR := by
  induction stmts generalizing scope s1 s2 bodyIR with
  | nil =>
      rw [FunctionBody.compileStmtList_nil_eq_ok] at hok ⊢
      exact hok
  | cons stmt rest ih =>
      rcases stmtListCompileCore_cons_inv hcore with ⟨hheadCore, _, hrestCore⟩
      rcases FunctionBody.compileStmtList_cons_ok_inv hok with ⟨headIR, tailIR, hhead, htail, rfl⟩
      rw [compileStmt_core_inScopeNames_irrelevant (s2 := s2) hheadCore] at hhead
      exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead (ih hrestCore htail)

private theorem exists_continue_of_execIRStmts_append_continue
    {fuel : Nat} {state next : IRState} {head tail : List YulStmt}
    (h : execIRStmts fuel state (head ++ tail) = .continue next) :
    ∃ mid, execIRStmts fuel state head = .continue mid ∧
      execIRStmts (fuel - head.length) mid tail = .continue next := by
  rcases hhead : execIRStmts fuel state head with mid | ⟨v, s⟩ | s | s
  · rw [execIRStmts_append_of_continue _ _ _ _ _ hhead] at h
    exact ⟨mid, rfl, h⟩
  all_goals
    rw [execIRStmts_append_of_not_continue _ _ _ _ _ hhead (by simp)] at h
    cases h

private theorem exists_execIRStmt_of_execIRStmts_singleton_continue
    {fuel : Nat} {state mid : IRState} {stmt : YulStmt}
    (h : execIRStmts fuel state [stmt] = .continue mid) :
    ∃ f, execIRStmt f state stmt = .continue mid := by
  cases fuel with
  | zero => cases h
  | succ f =>
      cases hstmt : execIRStmt f state stmt <;> simp [execIRStmts, hstmt] at h
      exact ⟨f, h ▸ hstmt⟩

private theorem getVar_eq_of_execIRStmt_let_continue
    {fuel : Nat} {state next : IRState} {name z : String} {valIR : YulExpr}
    (hne : z ≠ name) (h : execIRStmt fuel state (.let_ name valIR) = .continue next) :
    next.getVar z = state.getVar z := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
      cases heval : evalIRExpr state valIR with
      | none => simp [execIRStmt, heval] at h
      | some v =>
          simp only [execIRStmt, heval, IRExecResult.continue.injEq] at h
          rw [← h, FunctionBody.getVar_setVar_ne _ name z v hne]

private theorem getVar_eq_of_execIRStmt_assign_continue
    {fuel : Nat} {state next : IRState} {name z : String} {valIR : YulExpr}
    (hne : z ≠ name) (h : execIRStmt fuel state (.assign name valIR) = .continue next) :
    next.getVar z = state.getVar z := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
      cases heval : evalIRExpr state valIR with
      | none => simp [execIRStmt, heval] at h
      | some v =>
          simp only [execIRStmt, heval, IRExecResult.continue.injEq] at h
          rw [← h, FunctionBody.getVar_setVar_ne _ name z v hne]

private theorem eq_of_execIRStmt_require_continue
    {fuel : Nat} {state next : IRState} {failCond : YulExpr} {msg : String}
    (h : execIRStmt fuel state (.if_ failCond (CompilationModel.revertWithMessage msg)) =
      .continue next) :
    next = state := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
      rcases FunctionBody.execIRStmts_revertWithMessage_revert (fuel := fuel) (state := state) msg
        with ⟨revState, hrev⟩
      cases heval : evalIRExpr state failCond with
      | none => simp [execIRStmt, heval] at h
      | some v =>
          by_cases hv : v = 0 <;> simp [execIRStmt, heval, hv, hrev] at h
          exact h.symm

private theorem eq_vars_of_execIRStmt_mstore_continue
    {fuel : Nat} {state next : IRState} {offIR valIR : YulExpr}
    (h : execIRStmt fuel state (.exprStmt (.call "mstore" [offIR, valIR])) = .continue next) :
    next.vars = state.vars := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
      cases ho : evalIRExpr state offIR <;> cases hv : evalIRExpr state valIR <;>
        simp [execIRStmt, evalIRExprs, ho, hv] at h
      rw [← h]; rfl

private theorem eq_vars_of_execIRStmt_tstore_continue
    {fuel : Nat} {state next : IRState} {offIR valIR : YulExpr}
    (h : execIRStmt fuel state (.exprStmt (.call "tstore" [offIR, valIR])) = .continue next) :
    next.vars = state.vars := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
      cases ho : evalIRExpr state offIR <;> cases hv : evalIRExpr state valIR <;>
        simp [execIRStmt, evalIRExprs, ho, hv] at h
      rw [← h]

private theorem false_of_execIRStmts_stop_continue
    {fuel : Nat} {state mid : IRState}
    (h : execIRStmts fuel state [YulStmt.exprStmt (YulExpr.call "stop" [])] = .continue mid) :
    False := by
  obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue h
  cases f <;> simp [execIRStmt] at hf

private theorem false_of_execIRStmts_return_continue
    {fuel : Nat} {state mid : IRState} {valIR : YulExpr}
    (h : execIRStmts fuel state
      [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valIR])
      , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
        .continue mid) :
    False := by
  obtain ⟨s1, _, hret⟩ := exists_continue_of_execIRStmts_append_continue
    (head := [YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valIR])])
    (tail := [YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])]) h
  obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue hret
  cases f <;> simp [execIRStmt, evalIRExprs, evalIRExpr] at hf

private theorem getVar_eq_of_compileStmt_core_continue
    {fields : List Field} {inScopeNames : List String} {stmt : Stmt} {headIR : List YulStmt}
    {z : String} {fuel : Nat} {state mid : IRState} (hcore : FunctionBody.StmtCompileCore stmt)
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames [] stmt =
      Except.ok headIR)
    (hz : z ∉ collectStmtNames stmt) (hexec : execIRStmts fuel state headIR = .continue mid) :
    mid.getVar z = state.getVar z := by
  cases hcore with
  | letVar hval =>
      obtain ⟨valIR, hvalIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hval
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileExprWithInternals_nil_eq, hvalIR, pure, Except.pure, bind, Except.bind] at hcompile
      obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue (hcompile ▸ hexec)
      exact getVar_eq_of_execIRStmt_let_continue (fun h => hz (by simp [collectStmtNames, h])) hf
  | assignVar hval =>
      obtain ⟨valIR, hvalIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hval
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileExprWithInternals_nil_eq, hvalIR, pure, Except.pure, bind, Except.bind] at hcompile
      obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue (hcompile ▸ hexec)
      exact getVar_eq_of_execIRStmt_assign_continue (fun h => hz (by simp [collectStmtNames, h])) hf
  | require_ hcond =>
      obtain ⟨fc, hfail⟩ := FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileRequireFailCondWithInternals_nil_eq, hfail, pure, Except.pure, bind, Except.bind] at hcompile
      obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue (hcompile ▸ hexec)
      rw [eq_of_execIRStmt_require_continue hf]
  | return_ hval =>
      obtain ⟨valIR, hvalIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hval
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileExprWithInternals_nil_eq, hvalIR, pure, Except.pure, bind, Except.bind] at hcompile
      exact False.elim (false_of_execIRStmts_return_continue (hcompile ▸ hexec))
  | stop =>
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, pure, Except.pure] at hcompile
      exact False.elim (false_of_execIRStmts_stop_continue (hcompile ▸ hexec))
  | mstore hoff hval =>
      obtain ⟨offIR, hoffIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hoff
      obtain ⟨valIR, hvalIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hval
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileExprWithInternals_nil_eq, hoffIR, hvalIR, pure, Except.pure, bind, Except.bind] at hcompile
      obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue (hcompile ▸ hexec)
      simp [IRState.getVar, eq_vars_of_execIRStmt_mstore_continue hf]
  | tstore hoff hval =>
      obtain ⟨offIR, hoffIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hoff
      obtain ⟨valIR, hvalIR⟩ := FunctionBody.compileExpr_core_ok (fields := fields) hval
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        CompilationModel.compileExprWithInternals_nil_eq, hoffIR, hvalIR, pure, Except.pure, bind, Except.bind] at hcompile
      obtain ⟨f, hf⟩ := exists_execIRStmt_of_execIRStmts_singleton_continue (hcompile ▸ hexec)
      simp [IRState.getVar, eq_vars_of_execIRStmt_tstore_continue hf]

private theorem getVar_eq_of_compileStmtList_core_continue
    {fields : List Field} {scope inScopeNames : List String} {stmts : List Stmt}
    {bodyIR : List YulStmt} {z : String} {fuel : Nat} {state next : IRState}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hcompile : CompilationModel.compileStmtList fields [] [] .calldata [] false
      inScopeNames [] stmts = Except.ok bodyIR)
    (hz : z ∉ collectStmtListNames stmts)
    (hexec : execIRStmts fuel state bodyIR = .continue next) :
    next.getVar z = state.getVar z := by
  induction stmts generalizing scope inScopeNames bodyIR fuel state with
  | nil =>
      rw [FunctionBody.compileStmtList_nil_eq_ok, Except.ok.injEq] at hcompile
      subst hcompile
      cases fuel <;> simp [execIRStmts] at hexec <;> rw [← hexec]
  | cons stmt rest ih =>
      rcases stmtListCompileCore_cons_inv hcore with ⟨hheadCore, _, hrestCore⟩
      simp only [collectStmtListNames, List.mem_append, not_or] at hz
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with ⟨headIR, tailIR, hhead, htail, rfl⟩
      rcases exists_continue_of_execIRStmts_append_continue hexec with ⟨mid, hmid, hrestExec⟩
      exact (ih hrestCore htail hz.2 hrestExec).trans
        (getVar_eq_of_compileStmt_core_continue hheadCore hhead hz.1 hmid)

private abbrev iteCoreTempName (scope : List String) (cond : Expr)
    (thenBranch elseBranch : List Stmt) : String :=
  CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
    (scope ++ collectExprNames cond ++
      collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)

private abbrev compiledIteCoreIR (tempName : String) (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) : List YulStmt :=
  [YulStmt.block
    [ YulStmt.let_ tempName condIR
    , YulStmt.if_ (YulExpr.ident tempName) thenIR
    , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]

private theorem stmtNextScope_ite_of_noBind
    (scope : List String) (cond : Expr) {thenBranch elseBranch : List Stmt}
    (hnoBindThen : collectStmtListBindNames thenBranch = [])
    (hnoBindElse : collectStmtListBindNames elseBranch = []) :
    stmtNextScope scope (.ite cond thenBranch elseBranch) = scope := by
  simp [stmtNextScope, collectStmtBindNames, hnoBindThen, hnoBindElse]

private theorem compileStmt_ite_empty_else_eq
    {fields : List Field} {scope : List String} {cond : Expr} {thenBranch : List Stmt}
    {condIR : YulExpr} {thenIR : List YulStmt}
    (hcondIR : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthenIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] thenBranch = Except.ok thenIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.ite cond thenBranch []) =
      Except.ok [YulStmt.if_ condIR thenIR] := by
  have hcondInternal := hcondIR
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcondInternal
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
    FunctionBody.compileStmtList_nil_eq_ok, hcondInternal, hthenIR,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem compileStmt_ite_nonempty_else_eq
    {fields : List Field} {scope : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt} {condIR : YulExpr} {thenIR elseIR : List YulStmt}
    (hcondIR : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthenIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] thenBranch = Except.ok thenIR)
    (helseIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] elseBranch = Except.ok elseIR)
    (helseNonempty : elseBranch.isEmpty = false) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (.ite cond thenBranch elseBranch) =
      Except.ok (compiledIteCoreIR (iteCoreTempName scope cond thenBranch elseBranch)
        condIR thenIR elseIR) := by
  have hcondInternal := hcondIR
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcondInternal
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
    hcondInternal, hthenIR, helseIR, helseNonempty, compiledIteCoreIR, iteCoreTempName,
    List.append_assoc, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem execIRStmts_if_single_false
    {state : IRState} {condIR : YulExpr} {thenIR : List YulStmt} {extraFuel : Nat}
    (hcond : evalIRExpr state condIR = some 0) :
    execIRStmts ([YulStmt.if_ condIR thenIR].length + extraFuel + 1) state
      [YulStmt.if_ condIR thenIR] = .continue state := by
  rw [show [YulStmt.if_ condIR thenIR].length + extraFuel + 1 = Nat.succ (Nat.succ extraFuel) by
    simp; omega]
  simp [execIRStmts, execIRStmt, hcond]

private theorem execIRStmts_if_single_true
    {state : IRState} {condIR : YulExpr} {thenIR : List YulStmt} {condVal extraFuel : Nat}
    (hcond : evalIRExpr state condIR = some condVal)
    (hcondNZ : condVal ≠ 0)
    (hslack : sizeOf [YulStmt.if_ condIR thenIR] - [YulStmt.if_ condIR thenIR].length ≤ extraFuel) :
    execIRStmts ([YulStmt.if_ condIR thenIR].length + extraFuel + 1) state
        [YulStmt.if_ condIR thenIR] =
      execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 1) + 1) state thenIR := by
  have hge : sizeOf thenIR + 1 ≤ extraFuel := by
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, YulStmt.if_.sizeOf_spec,
      List.length_singleton] at hslack
    omega
  rw [show [YulStmt.if_ condIR thenIR].length + extraFuel + 1 =
      Nat.succ (Nat.succ (sizeOf thenIR + (extraFuel - sizeOf thenIR - 1) + 1)) by
    simp only [List.length_singleton]; omega]
  dsimp only [execIRStmts, execIRStmt]
  rw [hcond]
  simp only [ne_eq, hcondNZ, not_false_eq_true, ↓reduceIte]
  cases execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 1) + 1) state thenIR <;> rfl

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

private theorem evalIRExpr_iszero_ident_eq
    (s : IRState) (name : String) (v : Nat)
    (hv : s.getVar name = some v)
    (hlt : v < Compiler.Constants.evmModulus) :
    evalIRExpr s (YulExpr.call "iszero" [YulExpr.ident name]) =
      some (if v = 0 then 1 else 0) := by
  have hmod : v % Compiler.Constants.evmModulus = v := Nat.mod_eq_of_lt hlt
  simp [evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    hv, hmod]

private theorem compiledStmtStep_ite_core_empty_else
    {fields : List Field} {scope : List String} {cond : Expr} {thenBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListCompileCore scope thenBranch)
    (hnoBindThen : collectStmtListBindNames thenBranch = []) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch []) compiledIR := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
  rcases compileStmtList_ok_of_stmtListGenericCore
    (stmtListGenericCore_of_stmtListCompileCore hthen) FunctionBody.scopeNamesIncluded_refl
    with ⟨thenIR, hthenIR⟩
  refine ⟨[YulStmt.if_ condIR thenIR], compileStmt_ite_empty_else_eq hcondIR hthenIR, ?_⟩
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨condVal, hCondSrc, hcondEval, -⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcond hinScope hexact hscope hbounded hruntime hcondIR
  simp only [stmtNextScope, collectStmtBindNames, collectStmtListBindNames, hnoBindThen,
    List.append_nil]
  by_cases hzero : condVal = 0
  · refine ⟨.continue runtime, .continue state, ?_,
      execIRStmts_if_single_false (hzero ▸ hcondEval), hruntime, hexact, hbounded, hscope⟩
    simp [SourceSemantics.execStmt, SourceSemantics.execStmtList, hCondSrc, hzero]
  · rcases exec_compileStmtList_generic_sizeOf_extraFuel_step (extraFuel - sizeOf thenIR - 1)
      (stmtListGenericCore_of_stmtListCompileCore hthen) hscope hexact hbounded hruntime
      with ⟨thenIR', hthenIR', hmatch⟩
    cases hthenIR.symm.trans hthenIR'
    rw [foldl_stmtNextScope_eq_of_collectStmtListBindNames_nil scope hnoBindThen] at hmatch
    refine ⟨_, _, ?_, execIRStmts_if_single_true hcondEval hzero hslack, hmatch⟩
    simp [SourceSemantics.execStmt, hCondSrc, hzero]

private theorem evalIRExpr_ident_setVar_eq (state : IRState) (name : String) (v : Nat) :
    evalIRExpr (state.setVar name v) (YulExpr.ident name) = some v := by
  simp [evalIRExpr, FunctionBody.getVar_setVar_eq]

private theorem execIRStmts_compiledIteCoreIR_else
    {state : IRState} {tempName : String} {condIR : YulExpr}
    {thenIR elseIR : List YulStmt} {extraFuel : Nat}
    (hcond : evalIRExpr state condIR = some 0)
    (hslack : sizeOf (compiledIteCoreIR tempName condIR thenIR elseIR) -
      (compiledIteCoreIR tempName condIR thenIR elseIR).length ≤ extraFuel) :
    execIRStmts ((compiledIteCoreIR tempName condIR thenIR elseIR).length + extraFuel + 1) state
        (compiledIteCoreIR tempName condIR thenIR elseIR) =
      execIRStmts (sizeOf elseIR + (extraFuel - sizeOf elseIR - 5) + 1)
        (state.setVar tempName 0) elseIR := by
  have hge : sizeOf elseIR + 5 ≤ extraFuel := by
    simp only [compiledIteCoreIR, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
      YulStmt.block.sizeOf_spec, YulStmt.let_.sizeOf_spec, YulStmt.if_.sizeOf_spec,
      YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec, List.length_singleton] at hslack
    omega
  have hisz : evalIRExpr (state.setVar tempName 0)
      (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 := by
    simpa using evalIRExpr_iszero_ident_eq (state.setVar tempName 0) tempName 0
      (FunctionBody.getVar_setVar_eq state tempName 0)
      (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS])
  rw [show (compiledIteCoreIR tempName condIR thenIR elseIR).length + extraFuel + 1 =
      (sizeOf elseIR + (extraFuel - sizeOf elseIR - 5) + 1) + 6 by
    simp only [compiledIteCoreIR, List.length_singleton]; omega]
  dsimp only [compiledIteCoreIR, execIRStmts, execIRStmt]
  rw [hcond]
  dsimp only [execIRStmts, execIRStmt]
  rw [evalIRExpr_ident_setVar_eq]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, execIRStmts, execIRStmt]
  rw [hisz]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
  cases execIRStmts (sizeOf elseIR + (extraFuel - sizeOf elseIR - 5) + 1)
    (state.setVar tempName 0) elseIR <;> rfl

private theorem execIRStmts_compiledIteCoreIR_then
    {state : IRState} {tempName : String} {condIR : YulExpr}
    {thenIR elseIR : List YulStmt} {condVal extraFuel : Nat}
    (hcond : evalIRExpr state condIR = some condVal)
    (hcondNZ : condVal ≠ 0)
    (hcondLt : condVal < Compiler.Constants.evmModulus)
    (hslack : sizeOf (compiledIteCoreIR tempName condIR thenIR elseIR) -
      (compiledIteCoreIR tempName condIR thenIR elseIR).length ≤ extraFuel)
    (hpres : ∀ s2,
      execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 4) + 1)
        (state.setVar tempName condVal) thenIR = .continue s2 →
      s2.getVar tempName = some condVal) :
    execIRStmts ((compiledIteCoreIR tempName condIR thenIR elseIR).length + extraFuel + 1) state
        (compiledIteCoreIR tempName condIR thenIR elseIR) =
      execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 4) + 1)
        (state.setVar tempName condVal) thenIR := by
  have hge : sizeOf thenIR + 4 ≤ extraFuel := by
    simp only [compiledIteCoreIR, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
      YulStmt.block.sizeOf_spec, YulStmt.let_.sizeOf_spec, YulStmt.if_.sizeOf_spec,
      YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec, List.length_singleton] at hslack
    omega
  rw [show (compiledIteCoreIR tempName condIR thenIR elseIR).length + extraFuel + 1 =
      (sizeOf thenIR + (extraFuel - sizeOf thenIR - 4) + 1) + 5 by
    simp only [compiledIteCoreIR, List.length_singleton]; omega]
  dsimp only [compiledIteCoreIR, execIRStmts, execIRStmt]
  rw [hcond]
  dsimp only [execIRStmts, execIRStmt]
  rw [evalIRExpr_ident_setVar_eq]
  simp only [ne_eq, hcondNZ, not_false_eq_true, ↓reduceIte]
  rcases hthen : execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 4) + 1)
      (state.setVar tempName condVal) thenIR with s2 | ⟨v, s2⟩ | s2 | s2
  · have hisz : evalIRExpr s2 (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 0 := by
      simpa [hcondNZ] using evalIRExpr_iszero_ident_eq s2 tempName condVal (hpres s2 hthen) hcondLt
    dsimp only [execIRStmts, execIRStmt]
    rw [hisz]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  · rfl
  · rfl
  · rfl

private theorem iteCoreTempName_fresh
    (scope : List String) (cond : Expr) (thenBranch elseBranch : List Stmt) :
    iteCoreTempName scope cond thenBranch elseBranch ∉ scope ∧
      iteCoreTempName scope cond thenBranch elseBranch ∉ collectStmtListNames thenBranch := by
  dsimp only [iteCoreTempName]
  have h := CompilationModel.pickFreshName_not_mem_usedNames
    (CompilationModel.iteCondBaseName thenBranch elseBranch)
    (scope ++ collectExprNames cond ++ collectStmtListNames thenBranch ++
      collectStmtListNames elseBranch)
  exact ⟨fun hm => h (by simp only [List.mem_append, hm, true_or, or_true]),
    fun hm => h (by simp only [List.mem_append, hm, true_or, or_true])⟩

private theorem stmtStepMatchesIRExec_iteCoreBranch
    {fields : List Field} {scope : List String} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} (cond : Expr) (thenBranch elseBranch : List Stmt) {branch : List Stmt}
    {branchIR : List YulStmt} {condVal : Nat} (fuel : Nat)
    (hbranch : FunctionBody.StmtListCompileCore scope branch)
    (hnoBind : collectStmtListBindNames branch = [])
    (hbranchIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope [] branch = Except.ok branchIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    stmtStepMatchesIRExec fields scope
      (SourceSemantics.execStmtList fields runtime branch)
      (execIRStmts (sizeOf branchIR + fuel + 1)
        (state.setVar (iteCoreTempName scope cond thenBranch elseBranch) condVal) branchIR) := by
  rcases exec_compileStmtList_generic_sizeOf_extraFuel_step fuel
      (stmtListGenericCore_of_stmtListCompileCore hbranch) hscope
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
        hexact (iteCoreTempName_fresh scope cond thenBranch elseBranch).1)
      hbounded
      (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
        (name := iteCoreTempName scope cond thenBranch elseBranch) (value := condVal) hruntime)
    with ⟨branchIR', hbranchIR', hmatch⟩
  cases hbranchIR.symm.trans hbranchIR'
  simpa [foldl_stmtNextScope_eq_of_collectStmtListBindNames_nil scope hnoBind] using hmatch

private theorem compiledStmtStep_ite_core_nonempty_else
    {fields : List Field} {scope : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListCompileCore scope thenBranch)
    (helse : FunctionBody.StmtListCompileCore scope elseBranch)
    (hnoBindThen : collectStmtListBindNames thenBranch = [])
    (hnoBindElse : collectStmtListBindNames elseBranch = [])
    (helseNonempty : elseBranch.isEmpty = false) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
  rcases compileStmtList_ok_of_stmtListGenericCore
    (stmtListGenericCore_of_stmtListCompileCore hthen) FunctionBody.scopeNamesIncluded_refl
    with ⟨thenIR, hthenIR⟩
  rcases compileStmtList_ok_of_stmtListGenericCore
    (stmtListGenericCore_of_stmtListCompileCore helse) FunctionBody.scopeNamesIncluded_refl
    with ⟨elseIR, helseIR⟩
  let tempName := iteCoreTempName scope cond thenBranch elseBranch
  refine ⟨compiledIteCoreIR tempName condIR thenIR elseIR,
    compileStmt_ite_nonempty_else_eq hcondIR hthenIR helseIR helseNonempty, ?_⟩
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  obtain ⟨condVal, hCondSrc, hcondEval, hcondLt⟩ :=
    exists_eval_of_compileExpr_core_of_scope hcond hinScope hexact hscope hbounded hruntime hcondIR
  rw [stmtNextScope_ite_of_noBind scope cond hnoBindThen hnoBindElse]
  by_cases hzero : condVal = 0
  · refine ⟨_, _, ?_, execIRStmts_compiledIteCoreIR_else (hzero ▸ hcondEval) hslack,
      stmtStepMatchesIRExec_iteCoreBranch cond thenBranch elseBranch _ helse hnoBindElse helseIR
        hexact hscope hbounded hruntime⟩
    simp [SourceSemantics.execStmt, hCondSrc, hzero]
  · have hpres : ∀ s2,
        execIRStmts (sizeOf thenIR + (extraFuel - sizeOf thenIR - 4) + 1)
          (state.setVar tempName condVal) thenIR = .continue s2 →
        s2.getVar tempName = some condVal := fun s2 hs2 => by
      rw [getVar_eq_of_compileStmtList_core_continue hthen hthenIR
        (iteCoreTempName_fresh scope cond thenBranch elseBranch).2 hs2,
        FunctionBody.getVar_setVar_eq]
    refine ⟨_, _, ?_, execIRStmts_compiledIteCoreIR_then hcondEval hzero hcondLt hslack hpres,
      stmtStepMatchesIRExec_iteCoreBranch cond thenBranch elseBranch _ hthen hnoBindThen hthenIR
        hexact hscope hbounded hruntime⟩
    simp [SourceSemantics.execStmt, hCondSrc, hzero]

theorem compiledStmtStep_ite_core
    {fields : List Field} {scope : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListCompileCore scope thenBranch)
    (helse : FunctionBody.StmtListCompileCore scope elseBranch)
    (hnoBindThen : collectStmtListBindNames thenBranch = [])
    (hnoBindElse : collectStmtListBindNames elseBranch = []) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by
  cases elseBranch with
  | nil =>
      exact compiledStmtStep_ite_core_empty_else hcond hinScope hthen hnoBindThen
  | cons _ _ =>
      exact compiledStmtStep_ite_core_nonempty_else hcond hinScope hthen helse
        hnoBindThen hnoBindElse rfl

private def forEachCoreUsedNames (scope : List String) (varName : String) (n : Nat)
    (body : List Stmt) : List String :=
  varName :: (scope ++ collectExprNames (Expr.literal n) ++ collectStmtListNames body)

private def forEachCoreIdxName (scope : List String) (varName : String) (n : Nat)
    (body : List Stmt) : String :=
  pickFreshName "__forEach_idx" (forEachCoreUsedNames scope varName n body)

private def forEachCoreCountName (scope : List String) (varName : String) (n : Nat)
    (body : List Stmt) : String :=
  pickFreshName "__forEach_count"
    (forEachCoreIdxName scope varName n body :: forEachCoreUsedNames scope varName n body)

private def forEachCoreLoopStmt (idxName countName varName : String) (bodyIR : List YulStmt) :
    YulStmt :=
  YulStmt.for_ []
    (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
    [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
    (YulStmt.assign varName (YulExpr.ident idxName) :: bodyIR)

private def forEachCoreCompiledIR (scope : List String) (varName : String) (n : Nat)
    (body : List Stmt) (bodyIR : List YulStmt) : List YulStmt :=
  let idxName := forEachCoreIdxName scope varName n body
  let countName := forEachCoreCountName scope varName n body
  [YulStmt.for_
    [ YulStmt.let_ idxName (YulExpr.lit 0)
    , YulStmt.let_ countName (YulExpr.lit (SourceSemantics.wordNormalize n))
    , YulStmt.let_ varName (YulExpr.lit 0) ]
    (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
    [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
    (YulStmt.assign varName (YulExpr.ident idxName) :: bodyIR)]

private theorem forEachCore_fresh_facts
    {scope : List String} {varName : String} {n : Nat} {body : List Stmt} :
    let idxName := forEachCoreIdxName scope varName n body
    let countName := forEachCoreCountName scope varName n body
    idxName ≠ varName ∧ countName ≠ varName ∧ countName ≠ idxName ∧
      idxName ∉ scope ∧ countName ∉ scope ∧
      idxName ∉ collectStmtListNames body ∧ countName ∉ collectStmtListNames body := by
  intro idxName countName
  have hidx : idxName ∉ forEachCoreUsedNames scope varName n body :=
    CompilationModel.pickFreshName_not_mem_usedNames "__forEach_idx"
      (forEachCoreUsedNames scope varName n body)
  have hcount : countName ∉ idxName :: forEachCoreUsedNames scope varName n body :=
    CompilationModel.pickFreshName_not_mem_usedNames "__forEach_count"
      (idxName :: forEachCoreUsedNames scope varName n body)
  refine ⟨fun h => hidx (by simp [forEachCoreUsedNames, h]),
    fun h => hcount (by simp [forEachCoreUsedNames, h]),
    fun h => hcount (by simp [h]),
    fun h => hidx (by simp [forEachCoreUsedNames, h]),
    fun h => hcount (by simp [forEachCoreUsedNames, h]),
    fun h => hidx (by simp [forEachCoreUsedNames, h]),
    fun h => hcount (by simp [forEachCoreUsedNames, h])⟩

private theorem forEachCore_slack_bounds
    {scope : List String} {varName : String} {n : Nat} {body : List Stmt} {bodyIR : List YulStmt}
    {extraFuel : Nat}
    (hslack : sizeOf (forEachCoreCompiledIR scope varName n body bodyIR) -
      (forEachCoreCompiledIR scope varName n body bodyIR).length ≤ extraFuel) :
    4 ≤ extraFuel ∧
      SourceSemantics.wordNormalize n + sizeOf bodyIR + 3 ≤ Nat.succ extraFuel := by
  have hmin : SourceSemantics.wordNormalize n + sizeOf bodyIR + 4 ≤
      sizeOf (forEachCoreCompiledIR scope varName n body bodyIR) -
        (forEachCoreCompiledIR scope varName n body bodyIR).length := by
    dsimp [forEachCoreCompiledIR]
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, YulStmt.for_.sizeOf_spec,
      YulStmt.let_.sizeOf_spec, YulStmt.assign.sizeOf_spec, YulExpr.call.sizeOf_spec,
      YulExpr.ident.sizeOf_spec, YulExpr.lit.sizeOf_spec, List.length_singleton]
    have hboundSize :
        SourceSemantics.wordNormalize n ≤ sizeOf (SourceSemantics.wordNormalize n) := by simp
    omega
  omega

private theorem execIRStmts_forEach_core_body_with_bind
    {idxName varName : String} {bodyIR : List YulStmt} {idx extraBodyFuel fuel : Nat}
    {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hfuel : fuel = Nat.succ (sizeOf bodyIR + extraBodyFuel + 1)) :
    execIRStmts fuel state (YulStmt.assign varName (YulExpr.ident idxName) :: bodyIR) =
      execIRStmts (sizeOf bodyIR + extraBodyFuel + 1) (state.setVar varName idx) bodyIR := by
  subst hfuel
  simp [execIRStmts, execIRStmt, evalIRExpr, hidx]

private theorem execIRStmts_forEach_core_post_inc
    {idxName : String} {idx fuel : Nat} {sBody : IRState}
    (hidx : sBody.getVar idxName = some idx)
    (hidxNextLt : idx + 1 < Compiler.Constants.evmModulus)
    (hfuel : 2 ≤ fuel) :
    execIRStmts fuel sBody
        [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])] =
      .continue (sBody.setVar idxName (idx + 1)) := by
  rcases Nat.exists_eq_add_of_le hfuel with ⟨k, rfl⟩
  have hmod : (idx + 1) % Compiler.Constants.evmModulus = idx + 1 := Nat.mod_eq_of_lt hidxNextLt
  rw [Nat.add_comm 2 k]
  simp [execIRStmts, execIRStmt, evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    hidx, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS, hmod]

private theorem evalIRExpr_forEach_core_cond_lt
    {idxName countName : String} {idx remaining : Nat} {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some (idx + Nat.succ remaining))
    (hboundLt : idx + Nat.succ remaining < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]) =
      some 1 := by
  have hidxLt : idx < Compiler.Constants.evmModulus := by omega
  simp [evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    hidx, hcount, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt hidxLt, Nat.mod_eq_of_lt hboundLt]

private theorem evalIRExpr_forEach_core_cond_eq
    {idxName countName : String} {idx : Nat} {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some idx) :
    evalIRExpr state (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]) =
      some 0 := by
  simp [evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext, hidx, hcount]

private theorem forEachCore_iter_body_match
    {fields : List Field} {scope : List String} {varName : String} {body : List Stmt}
    {bodyIR : List YulStmt} {idx extraBodyFuel : Nat}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (hgeneric : StmtListGenericCore fields (varName :: scope) body)
    (hbodyIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false (varName :: scope) [] body = Except.ok bodyIR)
    (hnoBind : collectStmtListBindNames body = [])
    (hidxLt : idx < Compiler.Constants.evmModulus)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
      runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent (varName :: scope) runtime.bindings) :
    let runtimeIter : SourceSemantics.RuntimeState :=
      { runtime with bindings :=
          SourceSemantics.bindValue runtime.bindings varName (SourceSemantics.wordNormalize idx) }
    stmtStepMatchesIRExec fields (varName :: scope)
      (SourceSemantics.execStmtList fields runtimeIter body)
      (execIRStmts (sizeOf bodyIR + extraBodyFuel + 1) (state.setVar varName idx) bodyIR) := by
  intro runtimeIter
  have hiter : runtimeIter =
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings varName idx } := by
    simp [runtimeIter, SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
      Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt hidxLt]
  rw [hiter]
  rcases exec_compileStmtList_generic_sizeOf_extraFuel_step extraBodyFuel hgeneric
      (FunctionBody.scopeNamesPresent_cons_bindValue
        (FunctionBody.scopeNamesPresent_of_included hscope (fun _ h => List.mem_cons_of_mem _ h)))
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
        (FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact
          (fun _ h => List.mem_cons_of_mem _ h)))
      (FunctionBody.bindingsBounded_bindValue hbounded varName idx hidxLt)
      (FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime varName idx)
    with ⟨bodyIR', hbodyIR', hmatch⟩
  cases hbodyIR.symm.trans hbodyIR'
  simpa [foldl_stmtNextScope_eq_of_collectStmtListBindNames_nil (varName :: scope) hnoBind]
    using hmatch

private def ForEachCoreLoopCtx
    (fields : List Field) (scope : List String) (idxName countName varName : String)
    (body : List Stmt) (bodyIR : List YulStmt) : Prop :=
  StmtListGenericCore fields (varName :: scope) body ∧
    FunctionBody.StmtListCompileCore (varName :: scope) body ∧
    CompilationModel.compileStmtList fields [] [] .calldata [] false (varName :: scope) [] body =
      Except.ok bodyIR ∧
    collectStmtListBindNames body = [] ∧
    idxName ≠ varName ∧ countName ≠ varName ∧ countName ≠ idxName ∧
    idxName ∉ varName :: scope ∧
    idxName ∉ collectStmtListNames body ∧ countName ∉ collectStmtListNames body

private def ForEachCoreLoopInv
    (fields : List Field) (scope : List String) (idxName countName varName : String)
    (idx rem : Nat) (runtime : SourceSemantics.RuntimeState) (state : IRState) : Prop :=
  state.getVar idxName = some idx ∧
    state.getVar countName = some (idx + rem) ∧
    FunctionBody.runtimeStateMatchesIR fields runtime state ∧
    FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope) runtime.bindings state ∧
    FunctionBody.bindingsBounded runtime.bindings ∧
    FunctionBody.scopeNamesPresent (varName :: scope) runtime.bindings

private theorem forEachCoreLoopInv_post_inc
    {fields : List Field} {scope : List String} {idxName countName varName : String}
    {body : List Stmt} {bodyIR : List YulStmt} {rem idx bodyFuel : Nat}
    {nextRuntime : SourceSemantics.RuntimeState} {state sBody : IRState}
    (hctx : ForEachCoreLoopCtx fields scope idxName countName varName body bodyIR)
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some (idx + Nat.succ rem))
    (hir : execIRStmts bodyFuel (state.setVar varName idx) bodyIR = .continue sBody)
    (hbodyMatch : stmtStepMatchesIRExec fields (varName :: scope)
      (.continue nextRuntime) (.continue sBody)) :
    sBody.getVar idxName = some idx ∧
      ForEachCoreLoopInv fields scope idxName countName varName (idx + 1) rem
        nextRuntime (sBody.setVar idxName (idx + 1)) := by
  rcases hctx with ⟨_, hbody, hbodyIR, _, hidx_ne_var, hcount_ne_var,
    hcount_ne_idx, hidx_not_next, hidx_not_body, hcount_not_body⟩
  rcases hbodyMatch with ⟨hruntimeB, hexactB, hboundedB, hscopeB⟩
  have hidxB : sBody.getVar idxName = some idx := by
    rw [getVar_eq_of_compileStmtList_core_continue hbody hbodyIR hidx_not_body hir,
      FunctionBody.getVar_setVar_ne _ varName idxName idx hidx_ne_var, hidx]
  have hcountB : sBody.getVar countName = some (idx + Nat.succ rem) := by
    rw [getVar_eq_of_compileStmtList_core_continue hbody hbodyIR hcount_not_body hir,
      FunctionBody.getVar_setVar_ne _ varName countName idx hcount_ne_var, hcount]
  exact ⟨hidxB, FunctionBody.getVar_setVar_eq _ _ _,
    by rw [FunctionBody.getVar_setVar_ne _ idxName countName (idx + 1) hcount_ne_idx, hcountB]; congr 1; omega,
    FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntimeB,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexactB hidx_not_next,
    hboundedB, hscopeB⟩

private theorem execIRStmt_forEach_core_loop_succ
    {fields : List Field} {scope : List String} {idxName countName varName : String}
    {body : List Stmt} {bodyIR : List YulStmt} {rem idx f : Nat}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (hctx : ForEachCoreLoopCtx fields scope idxName countName varName body bodyIR)
    (hinv : ForEachCoreLoopInv fields scope idxName countName varName idx (Nat.succ rem) runtime state)
    (hboundLt : idx + Nat.succ rem < Compiler.Constants.evmModulus)
    (hf : rem + sizeOf bodyIR + 3 ≤ f)
    (ih : ∀ nextRuntime sPost,
      ForEachCoreLoopInv fields scope idxName countName varName (idx + 1) rem nextRuntime sPost →
      stmtStepMatchesIRExec fields (varName :: scope)
        (SourceSemantics.execForEachLoop varName (SourceSemantics.execStmtList fields · body)
          nextRuntime (idx + 1) rem)
        (execIRStmt f sPost (forEachCoreLoopStmt idxName countName varName bodyIR))) :
    stmtStepMatchesIRExec fields (varName :: scope)
      (SourceSemantics.execForEachLoop varName (SourceSemantics.execStmtList fields · body)
        runtime idx (Nat.succ rem))
      (execIRStmt (Nat.succ f) state (forEachCoreLoopStmt idxName countName varName bodyIR)) := by
  rcases hctx with ⟨hgeneric, hbody, hbodyIR, hnoBind, hrestCtx⟩
  rcases hinv with ⟨hidx, hcount, hruntime, hexact, hbounded, hscope⟩
  have hbodyMatch := forEachCore_iter_body_match (idx := idx) (extraBodyFuel := f - sizeOf bodyIR - 2)
    hgeneric hbodyIR hnoBind (by omega) hruntime hexact hbounded hscope
  have hbodyBind := execIRStmts_forEach_core_body_with_bind (varName := varName) (bodyIR := bodyIR)
    (extraBodyFuel := f - sizeOf bodyIR - 2) (fuel := f) hidx (by omega)
  unfold SourceSemantics.execForEachLoop
  cases hsrc : SourceSemantics.execStmtList fields
      { runtime with bindings :=
          SourceSemantics.bindValue runtime.bindings varName (SourceSemantics.wordNormalize idx) }
      body <;>
    cases hir : execIRStmts (sizeOf bodyIR + (f - sizeOf bodyIR - 2) + 1)
      (state.setVar varName idx) bodyIR <;>
    simp only [hsrc, hir] at hbodyMatch ⊢ <;>
    try contradiction
  · rcases forEachCoreLoopInv_post_inc ⟨hgeneric, hbody, hbodyIR, hnoBind, hrestCtx⟩
      hidx hcount hir hbodyMatch with ⟨hidxB, hinvPost⟩
    rw [forEachCoreLoopStmt, execIRStmt_for_one_continue f state state _
      (‹IRState›.setVar idxName (idx + 1)) _ _ _ _ 1 (by simp [execIRStmts])
      (evalIRExpr_forEach_core_cond_lt hidx hcount hboundLt) (by decide)
      (hbodyBind.trans hir) (execIRStmts_forEach_core_post_inc (fuel := f) hidxB (by omega) (by omega))]
    exact ih _ _ hinvPost
  all_goals
    rw [forEachCoreLoopStmt, execIRStmt_for_body_noncontinue f state state _ _ _ _ 1 _
      (by simp [execIRStmts]) (evalIRExpr_forEach_core_cond_lt hidx hcount hboundLt)
      (by decide) (hbodyBind.trans hir) (by simp)]
    simpa [stmtStepMatchesIRExec] using hbodyMatch

private theorem execIRStmt_forEach_core_loop
    {fields : List Field} {scope : List String} {idxName countName varName : String}
    {body : List Stmt} {bodyIR : List YulStmt} (remaining idx fuel : Nat)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (hctx : ForEachCoreLoopCtx fields scope idxName countName varName body bodyIR)
    (hinv : ForEachCoreLoopInv fields scope idxName countName varName idx remaining runtime state)
    (hboundLt : idx + remaining < Compiler.Constants.evmModulus)
    (hfuel : remaining + sizeOf bodyIR + 3 ≤ fuel) :
    stmtStepMatchesIRExec fields (varName :: scope)
      (SourceSemantics.execForEachLoop varName (SourceSemantics.execStmtList fields · body)
        runtime idx remaining)
      (execIRStmt fuel state (forEachCoreLoopStmt idxName countName varName bodyIR)) := by
  induction remaining generalizing idx fuel runtime state with
  | zero =>
      rcases hinv with ⟨hidx, hcount, hruntime, hexact, hbounded, hscope⟩
      obtain ⟨f, rfl⟩ : ∃ f, fuel = Nat.succ f := ⟨fuel - 1, by omega⟩
      rw [forEachCoreLoopStmt, execIRStmt_for_init_cond_zero f state state [] _ _ _
        (by simp [execIRStmts]) (evalIRExpr_forEach_core_cond_eq hidx (by simpa using hcount))]
      exact ⟨hruntime, hexact, hbounded, hscope⟩
  | succ rem ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = Nat.succ f := ⟨fuel - 1, by omega⟩
      exact execIRStmt_forEach_core_loop_succ hctx hinv hboundLt (by omega)
        (fun nextRuntime sPost hinv' =>
          ih (idx + 1) f nextRuntime sPost hinv' (by omega) (by omega))

private theorem compileStmt_forEach_literal_core_eq
    {fields : List Field} {scope : List String} {varName : String} {n : Nat} {body : List Stmt}
    {bodyIR : List YulStmt}
    (hbody : FunctionBody.StmtListCompileCore (varName :: scope) body)
    (hbodyIR : CompilationModel.compileStmtList
      fields [] [] .calldata [] false (varName :: scope) [] body = Except.ok bodyIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.forEach varName (Expr.literal n) body) =
      Except.ok (forEachCoreCompiledIR scope varName n body bodyIR) := by
  have hbodyForEachScope := compileStmtList_core_ok_any_scope
    (s2 := CompilationModel.forEachBodyScope scope varName (Expr.literal n) body) hbody hbodyIR
  dsimp [forEachCoreCompiledIR, forEachCoreIdxName, forEachCoreCountName, forEachCoreUsedNames]
  simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
    CompilationModel.compileExprWithInternals, SourceSemantics.wordNormalize,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS, CompilationModel.uint256Modulus,
    hbodyForEachScope, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem execIRStmts_forEachCoreCompiledIR_eq
    {scope : List String} {varName : String} {n extraFuel : Nat} {body : List Stmt}
    {bodyIR : List YulStmt} {state : IRState}
    (hinitFuel : 4 ≤ extraFuel) :
    let idxName := forEachCoreIdxName scope varName n body
    let countName := forEachCoreCountName scope varName n body
    let bound := SourceSemantics.wordNormalize n
    let sInit := ((state.setVar idxName 0).setVar countName bound).setVar varName 0
    execIRStmts ((forEachCoreCompiledIR scope varName n body bodyIR).length + extraFuel + 1) state
        (forEachCoreCompiledIR scope varName n body bodyIR) =
      execIRStmt (Nat.succ extraFuel) sInit
        (forEachCoreLoopStmt idxName countName varName bodyIR) := by
  intro idxName countName bound sInit
  have hinit := execIRStmts_forEach_init_literal extraFuel state idxName countName varName
    bound hinitFuel
  rw [show (forEachCoreCompiledIR scope varName n body bodyIR).length + extraFuel + 1 =
    Nat.succ (Nat.succ extraFuel) by simp [forEachCoreCompiledIR]; omega]
  dsimp only [forEachCoreCompiledIR, forEachCoreLoopStmt, idxName, countName, bound, execIRStmts]
  rw [execIRStmt_for_init_continue extraFuel state sInit _ _ _ _ hinit]
  cases execIRStmt (Nat.succ extraFuel) sInit _ <;> rfl

theorem compiledStmtStep_forEach_literal_core
    {fields : List Field} {scope : List String} {varName : String} (n : Nat) {body : List Stmt}
    (hbody : FunctionBody.StmtListCompileCore (varName :: scope) body)
    (hnoBind : collectStmtListBindNames body = []) :
    ∃ compiledIR,
      CompiledStmtStep fields scope (Stmt.forEach varName (Expr.literal n) body) compiledIR := by
  have hgeneric := stmtListGenericCore_of_stmtListCompileCore (fields := fields) hbody
  rcases compileStmtList_ok_of_stmtListGenericCore hgeneric FunctionBody.scopeNamesIncluded_refl
    with ⟨bodyIR, hbodyIR⟩
  refine ⟨forEachCoreCompiledIR scope varName n body bodyIR,
    compileStmt_forEach_literal_core_eq hbody hbodyIR, ?_⟩
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  rcases forEachCore_fresh_facts (scope := scope) (varName := varName) (n := n) (body := body)
    with ⟨hidx_ne_var, hcount_ne_var, hcount_ne_idx, hidx_not_scope, hcount_not_scope,
      hidx_not_body, hcount_not_body⟩
  rcases forEachCore_slack_bounds hslack with ⟨hinitFuel, hloopFuel⟩
  let idxName := forEachCoreIdxName scope varName n body
  let countName := forEachCoreCountName scope varName n body
  let bound := SourceSemantics.wordNormalize n
  let sInit := ((state.setVar idxName 0).setVar countName bound).setVar varName 0
  refine ⟨_, _, rfl, execIRStmts_forEachCoreCompiledIR_eq hinitFuel, ?_⟩
  rw [show stmtNextScope scope (Stmt.forEach varName (Expr.literal n) body) = varName :: scope by
    simp [stmtNextScope, collectStmtBindNames, hnoBind]]
  exact execIRStmt_forEach_core_loop bound 0 (Nat.succ extraFuel)
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings varName 0 } sInit
    ⟨hgeneric, hbody, hbodyIR, hnoBind, hidx_ne_var, hcount_ne_var, hcount_ne_idx,
      by simp [idxName, hidx_ne_var, hidx_not_scope], hidx_not_body, hcount_not_body⟩
    ⟨by rw [FunctionBody.getVar_setVar_ne _ varName idxName 0 hidx_ne_var,
            FunctionBody.getVar_setVar_ne _ countName idxName bound hcount_ne_idx.symm,
            FunctionBody.getVar_setVar_eq],
     by rw [FunctionBody.getVar_setVar_ne _ varName countName 0 hcount_ne_var,
            FunctionBody.getVar_setVar_eq]; simp,
     FunctionBody.runtimeStateMatchesIR_setVar_bindValue
       (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
         (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime)) varName 0,
     FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
       (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
         (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact hidx_not_scope)
         hcount_not_scope),
     FunctionBody.bindingsBounded_bindValue hbounded varName 0
       (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]),
     FunctionBody.scopeNamesPresent_cons_bindValue hscope⟩
    (by simpa [bound] using FunctionBody.wordNormalize_lt_evmModulus n) hloopFuel

/-- A singleton compile-core `require` is a generic-core statement list. -/
private theorem stmtListGenericCore_singleton_require_of_compileCore
    {fields : List Field} {scope : List String} {cond : Expr} {message : String}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope) :
    StmtListGenericCore fields scope [Stmt.require cond message] :=
  stmtListGenericCore_of_stmtListCompileCore
    (FunctionBody.StmtListCompileCore.require_ hcond hinScope FunctionBody.StmtListCompileCore.nil)

private theorem stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
    {fields : List Field}
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope [clause.toStmt] := by
  obtain ⟨family, n, m, p, q, message⟩ := clause
  have hinScope {cond : Expr} (hnames : FunctionBody.exprBoundNames cond = []) :
      FunctionBody.exprBoundNamesInScope cond scope := by
    intro name hmem
    simp [hnames] at hmem
  cases family with
  | binary op =>
      cases op <;>
        exact stmtListGenericCore_singleton_require_of_compileCore (by repeat constructor)
          (hinScope (by simp [FunctionBody.exprBoundNames]))
  | _ =>
      exact stmtListGenericCore_singleton_require_of_compileCore (by repeat constructor)
        (hinScope (by simp [FunctionBody.exprBoundNames]))

theorem stmtListGenericCore_append
    {fields : List Field}
    {scope : List String}
    {«prefix» «suffix» : List Stmt}
    (hprefix : StmtListGenericCore fields scope «prefix»)
    (hsuffix :
      StmtListGenericCore
        fields
        (List.foldl stmtNextScope scope «prefix»)
        «suffix») :
    StmtListGenericCore fields scope («prefix» ++ «suffix») := by
  induction hprefix generalizing «suffix» with
  | nil =>
      simpa using hsuffix
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp
      exact StmtListGenericCore.cons hstep (ih hsuffix)

private theorem stmtNextScope_requireLiteralGuardFamilyClause
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    stmtNextScope scope clause.toStmt = scope := by
  cases clause with
  | mk family n m p q message =>
      cases family with
      | binary guard =>
          cases guard <;>
            simp [stmtNextScope,
              Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
              collectStmtBindNames]
      | andEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtBindNames]
      | orEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtBindNames]

private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {«prefix» «suffix» : List Stmt}
    (_hprefix : SupportedStmtList fields scope «prefix»)
    (_hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope «prefix») «suffix»)
    (ihPrefix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «prefix» = false →
        StmtListGenericCore fields scope «prefix»)
    (ihSuffix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «suffix» = false →
        StmtListGenericCore fields (List.foldl stmtNextScope scope «prefix») «suffix»)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites («prefix» ++ «suffix») = false) :
    StmtListGenericCore fields scope («prefix» ++ «suffix») := by
  rw [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_append] at hsurface
  exact stmtListGenericCore_append
    (ihPrefix (Bool.or_eq_false_iff.mp hsurface).1)
    (ihSuffix (Bool.or_eq_false_iff.mp hsurface).2)

private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {rest : List Stmt}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (ihRest :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false →
        StmtListGenericCore fields scope rest)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (clause.toStmt :: rest) = false) :
    StmtListGenericCore fields scope (clause.toStmt :: rest) := by
  simp only [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    Bool.or_eq_false_iff] at hsurface
  apply stmtListGenericCore_append
    (stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
      (fields := fields) (scope := scope) clause)
  simp only [List.foldl, stmtNextScope_requireLiteralGuardFamilyClause clause]
  exact ihRest hsurface.2

private theorem stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero
    {varName : String}
    {body : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface [Stmt.forEach varName (.literal 0) body] = false) :
    stmtListTouchesUnsupportedContractSurface body = false := by
  cases body with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest =>
      simp only [stmtListTouchesUnsupportedContractSurface,
        stmtTouchesUnsupportedContractSurface, Bool.or_false,
        Bool.or_eq_false_iff] at hsurface
      exact Bool.or_eq_false_iff.mpr hsurface

private theorem stmtListGenericCore_singleton_of_compiledStmtStep
    {fields : List Field} {scope : List String} {stmt : Stmt}
    (hstep : ∃ compiledIR, CompiledStmtStep fields scope stmt compiledIR) :
    StmtListGenericCore fields scope [stmt] := by
  obtain ⟨_, hstep⟩ := hstep
  exact StmtListGenericCore.cons hstep StmtListGenericCore.nil

private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface
    {fields : List Field} {scope : List String} {rest : List Stmt}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (ihRest : stmtListTouchesUnsupportedContractSurface rest = false →
      StmtListGenericCore fields scope rest)
    (hsurface : stmtListTouchesUnsupportedContractSurface (clause.toStmt :: rest) = false) :
    StmtListGenericCore fields scope (clause.toStmt :: rest) := by
  simp [stmtListTouchesUnsupportedContractSurface] at hsurface
  apply stmtListGenericCore_append
    (stmtListGenericCore_singleton_requireLiteralGuardFamilyClause clause)
  simp only [List.foldl, stmtNextScope_requireLiteralGuardFamilyClause clause]
  exact ihRest hsurface.2

private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface
    {fields : List Field} {scope : List String} {«prefix» «suffix» : List Stmt}
    (ihPrefix : stmtListTouchesUnsupportedContractSurface «prefix» = false →
      StmtListGenericCore fields scope «prefix»)
    (ihSuffix : stmtListTouchesUnsupportedContractSurface «suffix» = false →
      StmtListGenericCore fields (List.foldl stmtNextScope scope «prefix») «suffix»)
    (hsurface : stmtListTouchesUnsupportedContractSurface («prefix» ++ «suffix») = false) :
    StmtListGenericCore fields scope («prefix» ++ «suffix») := by
  simp only [stmtListTouchesUnsupportedContractSurface_append, Bool.or_eq_false_iff] at hsurface
  exact stmtListGenericCore_append (ihPrefix hsurface.1) (ihSuffix hsurface.2)

/-- Every supported statement list that clears the contract-surface gate is in the
generic core fragment. Non-recursive constructors are discharged by their dedicated
leaf lemmas or refuted by the surface gate on their singleton statement. -/
theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported with
  | forEachLiteralBounded hbodyNames _ ih =>
      exact stmtListGenericCore_singleton_of_compiledStmtStep
        (compiledStmtStep_forEach_literal_zero hbodyNames
          (ih (stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero hsurface)))
  | forEachLiteralCore n hbody hnoBind =>
      exact stmtListGenericCore_singleton_of_compiledStmtStep
        (compiledStmtStep_forEach_literal_core n hbody hnoBind)
  | ite hcond hinScope hthen helse hnoBindThen hnoBindElse =>
      exact stmtListGenericCore_singleton_of_compiledStmtStep
        (compiledStmtStep_ite_core hcond hinScope hthen helse hnoBindThen hnoBindElse)
  | requireClause clause _ ih =>
      exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface clause ih hsurface
  | append _ _ ihPrefix ihSuffix =>
      exact stmtListGenericCore_of_supportedStmtList_append_of_surface ihPrefix ihSuffix hsurface
  | _ =>
      first
        | exact stmtListGenericCore_of_stmtListCompileCore ‹_›
        | exact stmtListGenericCore_of_stmtListTerminalCore ‹_›
        | exact stmtListGenericCore_singleton_of_compiledStmtStep
            compiledStmtStep_forEach_literal_empty
        | (first
            | apply stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_letStorageField_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_letStorageAddrField_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_assignStorageField_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_assignStorageAddrField_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_calldatacopySingle_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_returndataCopyEmptySingle_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_revertEmptySingle_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_revertReturndataEmptySingle_of_surface
            | apply stmtListGenericCore_of_supportedStmtList_iteTerminal_of_surface
          ) <;> assumption
        | (exfalso
           refine false_of_supportedStmtList_singleton_stmt_surface ?_ hsurface
           simp [stmtTouchesUnsupportedContractSurface, exprTouchesUnsupportedContractSurface])

/-- Body-local slot-safety witness for the singleton mapping-write statements
that are admitted by the alternate Tier 2 fragment. Unlike
`SupportedStmtListMappingWriteSlotSafety`, this predicate only talks about the
statements that actually occur in one function body, making the alternate whole
contract theorem practical to instantiate for concrete proof fixtures. -/
def StmtMappingWriteSlotSafe (fields : List Field) : Stmt → Prop
  | .setMappingUint fieldName key _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat,
          SourceSemantics.evalExpr fields runtime key = some keyNat →
            findResolvedFieldAtSlotCopy fields
              (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  | .setMappingChain fieldName keys _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyVals,
          SourceSemantics.evalExprList fields runtime keys = some keyVals →
            findResolvedFieldAtSlotCopy fields
              (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (SourceSemantics.mappingSlotChain slot keyVals) = none)
  | .setMapping fieldName key _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat,
          SourceSemantics.evalExpr fields runtime key = some keyNat →
            findResolvedFieldAtSlotCopy fields
              (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  | .setMappingWord fieldName key wordOffset _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat,
          SourceSemantics.evalExpr fields runtime key = some keyNat →
            findResolvedFieldAtSlotCopy fields
              (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (mappingWordTargetSlot slot keyNat wordOffset) = none)
  | .setMappingPackedWord fieldName key wordOffset _ _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat,
          SourceSemantics.evalExpr fields runtime key = some keyNat →
            findResolvedFieldAtSlotCopy fields
              (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (mappingWordTargetSlot slot keyNat wordOffset) = none)
  | .setStructMember fieldName key memberName _ =>
      ∃ slot wordOffset members,
        findFieldSlot fields fieldName = some slot ∧
        findStructMembers fields fieldName = some members ∧
        findStructMember members memberName =
          some { name := memberName, wordOffset := wordOffset, packed := none } ∧
        isMapping fields fieldName = true ∧
        isMapping2 fields fieldName = false ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat,
          SourceSemantics.evalExpr fields runtime key = some keyNat →
            findResolvedFieldAtSlotCopy fields
              (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (mappingWordTargetSlot slot keyNat wordOffset) = none)
  | .setMapping2 fieldName key1 key2 _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping2 fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat1 keyNat2,
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
  | .setMapping2Word fieldName key1 key2 wordOffset _ =>
      ∃ slot,
        findFieldSlot fields fieldName = some slot ∧
        isMapping2 fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat1 keyNat2,
          SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
          SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
            findResolvedFieldAtSlotCopy fields
              (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
  | .setStructMember2 fieldName key1 key2 memberName _ =>
      ∃ slot wordOffset members,
        findFieldSlot fields fieldName = some slot ∧
        findStructMembers fields fieldName = some members ∧
        findStructMember members memberName =
          some { name := memberName, wordOffset := wordOffset, packed := none } ∧
        isMapping2 fields fieldName = true ∧
        findFieldWriteSlots fields fieldName = some [slot] ∧
        (∀ runtime keyNat1 keyNat2,
          SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
          SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
            findResolvedFieldAtSlotCopy fields
              (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
            findDynamicArrayElementAtSlotCopy fields runtime.world
              (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
  | _ => True

/-- On a singleton statement that is not a top-level mapping write, the
mapping-write-tolerant surface gate is the plain contract-surface gate. -/
private theorem stmtListTouchesUnsupportedContractSurface_singleton_of_exceptMappingWrites
    {stmt : Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites [stmt] = false)
    (hnotWrite : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt =
      stmtTouchesUnsupportedContractSurface stmt) :
    stmtListTouchesUnsupportedContractSurface [stmt] = false := by
  simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtListTouchesUnsupportedContractSurface, hnotWrite] using hsurface

/-- Compile-core statement lists contain no top-level mapping writes. -/
private theorem stmtMappingWriteSlotSafe_of_stmtListCompileCore
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt := by
  induction hcore with
  | nil => exact fun _ hmem => nomatch hmem
  | _ => exact List.forall_mem_cons.2 ⟨trivial, ‹_›⟩

/-- Terminal-core statement lists contain no top-level mapping writes. -/
private theorem stmtMappingWriteSlotSafe_of_stmtListTerminalCore
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt := by
  induction hterminal with
  | return_ _ _ hrest | stop hrest | ite _ _ _ _ hrest _ _ =>
      exact List.forall_mem_cons.2 ⟨trivial, stmtMappingWriteSlotSafe_of_stmtListCompileCore hrest⟩
  | _ => exact List.forall_mem_cons.2 ⟨trivial, ‹_›⟩

/-- Body-local slot safety turns a supported singleton `setMappingUint` write into its
generic-core witness. -/
private theorem stmtListGenericCore_setMappingUint_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {slot : Nat}
    (hk : FunctionBody.ExprCompileCore key) (hsk : FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMappingUint fieldName key value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setMappingUint fieldName key value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety hk hsk hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setMappingChain` write. -/
private theorem stmtListGenericCore_setMappingChain_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String} {keys : List Expr}
    {value : Expr} {slot : Nat}
    (hk : ∀ key ∈ keys, FunctionBody.ExprCompileCore key)
    (hsk : ∀ key ∈ keys, FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMappingChain fieldName keys value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setMappingChain fieldName keys value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety hk hsk hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setMapping` write. -/
private theorem stmtListGenericCore_setMapping_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {slot : Nat}
    (hk : FunctionBody.ExprCompileCore key) (hsk : FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMapping fieldName key value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setMapping fieldName key value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMappingSingle_of_slotSafety hk hsk hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setMappingWord` write. -/
private theorem stmtListGenericCore_setMappingWord_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {wordOffset slot : Nat}
    (hk : FunctionBody.ExprCompileCore key) (hsk : FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMappingWord fieldName key wordOffset value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setMappingWord fieldName key wordOffset value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety hk hsk hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setMappingPackedWord` write. -/
private theorem stmtListGenericCore_setMappingPackedWord_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String} {key value : Expr}
    {wordOffset slot : Nat} {packed : PackedBits}
    (hk : FunctionBody.ExprCompileCore key) (hsk : FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hc1 : "__compat_value" ∉ scope) (hc2 : "__compat_packed" ∉ scope)
    (hc3 : "__compat_slot_word" ∉ scope) (hc4 : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMappingPackedWord fieldName key wordOffset packed value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope
      [Stmt.setMappingPackedWord fieldName key wordOffset packed value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
    hk hsk hv hsv hc1 hc2 hc3 hc4 hpacked hm hws hss

/-- Body-local slot safety for a supported singleton `setStructMember` write. -/
private theorem stmtListGenericCore_setStructMember_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName memberName : String}
    {key value : Expr} {slot wordOffset : Nat} {members : List StructMember}
    (hk : FunctionBody.ExprCompileCore key) (hsk : FunctionBody.exprBoundNamesInScope key scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember : findStructMember members memberName =
      some { name := memberName, wordOffset := wordOffset, packed := none })
    (hsafety : ∀ stmt ∈ [Stmt.setStructMember fieldName key memberName value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setStructMember fieldName key memberName value] := by
  obtain ⟨slot', wordOffset', members', hfind, hmembers', hmember', hm, hnotm2, hws, hss⟩ :=
    hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  obtain rfl : members' = members := Option.some.inj (hmembers'.symm.trans hmembers)
  obtain rfl : wordOffset' = wordOffset := by
    cases Option.some.inj (hmember'.symm.trans hmember); rfl
  exact stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
    hk hsk hv hsv hm hnotm2 hmembers hmember hws hss

/-- Body-local slot safety for a supported singleton `setMapping2` write. -/
private theorem stmtListGenericCore_setMapping2_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String}
    {key1 key2 value : Expr} {slot : Nat}
    (hk1 : FunctionBody.ExprCompileCore key1)
    (hsk1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hk2 : FunctionBody.ExprCompileCore key2)
    (hsk2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMapping2 fieldName key1 key2 value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope [Stmt.setMapping2 fieldName key1 key2 value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
    hk1 hsk1 hk2 hsk2 hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setMapping2Word` write. -/
private theorem stmtListGenericCore_setMapping2Word_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName : String}
    {key1 key2 value : Expr} {wordOffset slot : Nat}
    (hk1 : FunctionBody.ExprCompileCore key1)
    (hsk1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hk2 : FunctionBody.ExprCompileCore key2)
    (hsk2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hsafety : ∀ stmt ∈ [Stmt.setMapping2Word fieldName key1 key2 wordOffset value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope
      [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] := by
  obtain ⟨slot', hfind, hm, hws, hss⟩ := hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  exact stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
    hk1 hsk1 hk2 hsk2 hv hsv hm hws hss

/-- Body-local slot safety for a supported singleton `setStructMember2` write. -/
private theorem stmtListGenericCore_setStructMember2_of_stmtSafety
    {fields : List Field} {scope : List String} {fieldName memberName : String}
    {key1 key2 value : Expr} {slot wordOffset : Nat} {members : List StructMember}
    (hk1 : FunctionBody.ExprCompileCore key1)
    (hsk1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hk2 : FunctionBody.ExprCompileCore key2)
    (hsk2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hv : FunctionBody.ExprCompileCore value)
    (hsv : FunctionBody.exprBoundNamesInScope value scope)
    (hslot : findFieldSlot fields fieldName = some slot)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember : findStructMember members memberName =
      some { name := memberName, wordOffset := wordOffset, packed := none })
    (hsafety : ∀ stmt ∈ [Stmt.setStructMember2 fieldName key1 key2 memberName value],
      StmtMappingWriteSlotSafe fields stmt) :
    StmtListGenericCore fields scope
      [Stmt.setStructMember2 fieldName key1 key2 memberName value] := by
  obtain ⟨slot', wordOffset', members', hfind, hmembers', hmember', hm, hws, hss⟩ :=
    hsafety _ (List.mem_singleton_self _)
  obtain rfl : slot' = slot := Option.some.inj (hfind.symm.trans hslot)
  obtain rfl : members' = members := Option.some.inj (hmembers'.symm.trans hmembers)
  obtain rfl : wordOffset' = wordOffset := by
    cases Option.some.inj (hmember'.symm.trans hmember); rfl
  exact stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
    hk1 hsk1 hk2 hsk2 hv hsv hm hmembers hmember hws hss

/-- Away from top-level mapping writes the mapping-write-tolerant surface gate agrees with
the plain contract-surface gate, so every remaining supported constructor is discharged by
`stmtListGenericCore_of_supportedStmtList_of_surface`. -/
theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListGenericCore fields scope stmts := by
  have hSup := hSupported
  induction hSupported with
  | compileCore hcore => exact stmtListGenericCore_of_stmtListCompileCore hcore
  | terminalCore hterminal => exact stmtListGenericCore_of_stmtListTerminalCore hterminal
  | setMappingUintSingle hk hsk hv hsv hslot =>
      exact stmtListGenericCore_setMappingUint_of_stmtSafety hk hsk hv hsv hslot hsafety
  | setMappingChainSingle hk hsk hv hsv hslot =>
      exact stmtListGenericCore_setMappingChain_of_stmtSafety hk hsk hv hsv hslot hsafety
  | setMappingSingle hk hsk hv hsv hslot =>
      exact stmtListGenericCore_setMapping_of_stmtSafety hk hsk hv hsv hslot hsafety
  | setMappingWordSingle hk hsk hv hsv hslot =>
      exact stmtListGenericCore_setMappingWord_of_stmtSafety hk hsk hv hsv hslot hsafety
  | setMappingPackedWordSingle hk hsk hv hsv hc1 hc2 hc3 hc4 hpacked hslot =>
      exact stmtListGenericCore_setMappingPackedWord_of_stmtSafety
        hk hsk hv hsv hc1 hc2 hc3 hc4 hpacked hslot hsafety
  | setStructMemberSingle hk hsk hv hsv hslot hmembers hmember =>
      exact stmtListGenericCore_setStructMember_of_stmtSafety
        hk hsk hv hsv hslot hmembers hmember hsafety
  | setMapping2Single hk1 hsk1 hk2 hsk2 hv hsv hslot =>
      exact stmtListGenericCore_setMapping2_of_stmtSafety hk1 hsk1 hk2 hsk2 hv hsv hslot hsafety
  | setMapping2WordSingle hk1 hsk1 hk2 hsk2 hv hsv hslot =>
      exact stmtListGenericCore_setMapping2Word_of_stmtSafety
        hk1 hsk1 hk2 hsk2 hv hsv hslot hsafety
  | setStructMember2Single hk1 hsk1 hk2 hsk2 hv hsv hslot hmembers hmember =>
      exact stmtListGenericCore_setStructMember2_of_stmtSafety
        hk1 hsk1 hk2 hsk2 hv hsv hslot hmembers hmember hsafety
  | requireClause clause hrest ih =>
      exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
        clause (ih (fun stmt hmem => hsafety stmt (List.mem_cons_of_mem _ hmem)) · hrest) hsurface
  | append hpfx hsfx ihPrefix ihSuffix =>
      exact stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites hpfx hsfx
        (ihPrefix (fun stmt hmem => hsafety stmt (List.mem_append_left _ hmem)) · hpfx)
        (ihSuffix (fun stmt hmem => hsafety stmt (List.mem_append_right _ hmem)) · hsfx) hsurface
  | _ =>
      exact stmtListGenericCore_of_supportedStmtList_of_surface hnoConflict hSup
        (stmtListTouchesUnsupportedContractSurface_singleton_of_exceptMappingWrites hsurface rfl)

/-- A global mapping-write slot-safety witness specializes to body-local slot safety for
every top-level statement of a supported statement list. -/
private theorem stmtMappingWriteSlotSafe_of_supportedStmtList
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields) :
    ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt := by
  induction hSupported with
  | compileCore hcore => exact stmtMappingWriteSlotSafe_of_stmtListCompileCore hcore
  | terminalCore hterminal => exact stmtMappingWriteSlotSafe_of_stmtListTerminalCore hterminal
  | setMappingUintSingle hk hsk hv hsv hslot =>
      exact List.forall_mem_singleton.2
        ⟨_, hslot, hsafety.setMappingUintSingle hk hsk hv hsv hslot⟩
  | setMappingChainSingle hk hsk hv hsv hslot =>
      exact List.forall_mem_singleton.2
        ⟨_, hslot, hsafety.setMappingChainSingle hk hsk hv hsv hslot⟩
  | setMappingSingle hk hsk hv hsv hslot =>
      exact List.forall_mem_singleton.2 ⟨_, hslot, hsafety.setMappingSingle hk hsk hv hsv hslot⟩
  | setMappingWordSingle hk hsk hv hsv hslot =>
      exact List.forall_mem_singleton.2
        ⟨_, hslot, hsafety.setMappingWordSingle hk hsk hv hsv hslot⟩
  | setMappingPackedWordSingle hk hsk hv hsv hc1 hc2 hc3 hc4 hpacked hslot =>
      exact List.forall_mem_singleton.2 ⟨_, hslot,
        hsafety.setMappingPackedWordSingle hk hsk hv hsv hc1 hc2 hc3 hc4 hpacked hslot⟩
  | setStructMemberSingle hk hsk hv hsv hslot hmembers hmember =>
      exact List.forall_mem_singleton.2 ⟨_, _, _, hslot, hmembers, hmember,
        hsafety.setStructMemberSingle hk hsk hv hsv hslot hmembers hmember⟩
  | setMapping2Single hk1 hsk1 hk2 hsk2 hv hsv hslot =>
      exact List.forall_mem_singleton.2
        ⟨_, hslot, hsafety.setMapping2Single hk1 hsk1 hk2 hsk2 hv hsv hslot⟩
  | setMapping2WordSingle hk1 hsk1 hk2 hsk2 hv hsv hslot =>
      exact List.forall_mem_singleton.2
        ⟨_, hslot, hsafety.setMapping2WordSingle hk1 hsk1 hk2 hsk2 hv hsv hslot⟩
  | setStructMember2Single hk1 hsk1 hk2 hsk2 hv hsv hslot hmembers hmember =>
      exact List.forall_mem_singleton.2 ⟨_, _, _, hslot, hmembers, hmember,
        hsafety.setStructMember2Single hk1 hsk1 hk2 hsk2 hv hsv hslot hmembers hmember⟩
  | requireClause clause _ ih =>
      refine List.forall_mem_cons.2 ⟨?_, ih⟩
      cases clause
      simp [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt, StmtMappingWriteSlotSafe]
  | append _ _ ihPrefix ihSuffix =>
      exact fun stmt hmem => (List.mem_append.1 hmem).elim (ihPrefix stmt) (ihSuffix stmt)
  | _ => exact List.forall_mem_singleton.2 trivial

theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListGenericCore fields scope stmts :=
  stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety hnoConflict
    hSupported (stmtMappingWriteSlotSafe_of_supportedStmtList hSupported hsafety) hsurface

/-- The current supported statement-list witness already suffices for the
weaker helper-free source-step interface consumed by the exact helper-aware
seam. This keeps helper-free reuse derivable directly from the proof-layer
fragment witness without exposing the stronger full generic-core theorem at the
supported-body boundary. -/
theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  stmtListHelperFreeStepInterface_of_core
    (stmtListGenericCore_of_supportedStmtList_of_surface
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoConflict
      hSupported
      hsurface)

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  stmtListHelperFreeStepInterface_of_core
    (stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoConflict
      hSupported
      hsafety
      hsurface)

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  stmtListHelperFreeStepInterface_of_core
    (stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoConflict
      hSupported
      hsafety
      hsurface)

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  have hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false :=
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
      stmts hcore hstate hcalls heffects
  stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites
    (fields := fields)
    (scope := scope)
    (stmts := stmts)
    hnoConflict
    hSupported
    hsafety
    hsurface

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites_stmtSafety
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false)
    (hsafety : ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  have hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false :=
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
      stmts hcore hstate hcalls heffects
  stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety
    (fields := fields)
    (scope := scope)
    (stmts := stmts)
    hnoConflict
    hSupported
    hsafety
    hsurface

theorem SupportedBodyInterface.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by
  have hsurface :
      stmtListTouchesUnsupportedContractSurface fn.body = false :=
    stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
      hBody.core.surfaceClosed
      hBody.state.surfaceClosed
      (SupportedBodyCallInterface.surfaceClosed (hBody := hBody))
      hBody.effects.surfaceClosed
  exact stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
    (fields := spec.fields)
    (scope := fn.params.map (·.name))
    (stmts := fn.body)
    hnoConflict
    hBody.stmtList
    hsurface

theorem SupportedBodyInterfaceExceptMappingWrites.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety spec.fields) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body :=
  stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites
    (fields := spec.fields)
    (scope := fn.params.map (·.name))
    (stmts := fn.body)
    hnoConflict
    hBody.stmtList
    hBody.core.surfaceClosed
    hBody.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites (hBody := hBody))
    hBody.effects.surfaceClosed
    hsafety

theorem SupportedBodyInterfaceExceptMappingWrites.helperFreeStepInterface_stmtSafety
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe spec.fields stmt) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body :=
  stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites_stmtSafety
    (fields := spec.fields)
    (scope := fn.params.map (·.name))
    (stmts := fn.body)
    hnoConflict
    hBody.stmtList
    hBody.core.surfaceClosed
    hBody.state.surfaceClosed
    (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites (hBody := hBody))
    hBody.effects.surfaceClosed
    hsafety

theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
    {spec : CompilationModel} {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {scope : List String} {stmts : List Stmt}
    (helperFuel : Nat) (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (_hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec fields (List.foldl stmtNextScope scope stmts) sourceResult irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · exact FunctionBody.compileStmtList_nil_eq_ok _ _ _ _ _ _ _ _
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmts, stmtStepMatchesIRExec]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpers hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      rcases hstep.preserves runtime state helperFuel _ hexact hscope hbounded hruntime
          (headSlack_le_append compiledIR tailIR extraFuel) with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨compiledIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface
          hstep.compileOk htailCompile,
        stmtStepMatchesIRExec_append_of_head hheadExec hheadMatch
          (fun _ h => execStmtListWithHelpers_cons_eq_of_continue (hsourceHead.trans h))
          (execStmtListWithHelpers_cons_eq_of_halt hsourceHead) ?_⟩
      rintro next tailState ⟨hruntime', hexact', hbounded', hscope'⟩
      exact (of_exists_eq_ok_of_eq_ok htailCompile <|
        ih (extraFuel := sizeOf (compiledIR ++ tailIR) - compiledIR.length -
          sizeOf tailIR + extraFuel) hscope' hexact' hbounded' hruntime' :)

theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {stmts : List Stmt}
    (helperFuel : Nat) (extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (_hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExecWithInternals
        fields (List.foldl stmtNextScope scope stmts) sourceResult irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], FunctionBody.compileStmtList_nil_eq_ok _ _ _ _ _ _ _ _, ?_⟩
      simp [SourceSemantics.execStmtListWithHelpers, execIRStmtsWithInternals,
        stmtStepMatchesIRExecWithInternals]
      exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      rcases hstep.preserves runtime state helperFuel _ hfuelPos hexact hscope hbounded
          hruntime (headSlack_le_append compiledIR tailIR extraFuel) with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨compiledIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface
          hstep.compileOk htailCompile,
        stmtStepMatchesIRExecWithInternals_append_of_head hheadExec hheadMatch
          (fun _ h => execStmtListWithHelpers_cons_eq_of_continue (hsourceHead.trans h))
          (execStmtListWithHelpers_cons_eq_of_halt hsourceHead) ?_⟩
      rintro next tailState ⟨hruntime', hexact', hbounded', hscope'⟩
      exact (of_exists_eq_ok_of_eq_ok htailCompile <|
        ih (extraFuel := sizeOf (compiledIR ++ tailIR) - compiledIR.length -
          sizeOf tailIR + extraFuel) hscope' hexact' hbounded' hruntime' :)

theorem exec_compileStmtList_generic_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_sizeOf_extraFuel_step
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (extraFuel := extraFuel)
      hgeneric
      hscope
      hexact
      hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, hcompile, ?_⟩
  exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hstep

theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hgeneric
      hscope
      hexact
      hbounded
      hnoErrors
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, by simpa [hnoEvents, hnoErrors] using hcompile, ?_⟩
  exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hstep

theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hfuelPos
      hgeneric
      hscope
      hexact
      hbounded
      hnoErrors
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, by simpa [hnoEvents, hnoErrors] using hcompile, ?_⟩
  exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep

/-- Spec-functions-aware sibling of
`exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel`.
It consumes the `WithInternals` helper-IR list witness directly, preserving the
`spec.functions` helper world through compile reconstruction and execution. -/
theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel_step
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {stmts : List Stmt} {irFuelSlack : Nat}
    (helperFuel : Nat) (extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (hreserve : irFuelSlack ≤ extraFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmts irFuelSlack)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts spec.functions =
          Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec :=
        execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExecWithInternals
        fields (List.foldl stmtNextScope scope stmts) sourceResult irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmtsWithInternals,
          stmtStepMatchesIRExecWithInternals]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons irFuelSlack scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIRWithInternals_exact
          hrest with ⟨tailIR, htailCompile⟩
      rcases hstep.preserves runtime state helperFuel _ hfuelPos hexact hscope hbounded
          hruntime (headSlack_add_le_append compiledIR tailIR hreserve) with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨compiledIR ++ tailIR,
        compileStmtList_cons_eq_ok_with_internals _ _ _ _ _ _ _ _ _ _ _ _ _
          hstep.compileOk htailCompile,
        stmtStepMatchesIRExecWithInternals_append_of_head hheadExec hheadMatch
          (fun _ h => execStmtListWithHelpers_cons_eq_of_continue (hsourceHead.trans h))
          (execStmtListWithHelpers_cons_eq_of_halt hsourceHead) ?_⟩
      rintro next tailState ⟨hruntime', hexact', hbounded', hscope'⟩
      exact (of_exists_eq_ok_of_eq_ok htailCompile <|
        ih (extraFuel := sizeOf (compiledIR ++ tailIR) - compiledIR.length -
          sizeOf tailIR + extraFuel) (by omega) hscope' hexact' hbounded' hruntime' :)

/-- Result-level wrapper for the spec-functions-aware helper-IR list execution
theorem. -/
theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts spec.functions = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec :=
        execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel_step
      helperFuel extraFuel hfuelPos (Nat.zero_le extraFuel) hgeneric hscope hexact hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, by simpa [hnoEvents, hnoErrors] using hcompile, ?_⟩
  exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep

/-- Events-preserving sibling of
`exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel`.
The step theorem already compiles against `spec.events`; callers that admit
scalar event heads only need to erase the still-unsupported error catalog. -/
theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_with_events
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events [] .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hfuelPos
      hgeneric
      hscope
      hexact
      hbounded
      hnoErrors
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, by simpa [hnoErrors] using hcompile, ?_⟩
  exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep
