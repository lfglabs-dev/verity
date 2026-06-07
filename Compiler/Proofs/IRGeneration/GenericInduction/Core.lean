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
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {slot wordOffset : Nat}
    {key1 key2 value : Expr}
    {members : List StructMember}
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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
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

private theorem false_of_supportedStmtList_emitEvent_surface
    {eventName : String}
    {args : List Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.emit eventName args] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.emit eventName args)
    (by simp [stmtTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_emitEvent_surface_exceptMappingWrites
    {eventName : String}
    {args : List Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.emit eventName args] = false) :
    False := by
  have hhead :
      stmtTouchesUnsupportedContractSurfaceExceptMappingWrites
        (Stmt.emit eventName args) = false := by
    simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface
  simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface] at hhead

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

private theorem false_of_supportedStmtList_letMappingField_surface
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mapping fieldName key)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mapping fieldName key))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMappingField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mapping fieldName key)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letMappingWordField_surface
    {tmp fieldName : String}
    {key : Expr} {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mappingWord fieldName key wordOffset)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mappingWord fieldName key wordOffset))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMappingWordField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key : Expr} {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mappingWord fieldName key wordOffset)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letMappingUintField_surface
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mappingUint fieldName key))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMappingUintField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letMappingPackedWordField_surface
    {tmp fieldName : String}
    {key : Expr} {wordOffset : Nat} {packed : PackedBits}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mappingPackedWord fieldName key wordOffset packed)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mappingPackedWord fieldName key wordOffset packed))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMappingPackedWordField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key : Expr} {wordOffset : Nat} {packed : PackedBits}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mappingPackedWord fieldName key wordOffset packed)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letMapping2Field_surface
    {tmp fieldName : String}
    {key1 key2 : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMapping2Field_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key1 key2 : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letMapping2WordField_surface
    {tmp fieldName : String}
    {key1 key2 : Expr} {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mapping2Word fieldName key1 key2 wordOffset)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mapping2Word fieldName key1 key2 wordOffset))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMapping2WordField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key1 key2 : Expr} {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.mapping2Word fieldName key1 key2 wordOffset)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letStructMemberField_surface
    {tmp fieldName : String}
    {key : Expr} {memberName : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.structMember fieldName key memberName)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.structMember fieldName key memberName))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letStructMemberField_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key : Expr} {memberName : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.structMember fieldName key memberName)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_letStructMember2Field_surface
    {tmp fieldName : String}
    {key1 key2 : Expr} {memberName : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.structMember2 fieldName key1 key2 memberName)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.structMember2 fieldName key1 key2 memberName))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letStructMember2Field_surface_exceptMappingWrites
    {tmp fieldName : String}
    {key1 key2 : Expr} {memberName : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.letVar tmp (Expr.structMember2 fieldName key1 key2 memberName)] = false) :
    False := by
  simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_setMappingUintSingle_surface
    {fieldName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingUint fieldName key value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingUint fieldName key value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingChainSingle_surface
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingChain fieldName keys value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingChain fieldName keys value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingSingle_surface
    {fieldName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping fieldName key value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping fieldName key value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingWordSingle_surface
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingWord fieldName key wordOffset value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingWord fieldName key wordOffset value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingPackedWordSingle_surface
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingPackedWord fieldName key wordOffset packed value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingPackedWord fieldName key wordOffset packed value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setStructMemberSingle_surface
    {fieldName memberName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setStructMember fieldName key memberName value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setStructMember fieldName key memberName value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMapping2Single_surface
    {fieldName : String}
    {key1 key2 value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping2 fieldName key1 key2 value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping2 fieldName key1 key2 value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMapping2WordSingle_surface
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping2Word fieldName key1 key2 wordOffset value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setStructMember2Single_surface
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setStructMember2 fieldName key1 key2 memberName value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setStructMember2 fieldName key1 key2 memberName value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_singleton_stmt_surface_exceptMappingWrites
    {stmt : Stmt}
    (hunsupported : stmtTouchesUnsupportedContractSurface stmt = true)
    (hnotMappingWrite : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt =
      stmtTouchesUnsupportedContractSurface stmt)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites [stmt] = false) :
    False := by
  have hhead : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
    simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface
  rw [hnotMappingWrite, hunsupported] at hhead
  contradiction

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
        (ih <| scopeNamesIncluded_cons hincluded)
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
        (ih <| scopeNamesIncluded_cons hincluded)
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

private theorem stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil => exact StmtListGenericCore.nil
  | letVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_letVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
  | assignVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_assignVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
  | require_ hcond hinScope hrest ih =>
      rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
        ⟨failCond, hfailCond⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_require
          (hcore := hcond)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hfailCompile := hfailCond))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
          (stmt := .require _ _) hincluded)
  | return_ hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_return
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .return _) hincluded)
  | stop hrest ih =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .stop) hincluded)
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
        ⟨offsetIR, hoffsetIR⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_mstore_single
          (hcoreOffset := hcoreOffset)
          (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
          (hcoreValue := hcoreValue)
          (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
          (hoffsetIR := hoffsetIR)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .mstore _ _) hincluded)
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
        ⟨offsetIR, hoffsetIR⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_tstore_single
          (hcoreOffset := hcoreOffset)
          (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
          (hcoreValue := hcoreValue)
          (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
          (hoffsetIR := hoffsetIR)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .tstore _ _) hincluded)

private theorem stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hterminal generalizing largerScope with
  | letVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_letVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
  | assignVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_assignVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
  | require_ hcond hinScope hrest ih =>
      rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
        ⟨failCond, hfailCond⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_require
          (hcore := hcond)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hfailCompile := hfailCond))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
          (stmt := .require _ _) hincluded)
  | return_ hvalue hinScope hrest =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_return
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .return _) hincluded))
  | stop hrest =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .stop) hincluded))
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
        ⟨offsetIR, hoffsetIR⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_mstore_single
          (hcoreOffset := hcoreOffset)
          (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
          (hcoreValue := hcoreValue)
          (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
          (hoffsetIR := hoffsetIR)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .mstore _ _) hincluded)
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
        ⟨offsetIR, hoffsetIR⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_tstore_single
          (hcoreOffset := hcoreOffset)
          (hinScopeOffset := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeOffset hincluded)
          (hcoreValue := hcoreValue)
          (hinScopeValue := exprBoundNamesInScope_of_scopeNamesIncluded hinScopeValue hincluded)
          (hoffsetIR := hoffsetIR)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .tstore _ _) hincluded)
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      rcases compiledStmtStep_ite (fields := fields) hcond
          (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded hthen hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded helse hincluded) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .ite _ _ _) hincluded))

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

private theorem stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
    {fields : List Field}
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope [clause.toStmt] := by
  cases clause with
  | mk family n m p q message =>
      cases family with
      | binary op =>
          cases op
          case eq =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case notEq =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case lt =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case gt =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case ge =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case le =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
      | andEqLt =>
          simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
            (show StmtListGenericCore fields scope
              [Stmt.require
                (Expr.logicalAnd (Expr.eq (Expr.literal n) (Expr.literal m))
                  (Expr.lt (Expr.literal p) (Expr.literal q)))
                message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require
                        (Expr.logicalAnd (Expr.eq (Expr.literal n) (Expr.literal m))
                          (Expr.lt (Expr.literal p) (Expr.literal q)))
                        message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
      | orEqLt =>
          simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
            (show StmtListGenericCore fields scope
              [Stmt.require
                (Expr.logicalOr (Expr.eq (Expr.literal n) (Expr.literal m))
                  (Expr.lt (Expr.literal p) (Expr.literal q)))
                message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require
                        (Expr.logicalOr (Expr.eq (Expr.literal n) (Expr.literal m))
                          (Expr.lt (Expr.literal p) (Expr.literal q)))
                        message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)

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
              collectStmtNames, collectExprNames]
      | andEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtNames, collectExprNames]
      | orEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtNames, collectExprNames]

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

private theorem stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero_exceptMappingWrites
    {varName : String}
    {body : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites
        [Stmt.forEach varName (.literal 0) body] = false) :
    stmtListTouchesUnsupportedContractSurface body = false := by
  cases body with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest =>
      simp only [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedContractSurface,
        stmtListTouchesUnsupportedContractSurface, Bool.or_false,
        Bool.or_eq_false_iff] at hsurface
      exact Bool.or_eq_false_iff.mpr hsurface

theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported with
  | compileCore hcore =>
      exact stmtListGenericCore_of_stmtListCompileCore hcore
  | terminalCore hterminal =>
      exact stmtListGenericCore_of_stmtListTerminalCore hterminal
  | setStorageSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | letStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | letStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | emitEvent _ _ =>
      exact False.elim (false_of_supportedStmtList_emitEvent_surface hsurface)
  | letMappingField _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMappingField_surface hsurface)
  | letMappingWordField _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMappingWordField_surface hsurface)
  | letMappingUintField _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMappingUintField_surface hsurface)
  | letMappingPackedWordField _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMappingPackedWordField_surface hsurface)
  | letMapping2Field _ _ _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMapping2Field_surface hsurface)
  | letMapping2WordField _ _ _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letMapping2WordField_surface hsurface)
  | letStructMemberField _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letStructMemberField_surface hsurface)
  | letStructMember2Field _ _ _ _ _ =>
      exact False.elim (false_of_supportedStmtList_letStructMember2Field_surface hsurface)
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingUintSingle_surface hsurface)
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingChainSingle_surface hsurface)
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingSingle_surface hsurface)
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingWordSingle_surface hsurface)
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingPackedWordSingle_surface hsurface)
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      exact False.elim (false_of_supportedStmtList_setStructMemberSingle_surface hsurface)
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMapping2Single_surface hsurface)
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMapping2WordSingle_surface hsurface)
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
      exact False.elim (false_of_supportedStmtList_setStructMember2Single_surface hsurface)
  | forEachLiteralBounded hbodyNames _ ih =>
      rcases compiledStmtStep_forEach_literal_zero hbodyNames
          (ih (stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero
            hsurface)) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | forEachLiteralEmpty n =>
      rename_i scope varName
      rcases compiledStmtStep_forEach_literal_empty
          (fields := fields) (scope := scope) (varName := varName) (n := n) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | requireClause clause _ ih =>
      simp [stmtListTouchesUnsupportedContractSurface] at hsurface
      apply stmtListGenericCore_append
        (stmtListGenericCore_singleton_requireLiteralGuardFamilyClause clause)
      simp only [List.foldl, stmtNextScope_requireLiteralGuardFamilyClause clause]
      exact ih hsurface.2
  | iteTerminal hcond hinScope hthen helse =>
      exact stmtListGenericCore_of_supportedStmtList_iteTerminal_of_surface
        hcond hinScope hthen helse
  | append _ _ ihPrefix ihSuffix =>
      simp only [stmtListTouchesUnsupportedContractSurface_append, Bool.or_eq_false_iff] at hsurface
      exact stmtListGenericCore_append (ihPrefix hsurface.1) (ihSuffix hsurface.2)

theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported with
  | compileCore hcore =>
      exact stmtListGenericCore_of_stmtListCompileCore hcore
  | terminalCore hterminal =>
      exact stmtListGenericCore_of_stmtListTerminalCore hterminal
  | setStorageSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | letStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | letStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | emitEvent _ _ =>
      exact False.elim
        (false_of_supportedStmtList_emitEvent_surface_exceptMappingWrites hsurface)
  | letMappingField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingField_surface_exceptMappingWrites hsurface)
  | letMappingWordField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingWordField_surface_exceptMappingWrites hsurface)
  | letMappingUintField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingUintField_surface_exceptMappingWrites hsurface)
  | letMappingPackedWordField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingPackedWordField_surface_exceptMappingWrites hsurface)
  | letMapping2Field _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMapping2Field_surface_exceptMappingWrites hsurface)
  | letMapping2WordField _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMapping2WordField_surface_exceptMappingWrites hsurface)
  | letStructMemberField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letStructMemberField_surface_exceptMappingWrites hsurface)
  | letStructMember2Field _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letStructMember2Field_surface_exceptMappingWrites hsurface)
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rcases hsafety.setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot with
        ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      rcases hsafety.setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot with
        ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety
        hkeys hscopeKeys hvalue hscopeValue hm hws hss
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rcases hsafety.setMappingSingle hkey hscopeKey hvalue hscopeValue hslot with
        ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMappingSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rcases hsafety.setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot with
        ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      rcases hsafety.setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
        hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot with
        ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue
        hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hm hws hss
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      rcases hsafety.setStructMemberSingle hkey hscopeKey hvalue hscopeValue
        hslot hmembers hmember with ⟨hm, hnotm2, hws, hss⟩
      exact stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hnotm2 hmembers hmember hws hss
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      rcases hsafety.setMapping2Single hkey1 hscope1 hkey2 hscope2
        hvalue hscopeValue hslot with ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hws hss
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      rcases hsafety.setMapping2WordSingle hkey1 hscope1 hkey2 hscope2
        hvalue hscopeValue hslot with ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hws hss
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue
      hslot hmembers hmember =>
      rcases hsafety.setStructMember2Single hkey1 hscope1 hkey2 hscope2
        hvalue hscopeValue hslot hmembers hmember with ⟨hm, hws, hss⟩
      exact stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hmembers hmember hws hss
  | forEachLiteralBounded hbodyNames _ ih =>
      rcases compiledStmtStep_forEach_literal_zero hbodyNames
          (ih (stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_contractSurface
            (stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero_exceptMappingWrites
              hsurface))) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | forEachLiteralEmpty n =>
      rename_i scope varName
      rcases compiledStmtStep_forEach_literal_empty
          (fields := fields) (scope := scope) (varName := varName) (n := n) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | requireClause clause _ ih =>
      exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
        clause ih hsurface
  | iteTerminal hcond hinScope hthen helse =>
      exact stmtListGenericCore_of_supportedStmtList_iteTerminal_of_surface
        hcond hinScope hthen helse
  | append hpfx hsfx ihPrefix ihSuffix =>
      exact stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
        hpfx hsfx ihPrefix ihSuffix hsurface

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

theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : ∀ stmt ∈ stmts, StmtMappingWriteSlotSafe fields stmt)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported with
  | compileCore hcore =>
      exact stmtListGenericCore_of_stmtListCompileCore hcore
  | terminalCore hterminal =>
      exact stmtListGenericCore_of_stmtListTerminalCore hterminal
  | setStorageSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | letStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | letStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_letStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageField_of_surface
        hnoConflict hfind hfieldInScope
  | assignStorageAddrField hfind hfieldInScope =>
      exact stmtListGenericCore_of_supportedStmtList_assignStorageAddrField_of_surface
        hnoConflict hfind hfieldInScope
  | emitEvent _ _ =>
      exact False.elim
        (false_of_supportedStmtList_emitEvent_surface_exceptMappingWrites hsurface)
  | letMappingField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingField_surface_exceptMappingWrites hsurface)
  | letMappingWordField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingWordField_surface_exceptMappingWrites hsurface)
  | letMappingUintField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingUintField_surface_exceptMappingWrites hsurface)
  | letMappingPackedWordField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMappingPackedWordField_surface_exceptMappingWrites hsurface)
  | letMapping2Field _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMapping2Field_surface_exceptMappingWrites hsurface)
  | letMapping2WordField _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letMapping2WordField_surface_exceptMappingWrites hsurface)
  | letStructMemberField _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letStructMemberField_surface_exceptMappingWrites hsurface)
  | letStructMember2Field _ _ _ _ _ =>
      exact False.elim
        (false_of_supportedStmtList_letStructMember2Field_surface_exceptMappingWrites hsurface)
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rename_i scope fieldName key value slot0
      rcases hsafety (.setMappingUint fieldName key value) (by simp) with ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      rename_i scope fieldName keys value slot0
      rcases hsafety (.setMappingChain fieldName keys value) (by simp) with ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety
        hkeys hscopeKeys hvalue hscopeValue hm hws hss
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rename_i scope fieldName key value slot0
      rcases hsafety (.setMapping fieldName key value) (by simp) with ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMappingSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      rename_i scope fieldName key value wordOffset slot0
      rcases hsafety (.setMappingWord fieldName key wordOffset value) (by simp) with ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hws hss
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      rename_i scope fieldName key value wordOffset slot0 packed
      rcases hsafety (.setMappingPackedWord fieldName key wordOffset packed value) (by simp) with
        ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue
        hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hm hws hss
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      rename_i scope fieldName memberName key value slot0 wordOffset0 members0
      rcases hsafety (.setStructMember fieldName key memberName value) (by simp) with ⟨slot, wordOffset, members, hfind, hmembers',
        hmember', hm, hnotm2, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      have hmembersEq : members = members0 := by
        rw [hmembers] at hmembers'
        injection hmembers' with hEq
        exact hEq.symm
      subst hslotEq
      subst hmembersEq
      have hwordOffsetEq : wordOffset = wordOffset0 := by
        rw [hmember] at hmember'
        injection hmember' with hmemberEq
        injection hmemberEq with _ _ hEq
        exact hEq.symm
      subst hwordOffsetEq
      exact stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
        hkey hscopeKey hvalue hscopeValue hm hnotm2 hmembers hmember hws hss
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      rename_i scope fieldName key1 key2 value slot0
      rcases hsafety (.setMapping2 fieldName key1 key2 value) (by simp) with ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hws hss
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2
      hvalue hscopeValue hslot =>
      rename_i scope fieldName key1 key2 value wordOffset slot0
      rcases hsafety (.setMapping2Word fieldName key1 key2 wordOffset value) (by simp) with
        ⟨slot, hfind, hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hslotEq
      exact stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hws hss
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue
      hslot hmembers hmember =>
      rename_i scope fieldName memberName key1 key2 value slot0 wordOffset0 members0
      rcases hsafety (.setStructMember2 fieldName key1 key2 memberName value) (by simp) with ⟨slot, wordOffset, members, hfind, hmembers',
        hmember', hm, hws, hss⟩
      have hslotEq : slot = slot0 := by
        rw [hslot] at hfind
        injection hfind with hEq
        exact hEq.symm
      have hmembersEq : members = members0 := by
        rw [hmembers] at hmembers'
        injection hmembers' with hEq
        exact hEq.symm
      subst hslotEq
      subst hmembersEq
      have hwordOffsetEq : wordOffset = wordOffset0 := by
        rw [hmember] at hmember'
        injection hmember' with hmemberEq
        injection hmemberEq with _ _ hEq
        exact hEq.symm
      subst hwordOffsetEq
      exact stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
        hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hm hmembers hmember hws hss
  | forEachLiteralBounded hbodyNames hbody ih =>
      rcases compiledStmtStep_forEach_literal_zero hbodyNames
          (stmtListGenericCore_of_supportedStmtList_of_surface
            hnoConflict hbody (by
              exact stmtListTouchesUnsupportedContractSurface_body_of_singleton_forEach_zero_exceptMappingWrites
                hsurface)) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | forEachLiteralEmpty n =>
      rename_i scope varName
      rcases compiledStmtStep_forEach_literal_empty
          (fields := fields) (scope := scope) (varName := varName) (n := n) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep StmtListGenericCore.nil
  | requireClause clause hsupportedRest ih =>
      exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
        clause
        (fun hrestSurface =>
          ih
            (fun stmt hmem => hsafety stmt (by simp [hmem]))
            hrestSurface)
        hsurface
  | iteTerminal hcond hinScope hthen helse =>
      exact stmtListGenericCore_of_supportedStmtList_iteTerminal_of_surface
        hcond hinScope hthen helse
  | append hpfx hsfx ihPrefix ihSuffix =>
      exact stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
        hpfx hsfx
        (fun hpfxSurface =>
          ihPrefix
            (fun stmt hmem => hsafety stmt (by simp [hmem]))
            hpfxSurface)
        (fun hsfxSurface =>
          ihSuffix
            (fun stmt hmem => hsafety stmt (by simp [hmem]))
            hsfxSurface)
        hsurface

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


private theorem scopeNamesIncluded_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt} :
    FunctionBody.scopeNamesIncluded scope (List.foldl stmtNextScope scope stmts) := by
  induction stmts generalizing scope with
  | nil =>
      simpa using FunctionBody.scopeNamesIncluded_refl
  | cons stmt rest ih =>
      intro name hname
      exact ih (scope := stmtNextScope scope stmt) name (mem_stmtNextScope_of_mem_scope hname)

private theorem stmtListGenericCore_of_requireClausesOnly
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) :=
  stmtListGenericCore_of_stmtListCompileCore
    (stmtListCompileCore_of_requireLiteralGuardFamilyClauses clauses)

private theorem stmtListGenericCore_of_requireClausesThenReturnLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.return (Expr.literal retVal)]) := by
  have htail :
      FunctionBody.StmtListCompileCore scope [Stmt.return (Expr.literal retVal)] := by
    refine FunctionBody.StmtListCompileCore.return_ (.literal retVal) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

private theorem stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (tmp : String)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)]) := by
  have htail :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal retVal) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · refine FunctionBody.StmtListCompileCore.return_ (.localVar tmp) ?_ ?_
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem
        simp [hmem]
      · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

private theorem stmtListGenericCore_of_requireClausesThenSetStorageLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName : String)
    (slot writeVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.setStorage fieldName (Expr.literal writeVal)]) :=
  stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_singleton_setStorage_singleSlot
          (fields := fields)
          (scope := scope)
          (hnoConflict := hnoConflict)
          (hfind := hfind)
          (hcore := .literal writeVal)
          (hinScope := by intro name hmem; simp [FunctionBody.exprBoundNames] at hmem)))

private theorem stmtListGenericCore_of_requireClausesThenLetSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
  have hprefix :
      FunctionBody.StmtListCompileCore scope [Stmt.letVar tmp (Expr.literal n)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope [Stmt.letVar tmp (Expr.literal n)])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

private theorem stmtListGenericCore_of_requireClausesThenLetAssignSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.literal m),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · refine FunctionBody.StmtListCompileCore.assignVar (.literal m) ?_ ?_
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem
      · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

private theorem stmtListGenericCore_of_requireClausesThenLetAssignAddSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.add (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

private theorem stmtListGenericCore_of_requireClausesThenLetAssignSubSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.sub (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

private theorem stmtListGenericCore_of_requireClausesThenLetAssignMulSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.mul (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

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
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
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
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope_with_surface
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
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
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope_with_surface
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
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

private theorem yulStmtList_length_add_sizeOf_le_append
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

private theorem scopeNamesIncluded_stmtNextScope
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope stmt)
      (collectStmtNames stmt ++ inScopeNames) := by
  intro name hname
  rcases List.mem_append.mp hname with hhead | htail
  · exact List.mem_append.mpr <| Or.inl hhead
  · exact List.mem_append.mpr <| Or.inr <| hincluded name htail

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

theorem exec_compileStmtList_generic_sizeOf_extraFuel_step
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
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericCore hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false scope [] (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state headExtraFuel
          hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
          have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
          dsimp [bodyIR]; omega
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec'
          rw [hrw]
          congr 1
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtList fields runtime (stmt :: rest) =
            SourceSemantics.execStmtList fields ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtList, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .stop ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .return ‹Nat› ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .revert ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExec]

theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
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
    (_hnoEvents : spec.events = [])
    (_hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmts, stmtStepMatchesIRExec]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpers hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields spec.events spec.errors .calldata [] false scope [] (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state helperFuel headExtraFuel
          hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
          have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
          dsimp [bodyIR]; omega
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec'
          rw [hrw]
          congr 1
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
            SourceSemantics.execStmtListWithHelpers spec fields helperFuel
              ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .stop ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .return ‹Nat› ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .revert ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExec]

-- Old placeholder proof body removed; the proof now uses scope directly.

theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
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
    (_hnoEvents : spec.events = [])
    (_hnoErrors : spec.errors = [])
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExecWithInternals
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmtsWithInternals,
              stmtStepMatchesIRExecWithInternals]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields spec.events spec.errors .calldata [] false scope [] (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok_with_surface
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state helperFuel headExtraFuel
          hfuelPos hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;>
        simp [stmtStepMatchesIRExecWithInternals] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmtsWithInternals runtimeContract
                (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmtsWithInternals_append_of_continue
              runtimeContract
              (sizeOf bodyIR + extraFuel + 1)
              state
              ‹IRState›
              compiledIR
              tailIR
              hheadExec'
          rw [hrw]
          congr 1
          have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
            have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
            dsimp [bodyIR]; omega
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
            SourceSemantics.execStmtListWithHelpers spec fields helperFuel
              ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .stop ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .return ‹Nat› ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .revert ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExecWithInternals]

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
      hnoEvents
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
      hnoEvents
      hnoErrors
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, by simpa [hnoEvents, hnoErrors] using hcompile, ?_⟩
  exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep

theorem supported_function_body_correct_from_exact_state_generic
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors, hnoAdtTypes] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hgeneric
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

/-- Exact helper-aware body theorem for a helper-aware generic statement
induction witness. This is the induction-level target needed to replace the
current helper-free `SupportedStmtList` gate with compositional helper-step
proofs. -/
private theorem supported_function_body_correct_from_exact_state_generic_helper_steps_raw
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtListWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors, hnoAdtTypes] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hgeneric
      hscope
      hscopeExact
      hbounded
      hnoEvents
      hnoErrors
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

/-- Exact future helper-aware body theorem target: helper-aware source semantics
against helper-aware compiled-body semantics. This is the body-level theorem
shape needed once helper-rich statements enter the proved domain, because raw
`execIRStmts` rejects Yul constructs such as `letMany` that represent internal
helper calls. -/
def SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmtListWithHelpers
      model
      (SourceSemantics.effectiveFields model)
      helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings
        selector := tx.functionSelector }
      fn.body = sourceResult ∧
    execIRStmtsWithInternals runtimeContract
      (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
    stmtResultMatchesIRExecWithInternals
      (SourceSemantics.effectiveFields model) sourceResult irExec

/-- Exact helper-aware body theorem for an exact helper-aware generic
statement-induction witness. Unlike the transitional legacy-compiled-body
theorem, this already targets `execIRStmtsWithInternals`, so future helper-call
cases can be proved against the compiled semantics that actually executes
helper-rich Yul. -/
private theorem
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors, hnoAdtTypes] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
      (runtimeContract := runtimeContract)
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hfuelPos
      hgeneric
      hscope
      hscopeExact
      hbounded
      hnoEvents
      hnoErrors
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

/-- Transitional helper-aware body/IR preservation target for the non-core
generic body theorem. This already moves the source side onto helper-aware
semantics, but the compiled side still runs through legacy `execIRStmts`, so it
only matches the current helper-free compiled-body boundary. -/
def SupportedFunctionBodyWithHelpersIRPreservationGoal
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmtListWithHelpers
      model
      (SourceSemantics.effectiveFields model)
      helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings
        selector := tx.functionSelector }
      fn.body = sourceResult ∧
    execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
    FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec

/-- Disjoint-based body-level bridge: the helper-free compiled-body goal lifts to
the exact helper-aware compiled-body target when the compiled body is disjoint
from the runtime contract's internal function table.  Does **not** require
`runtimeContract.internalFunctions = []`. -/
theorem supported_function_body_with_helpers_and_helper_ir_goal_of_legacy_ir_goal_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hbody :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompat :=
    execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
      (bodyStmts.length + extraFuel + 1)
      state
      bodyStmts
      hdisjoint
  cases irExec with
  | «continue» next =>
      refine ⟨sourceResult, .continue next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | «return» value next =>
      refine ⟨sourceResult, .return value next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | stop next =>
      refine ⟨sourceResult, .stop next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | revert next =>
      refine ⟨sourceResult, .revert next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch

/-- Under compiled-body disjointness, the exact helper-aware body goal can also
be collapsed back to the legacy compiled-body goal. This keeps the new exact
helper-aware seam reusable with the existing function-level theorem surface
until callers are ready to retarget all the way to `execIRFunctionWithInternals`. -/
theorem supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hbody :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompat :=
    execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
      (bodyStmts.length + extraFuel + 1)
      state
      bodyStmts
      hdisjoint
  rw [hcompat] at hbodyExec
  -- hbodyExec : (match execIRStmts ... with ...) = irExec
  -- case-split on `execIRStmts` to reduce the match in hbodyExec
  generalize hexec : execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irPlain at hbodyExec
  cases irPlain with
  | «continue» next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .continue next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | «return» value next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .return value next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | stop next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .stop next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | revert next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .revert next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩

/-- Exact helper-aware body theorem for a helper-aware generic statement
induction witness. This is the induction-level target needed to replace the
current helper-free `SupportedStmtList` gate with compositional helper-step
proofs. -/
theorem supported_function_body_correct_from_exact_state_generic_helper_steps
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact supported_function_body_correct_from_exact_state_generic_helper_steps_raw
    model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
    hextraFuel hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
    hbounded hstateRuntime hstateBindings

/-- Exact helper-aware body theorem for an exact helper-aware generic
statement-induction witness. This is the future-proof induction-level theorem
surface for helper-rich bodies because it already targets
`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`. -/
theorem supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

theorem supported_function_body_correct_from_exact_state_generic_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hsteps :
      StmtListHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hsteps := hsteps)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hinternal
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

/-- Body-level exact helper-aware bridge over the split helper-positive
interfaces: genuine internal-helper heads are discharged separately from the
residual coarse helper-surface heads, so future helper-summary work does not
also need to prove unrelated non-helper exact-step cases. -/
theorem supported_function_body_correct_from_exact_state_generic_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hinternalSteps :
      StmtListInternalHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidualSteps :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hinternal := hinternalSteps)
      (hresidual := hresidualSteps)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

/-- Body-level exact helper-aware bridge over the fully split genuine-helper
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are supplied separately, so the next helper-rich
proof step can land at the exact source-side obligation it discharges. -/
theorem supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hcall := hcall)
      (hassign := hassign)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

/-- Body-level exact helper-aware bridge over the fully split genuine-helper
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are supplied separately, so the next helper-rich
proof step can land at the exact source-side obligation it discharges. -/
theorem supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdirect :
      StmtListDirectInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hdirect := hdirect)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

private theorem
    generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    StmtListGenericWithHelpersAndHelperIR
      runtimeContract
      model
      (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name))
      fn.body :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    (runtimeContract := runtimeContract)
    (spec := model)
    (hhelperFree := hhelperFree)
    (hsteps :=
      stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
        (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
            hcall
            hassign)
          hexpr
          hstruct)
        hresidual)
    (hnoEvents := hnoEvents)
    (hnoErrors := hnoErrors)
    (hdisjoint := hdisjoint)

/-- Disjoint-based body-level exact helper-aware bridge over the fully split
genuine-helper interfaces.  Replaces `StmtListHelperFreeCompiledLegacyCompatible`
+ `runtimeContract.internalFunctions = []` with the weaker
`StmtListHelperFreeCompiledCallsDisjoint`.  This is the entry point for
function bodies that live in a contract with an internal helper table. -/
theorem supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
      runtimeContract model fn hhelperFree hcall hassign hexpr hstruct hresidual
      hnoEvents hnoErrors hdisjoint
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

/-- Focused Tier 2 entry point for bodies whose only genuinely new helper work
is direct `Stmt.internalCallAssign`. Void helper statements, expression-position
helper calls, and structural helper recursion stay fail-closed, while the
assign-specific exact-step interface can be discharged by future helper-rank
induction independently. Residual non-helper helper-surface cases remain an
explicit obligation instead of being hidden behind the coarse old gate. -/
theorem
    supported_function_body_correct_from_exact_state_generic_with_direct_internal_helper_assign_steps_and_helper_ir_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcallClosed :
      stmtListTouchesDirectInternalHelperCallSurface fn.body = false)
    (hexprClosed :
      stmtListTouchesExprInternalHelperSurface fn.body = false)
    (hstructClosed :
      stmtListTouchesStructuralInternalHelperSurface fn.body = false)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hnoAdtTypes : model.adtTypes = [])
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperFree
      (stmtListDirectInternalHelperCallStepInterface_of_directCallSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hcallClosed)
      hassign
      (stmtListExprInternalHelperStepInterface_of_exprSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hexprClosed)
      (stmtListStructuralInternalHelperStepInterface_of_structuralSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hstructClosed)
      hresidual
      hdisjoint
      (by simpa [hnoAdtTypes] using hbodyCompile)
      hscope hbounded hstateRuntime hstateBindings

/-- Current-fragment disjointness-based wrapper that lands directly in the exact
helper-aware compiled body goal. This keeps the existing helper-free step
library reusable while exposing the weaker compiled-side condition that later
helper-table work actually needs. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (_hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false :=
    stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
      hcontractSurface
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperFree
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      hdisjoint
      hbodyCompile
      hscope hbounded hstateRuntime hstateBindings

/-- Current-fragment wrapper that lands directly in the exact helper-aware
compiled body goal. This keeps the existing helper-free step library reusable,
but removes the need for callers to supply a separate
`StmtListCompiledLegacyCompatible` witness when the body already lies on the
current supported contract surface. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body := by
    simpa [hnormalized] using
      (stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface
        (runtimeContract := runtimeContract)
        (fields := model.fields)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hnoPacked
        hcontractSurface
        hinternal)
  exact
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hnoPacked hcontractSurface
      hhelperFree hbodyCompile hscope hbounded hstateRuntime hstateBindings hdisjoint

/-- Tier 2 disjointness-based exact helper-aware wrapper for the alternate
singleton mapping-write contract surface. This keeps the helper-aware
compiled-body seam available even before those writes are promoted onto the
default support path, without assuming the runtime helper table is empty. -/
theorem
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (_hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (_hcontractSurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites fn.body = false)
    (hhelperSurface :
      stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperFree
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      hdisjoint
      hbodyCompile
      hscope hbounded hstateRuntime hstateBindings

/-- Tier 2 exact helper-aware wrapper for the alternate singleton
mapping-write contract surface. This keeps the helper-aware compiled-body seam
available even before those writes are promoted onto the default support path. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites fn.body = false)
    (hhelperSurface :
      stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body := by
    simpa [hnormalized] using
      (stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface_exceptMappingWrites
        (runtimeContract := runtimeContract)
        (fields := model.fields)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hnoPacked
        hcontractSurface
        hinternal)
  exact
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hnoPacked hcontractSurface hhelperSurface
      hhelperFree hbodyCompile hscope hbounded hstateRuntime hstateBindings hdisjoint

/-- Goal-based helper-aware wrapper around the generic body/IR preservation
theorem. This keeps the current helper-free collapse available as a corollary,
while making the direct helper-aware body/IR target explicit in Lean. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_goal
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body)
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  rcases supported_function_body_correct_from_exact_state_generic
      model fn bodyStmts tx initialWorld state bindings extraFuel hextraFuel
      hnormalized hnoEvents hnoErrors hnoAdtTypes hgeneric hbodyCompile hscope hbounded
      hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
  have hsourceWithEvents :
      SourceSemantics.execStmtListWithEvents (SourceSemantics.effectiveFields model) model.events
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult := by
    simpa [hnoEvents] using hsource
  simpa [hnoEvents, SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
    hhelperGoal.trans hsourceWithEvents

/-- Helper-aware wrapper around the generic body/IR preservation theorem.
This theorem now consumes the exact source-side helper-conservative-extension
goal rather than baking in the temporary fail-closed helper scan directly.
Today that goal is still discharged from `stmtListTouchesUnsupportedHelperSurface
= false`; later helper-summary/rank composition should target the same named
goal surface without another theorem-shape change. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgenericWithHelpers :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
      (spec := model)
      (hhelperFree := hhelperFree)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hhelperSurface
  exact supported_function_body_correct_from_exact_state_generic_helper_steps
    model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
    hextraFuel hnormalized hnoEvents hnoErrors hnoAdtTypes hgenericWithHelpers hbodyCompile
    hscope hbounded hstateRuntime hstateBindings


end Compiler.Proofs.IRGeneration
