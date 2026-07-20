import Compiler.Proofs.IRGeneration.GenericInduction.Storage

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

attribute [local simp] CompilationModel.compileExprWithInternals_nil_eq

private def setStorageWordSlotExpr (slot wordOffset : Nat) : YulExpr :=
  if wordOffset == 0 then YulExpr.lit slot
  else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset]

private def setStorageWordIRStmts (slot wordOffset : Nat) (valueIR : YulExpr) : List YulStmt :=
  [YulStmt.exprStmt (YulExpr.call "sstore" [setStorageWordSlotExpr slot wordOffset, valueIR])]

private def setStorageWordPreservesGoal
    (fields : List Field) (scope : List String) (fieldName : String) (value : Expr)
    (wordOffset : Nat) (valueIR : YulExpr) (baseSlot : Nat)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmt fields runtime (.setStorageWord fieldName wordOffset value) =
      sourceResult ∧
    execIRStmts ((setStorageWordIRStmts baseSlot wordOffset valueIR).length + extraFuel + 1)
      state (setStorageWordIRStmts baseSlot wordOffset valueIR) = irExec ∧
    stmtStepMatchesIRExec fields
      (stmtNextScope scope (.setStorageWord fieldName wordOffset value)) sourceResult irExec

private def setStorageWordTargetSafe (fields : List Field) (targetSlot : Nat) : Prop :=
  (∃ f, findResolvedFieldAtSlotCopy fields targetSlot = some f ∧
    SourceSemantics.fieldUsesAddressStorage f = false ∧
    SourceSemantics.fieldUsesDynamicArrayStorage f = false) ∨
  (findResolvedFieldAtSlotCopy fields targetSlot = none ∧
    ∀ runtime : SourceSemantics.RuntimeState,
      findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none)

private def setStorageWordTargetSafeForRuntime
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (targetSlot : Nat) : Prop :=
  (∃ f, findResolvedFieldAtSlotCopy fields targetSlot = some f ∧
    SourceSemantics.fieldUsesAddressStorage f = false ∧
    SourceSemantics.fieldUsesDynamicArrayStorage f = false) ∨
  (findResolvedFieldAtSlotCopy fields targetSlot = none ∧
    findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none)

private theorem compileExprWithInternals_nil_ok
    {fields : List Field} {dynamicSource : DynamicDataSource} {expr : Expr} {exprIR : YulExpr}
    (h : CompilationModel.compileExpr fields dynamicSource expr = Except.ok exprIR) :
    CompilationModel.compileExprWithInternals fields dynamicSource [] expr = Except.ok exprIR := by
  simpa [CompilationModel.compileExprWithInternals_nil_eq] using h

private theorem uint256_add_val_eq_mod (a b : Nat) :
    (Verity.Core.Uint256.ofNat a + Verity.Core.Uint256.ofNat b).val =
      (a + b) % Compiler.Constants.evmModulus := by
  change ((a % Compiler.Constants.evmModulus) + (b % Compiler.Constants.evmModulus)) %
      Compiler.Constants.evmModulus =
    (a + b) % Compiler.Constants.evmModulus
  exact (Nat.add_mod a b Compiler.Constants.evmModulus).symm

private theorem IRStorageSlot.toNat_ofNat_wordNormalize (slot : Nat) :
    (IRStorageSlot.ofNat slot).toNat = SourceSemantics.wordNormalize slot := by
  simp [IRStorageSlot.toNat_ofNat, SourceSemantics.wordNormalize,
    Compiler.Constants.evmModulus, EvmYul.UInt256.size]

private theorem IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat
    {query : IRStorageSlot} {slot : Nat}
    (hneq : query ≠ IRStorageSlot.ofNat slot) :
    query.toNat ≠ SourceSemantics.wordNormalize slot := by
  intro h
  apply hneq
  apply IRStorageSlot.eq_of_toNat_eq
  simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using h

private theorem execIRStmt_sstore_of_eval
    {state : IRState}
    {slotExpr valueExpr : YulExpr}
    {slotVal valueVal : Nat}
    {fuel : Nat}
    (hslot : evalIRExpr state slotExpr = some slotVal)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.exprStmt (YulExpr.call "sstore" [slotExpr, valueExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slotVal valueVal } := by
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

private theorem evalIRExpr_storageWordTarget_of_eval
    {state : IRState} {slot wordOffset : Nat} :
    evalIRExpr state
      (if wordOffset == 0 then YulExpr.lit slot
       else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset]) =
      some (if wordOffset == 0 then slot else (slot + wordOffset) % Compiler.Constants.evmModulus) := by
  by_cases hzero : wordOffset = 0
  · subst hzero
    simp [evalIRExpr]
  · have hAdd :=
      FunctionBody.evalIRExpr_add_of_eval
        (state := state)
        (lhs := YulExpr.lit slot)
        (rhs := YulExpr.lit wordOffset)
        (a := slot)
        (b := wordOffset)
        (by simp [evalIRExpr])
        (by simp [evalIRExpr])
    simpa [hzero] using hAdd

private theorem storageWordTarget_eq_wordNormalize
    (slot wordOffset : Nat) :
    (if wordOffset == 0 then slot else (slot + wordOffset) % Compiler.Constants.evmModulus) %
        Compiler.Constants.evmModulus =
      SourceSemantics.wordNormalize (slot + wordOffset) := by
  by_cases hzero : wordOffset = 0
  · subst hzero
    simp [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus]
  · simp [hzero, SourceSemantics.wordNormalize, Compiler.Constants.evmModulus]
    exact (uint256_add_val_eq_mod slot wordOffset).symm

private theorem bindingsExactlyMatchIRVarsOnScope_writeStorageWordSlot
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

private theorem findDynamicArrayElementAtSlot_writeStorageWordSlots_none
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {slot wordOffset targetSlot value : Nat}
    (hdynNone : findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none) :
    SourceSemantics.findDynamicArrayElementAtSlot fields
        (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
        (IRStorageSlot.ofNat targetSlot).toNat = none := by
  have hdynNorm :
      findDynamicArrayElementAtSlotCopy fields runtime.world
          (IRStorageSlot.ofNat targetSlot).toNat =
        findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot := by
    rw [IRStorageSlot.toNat_ofNat_wordNormalize]
    simpa [SourceSemantics.wordNormalize] using
      findDynamicArrayElementAtSlotCopy_wordNormalize fields runtime.world targetSlot
  have hcongr :=
    SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray
      fields
      (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
      runtime.world
      (IRStorageSlot.ofNat targetSlot).toNat
      (by simp [SourceSemantics.writeStorageWordSlots])
  have hold :
      SourceSemantics.findDynamicArrayElementAtSlot fields runtime.world
          (IRStorageSlot.ofNat targetSlot).toNat = none := by
    rw [findDynamicArrayElementAtSlotCopy_eq, hdynNorm, hdynNone]
  exact hcongr.trans hold

private theorem encodeStorageAt_writeStorageWordSlot_target_none
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {slot wordOffset targetSlot value : Nat}
    (hresolvedNone : findResolvedFieldAtSlotCopy fields targetSlot = none)
    (hdynNone : findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none)
    (htargetEq : targetSlot % Compiler.Constants.evmModulus =
      SourceSemantics.wordNormalize (slot + wordOffset))
    (hvalue : value < Verity.Core.Uint256.modulus) :
    IRStorageWord.ofNat value =
      IRStorageWord.ofNat
        (SourceSemantics.encodeStorageAt fields
          (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
          (IRStorageSlot.ofNat targetSlot).toNat) := by
  have hqueryTarget :
      (IRStorageSlot.ofNat targetSlot).toNat =
        SourceSemantics.wordNormalize (slot + wordOffset) := by
    simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using htargetEq
  have hresolvedNorm :
      findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat targetSlot).toNat =
        findResolvedFieldAtSlotCopy fields targetSlot := by
    rw [IRStorageSlot.toNat_ofNat_wordNormalize]
    simpa [SourceSemantics.wordNormalize] using
      findResolvedFieldAtSlotCopy_wordNormalize fields targetSlot
  rw [SourceSemantics.encodeStorageAt]
  rw [findResolvedFieldAtSlotCopy_eq, hresolvedNorm, hresolvedNone]
  have hdynWritten :=
    findDynamicArrayElementAtSlot_writeStorageWordSlots_none
      (fields := fields) (runtime := runtime)
      (slot := slot) (wordOffset := wordOffset)
      (targetSlot := targetSlot) (value := value) hdynNone
  rw [hdynWritten]
  simp [SourceSemantics.writeStorageWordSlots, hqueryTarget,
    SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat,
    Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    htargetEq, Nat.mod_eq_of_lt hvalue]
  exact congrArg IRStorageWord.ofNat (Nat.mod_eq_of_lt hvalue).symm

private theorem encodeStorageAt_writeStorageWordSlot_target
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {slot wordOffset targetSlot value : Nat}
    (htarget : setStorageWordTargetSafeForRuntime fields runtime targetSlot)
    (htargetEq : targetSlot % Compiler.Constants.evmModulus =
      SourceSemantics.wordNormalize (slot + wordOffset))
    (hvalue : value < Verity.Core.Uint256.modulus) :
    IRStorageWord.ofNat value =
      IRStorageWord.ofNat
        (SourceSemantics.encodeStorageAt fields
          (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
          (IRStorageSlot.ofNat targetSlot).toNat) := by
  have hqueryTarget :
      (IRStorageSlot.ofNat targetSlot).toNat =
        SourceSemantics.wordNormalize (slot + wordOffset) := by
    simpa [IRStorageSlot.toNat_ofNat_wordNormalize] using htargetEq
  have hresolvedNorm :
      findResolvedFieldAtSlotCopy fields (IRStorageSlot.ofNat targetSlot).toNat =
        findResolvedFieldAtSlotCopy fields targetSlot := by
    rw [IRStorageSlot.toNat_ofNat_wordNormalize]
    simpa [SourceSemantics.wordNormalize] using
      findResolvedFieldAtSlotCopy_wordNormalize fields targetSlot
  rcases htarget with hresolved | hnone
  · rcases hresolved with ⟨f, hf, hnotAddr, hnotDyn⟩
    rw [SourceSemantics.encodeStorageAt]
    rw [findResolvedFieldAtSlotCopy_eq, hresolvedNorm]
    simp [hf, hnotAddr, hnotDyn, SourceSemantics.writeStorageWordSlots,
      hqueryTarget, SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat,
      Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
      htargetEq, Nat.mod_eq_of_lt hvalue]
    exact congrArg IRStorageWord.ofNat (Nat.mod_eq_of_lt hvalue).symm
  · rcases hnone with ⟨hresolvedNone, hdynNone⟩
    exact encodeStorageAt_writeStorageWordSlot_target_none
      hresolvedNone hdynNone htargetEq hvalue

private theorem encodeStorageAt_writeStorageWordSlot_other
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {query : IRStorageSlot}
    {slot wordOffset targetSlot value : Nat}
    (hEq : query ≠ IRStorageSlot.ofNat targetSlot)
    (htargetEq : targetSlot % Compiler.Constants.evmModulus =
      SourceSemantics.wordNormalize (slot + wordOffset)) :
    SourceSemantics.encodeStorageAt fields
        (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
        query.toNat =
      SourceSemantics.encodeStorageAt fields runtime.world query.toNat := by
  have hneqNat := IRStorageSlot.ne_toNat_wordNormalize_of_ne_ofNat hEq
  have hneqTarget :
      query.toNat ≠ SourceSemantics.wordNormalize (slot + wordOffset) := by
    intro hq
    exact hneqNat (by simpa [htargetEq] using hq)
  have hneqWrite :
      query.toNat ≠
        (Verity.Core.Uint256.ofNat slot + Verity.Core.Uint256.ofNat wordOffset).val := by
    intro hq
    exact hneqTarget (by
      simpa [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
        uint256_add_val_eq_mod] using hq)
  exact SourceSemantics.encodeStorageAt_congr
    (fields := fields)
    (world1 := SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
    (world2 := runtime.world)
    (slot := query.toNat)
    (by simp [SourceSemantics.writeStorageWordSlots, SourceSemantics.wordNormalize,
      hneqTarget, hneqWrite])
    (by simp [SourceSemantics.writeStorageWordSlots, SourceSemantics.wordNormalize,
      hneqTarget, hneqWrite])
    (by simp [SourceSemantics.writeStorageWordSlots])

private theorem runtimeStateMatchesIR_writeStorageWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot wordOffset targetSlot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (htarget : setStorageWordTargetSafeForRuntime fields runtime targetSlot)
    (htargetEq : targetSlot % Compiler.Constants.evmModulus =
      SourceSemantics.wordNormalize (slot + wordOffset))
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = IRStorageSlot.ofNat targetSlot
  · subst hEq
    simp only [Compiler.Proofs.abstractStoreStorageOrMapping_eq, if_true]
    exact encodeStorageAt_writeStorageWordSlot_target htarget htargetEq hvalue
  · change (if query = IRStorageSlot.ofNat targetSlot then IRStorageWord.ofNat value
          else state.storage query) =
        IRStorageWord.ofNat
          (SourceSemantics.encodeStorageAt fields
            (SourceSemantics.writeStorageWordSlots runtime.world [slot] wordOffset value)
            query.toNat)
    rw [if_neg hEq]
    rw [hstorage]
    exact congrArg IRStorageWord.ofNat
      (encodeStorageAt_writeStorageWordSlot_other
        (fields := fields) (runtime := runtime) (query := query)
        (slot := slot) (wordOffset := wordOffset)
        (targetSlot := targetSlot) (value := value) hEq htargetEq).symm

private theorem execStmt_setStorageWord_singleSlot_continue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {fieldName : String}
    {value : Expr}
    {wordOffset baseSlot valueNat : Nat}
    {f : Field}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, baseSlot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [baseSlot])
    (hnotTransient : f.isTransient = false)
    (hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmt fields runtime (.setStorageWord fieldName wordOffset value) =
      .continue
        { runtime with
          world :=
            SourceSemantics.writeStorageWordSlots runtime.world [baseSlot] wordOffset valueNat } := by
  have hfieldTransient :
      SourceSemantics.fieldIsTransient fields fieldName = false := by
    simp [SourceSemantics.fieldIsTransient, hfind, hnotTransient]
  have hworld :
      SourceSemantics.writeStorageWordFieldSlots fields fieldName runtime.world
          [baseSlot] wordOffset valueNat =
        SourceSemantics.writeStorageWordSlots runtime.world [baseSlot] wordOffset valueNat := by
    simp [SourceSemantics.writeStorageWordFieldSlots, hfieldTransient]
  simp [SourceSemantics.execStmt, hwriteSlots, hValueSrc, hworld]

private theorem execIRStmts_setStorageWord_singleSlot_continue
    {state : IRState}
    {writeSlotExpr valueIR : YulExpr}
    {targetSlot valueNat extraFuel : Nat}
    (hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot)
    (hIRValue : evalIRExpr state valueIR = some valueNat) :
    execIRStmts (1 + extraFuel + 1) state
        [YulStmt.exprStmt (YulExpr.call "sstore" [writeSlotExpr, valueIR])] =
      .continue
        { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat } := by
  have hExecStmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.exprStmt (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
          .continue
            { state with
              storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat } := by
    exact execIRStmt_sstore_of_eval
      (state := state) (slotExpr := writeSlotExpr) (valueExpr := valueIR)
      (slotVal := targetSlot) (valueVal := valueNat) (fuel := extraFuel)
      hWriteSlotEval hIRValue
  have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
  simp [execIRStmts, hfuelEq, hExecStmt]

private theorem scopeNamesIncluded_setStorageWord
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {wordOffset : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.setStorageWord fieldName wordOffset value)) scope := by
  intro n hn
  simpa [stmtNextScope, collectStmtBindNames] using hn

private theorem setStorageWord_target_safety_runtime
    {fields : List Field}
    {targetSlot : Nat}
    {runtime : SourceSemantics.RuntimeState}
    (hslotSafety : setStorageWordTargetSafe fields targetSlot) :
    setStorageWordTargetSafeForRuntime fields runtime targetSlot := by
  rcases hslotSafety with hresolved | hnone
  · exact Or.inl hresolved
  · exact Or.inr ⟨hnone.1, hnone.2 runtime⟩

private theorem stmtStepMatchesIRExec_setStorageWord_singleSlot_continue
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {wordOffset baseSlot targetSlot valueNat : Nat}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hslotTarget : targetSlot =
      if wordOffset == 0 then baseSlot
      else (baseSlot + wordOffset) % Compiler.Constants.evmModulus)
    (hslotSafety :
      (∃ f,
        findResolvedFieldAtSlotCopy fields targetSlot = some f ∧
        SourceSemantics.fieldUsesAddressStorage f = false ∧
        SourceSemantics.fieldUsesDynamicArrayStorage f = false) ∨
      (findResolvedFieldAtSlotCopy fields targetSlot = none ∧
        ∀ runtime : SourceSemantics.RuntimeState,
          findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none))
    (hvalueLt : valueNat < Verity.Core.Uint256.modulus)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
      (stmtNextScope scope (.setStorageWord fieldName wordOffset value))
      runtime.bindings
      { state with storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat })
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope' : FunctionBody.scopeNamesPresent
      (stmtNextScope scope (.setStorageWord fieldName wordOffset value)) runtime.bindings) :
    stmtStepMatchesIRExec fields
      (stmtNextScope scope (.setStorageWord fieldName wordOffset value))
      (.continue
        { runtime with
          world :=
            SourceSemantics.writeStorageWordSlots runtime.world [baseSlot] wordOffset valueNat })
      (.continue
        { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat }) := by
  simp [stmtStepMatchesIRExec]
  exact ⟨by
      exact runtimeStateMatchesIR_writeStorageWordSlot
        (fields := fields) (runtime := runtime) (state := state)
        (slot := baseSlot) (wordOffset := wordOffset)
        (targetSlot := targetSlot) (value := valueNat)
        hruntime (setStorageWord_target_safety_runtime hslotSafety)
        (by simpa [hslotTarget] using
          storageWordTarget_eq_wordNormalize baseSlot wordOffset)
        hvalueLt,
    hexact', hbounded, hscope'⟩

private theorem compiledStmtStep_setStorageWord_singleSlot_preserves_of_eval
    {fields : List Field} {scope : List String} {fieldName : String}
    {value : Expr} {wordOffset : Nat} {valueIR : YulExpr} {f : Field}
    {baseSlot targetSlot valueNat : Nat}
    (hcore : FunctionBody.ExprCompileCore value) (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, baseSlot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [baseSlot])
    (hnotTransient : f.isTransient = false)
    (hslotTarget :
      targetSlot =
        if wordOffset == 0 then baseSlot
        else (baseSlot + wordOffset) % Compiler.Constants.evmModulus)
    (hslotSafety : setStorageWordTargetSafe fields targetSlot)
    {runtime : SourceSemantics.RuntimeState} {state : IRState} {extraFuel : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat)
    (hIRValue : evalIRExpr state valueIR = some valueNat)
    (hvalueLt : valueNat < Verity.Core.Uint256.modulus) :
    setStorageWordPreservesGoal fields scope fieldName value wordOffset valueIR
      baseSlot runtime state extraFuel := by
  let writeSlotExpr := setStorageWordSlotExpr baseSlot wordOffset
  have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
    simpa [writeSlotExpr, setStorageWordSlotExpr, hslotTarget] using
      (evalIRExpr_storageWordTarget_of_eval
        (state := state) (slot := baseSlot) (wordOffset := wordOffset))
  have hSrcExec := execStmt_setStorageWord_singleSlot_continue
    (wordOffset := wordOffset) hfind hwriteSlots hnotTransient hValueSrc
  have hIRExec := execIRStmts_setStorageWord_singleSlot_continue
    (state := state) (writeSlotExpr := writeSlotExpr) (valueIR := valueIR)
    (targetSlot := targetSlot) (valueNat := valueNat) (extraFuel := extraFuel)
    hWriteSlotEval hIRValue
  have hincl := scopeNamesIncluded_setStorageWord (scope := scope) (fieldName := fieldName) (value := value) (wordOffset := wordOffset) hcore hinScope
  have hexact' := FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
    (bindingsExactlyMatchIRVarsOnScope_writeStorageWordSlot
      (slot := targetSlot) (value := valueNat) hexact) hincl
  have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
  unfold setStorageWordPreservesGoal
  refine ⟨
    .continue { runtime with
      world := SourceSemantics.writeStorageWordSlots runtime.world [baseSlot] wordOffset valueNat },
    .continue { state with storage :=
      Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat },
    hSrcExec, ?_, ?_⟩
  · simpa [setStorageWordIRStmts, writeSlotExpr] using hIRExec
  · exact stmtStepMatchesIRExec_setStorageWord_singleSlot_continue
      hslotTarget hslotSafety hvalueLt hruntime hexact' hbounded hscope'

private theorem compiledStmtStep_setStorageWord_singleSlot_preserves
    {fields : List Field} {scope : List String} {fieldName : String}
    {value : Expr} {wordOffset : Nat} {valueIR : YulExpr} {f : Field}
    {baseSlot targetSlot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, baseSlot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [baseSlot])
    (hnotTransient : f.isTransient = false)
    (hslotTarget : targetSlot =
      if wordOffset == 0 then baseSlot
      else (baseSlot + wordOffset) % Compiler.Constants.evmModulus)
    (hslotSafety : setStorageWordTargetSafe fields targetSlot)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ runtime state extraFuel,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf (setStorageWordIRStmts baseSlot wordOffset valueIR) -
        (setStorageWordIRStmts baseSlot wordOffset valueIR).length ≤ extraFuel →
      setStorageWordPreservesGoal fields scope fieldName value wordOffset valueIR
        baseSlot runtime state extraFuel := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
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
    exact compiledStmtStep_setStorageWord_singleSlot_preserves_of_eval
      hcore hinScope hfind hwriteSlots hnotTransient hslotTarget hslotSafety
      hexact hscope hbounded hruntime hValueSrc hIRValue hvalueLt

theorem compiledStmtStep_setStorageWord_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {wordOffset : Nat}
    {valueIR : YulExpr}
    {f : Field}
    {slot targetSlot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (halias : f.aliasSlots = [])
    (_hunpacked : f.packedBits = none)
    (hnotTransient : f.isTransient = false)
    (hslotTarget :
      targetSlot =
        if wordOffset == 0 then slot
        else (slot + wordOffset) % Compiler.Constants.evmModulus)
    (hslotSafety :
      (∃ targetField, findResolvedFieldAtSlotCopy fields targetSlot = some targetField ∧
        SourceSemantics.fieldUsesAddressStorage targetField = false ∧
        SourceSemantics.fieldUsesDynamicArrayStorage targetField = false) ∨
      (findResolvedFieldAtSlotCopy fields targetSlot = none ∧
        ∀ runtime : SourceSemantics.RuntimeState,
          findDynamicArrayElementAtSlotCopy fields runtime.world targetSlot = none))
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorageWord fieldName wordOffset value)
      [YulStmt.exprStmt
        (YulExpr.call "sstore"
          [if wordOffset == 0 then YulExpr.lit slot
           else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset],
           valueIR])] where
  compileOk := by
    have hvalueIRInternal := compileExprWithInternals_nil_ok hvalueIR
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      hfind, halias, hnotTransient, hvalueIRInternal]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    exact
      (compiledStmtStep_setStorageWord_singleSlot_preserves
        (fields := fields) (scope := scope) (fieldName := fieldName)
        (value := value) (wordOffset := wordOffset) (valueIR := valueIR)
        (f := f) (baseSlot := slot) (targetSlot := targetSlot)
        hcore hinScope
        hfind hwriteSlots hnotTransient hslotTarget hslotSafety hvalueIR
        runtime state extraFuel hexact hscope hbounded hruntime hslack)

end Compiler.Proofs.IRGeneration
