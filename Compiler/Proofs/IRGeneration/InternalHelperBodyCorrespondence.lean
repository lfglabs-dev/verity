import Compiler.Proofs.IRGeneration.GenericInduction.Helpers

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

def internalHelperBodyScope (callee : FunctionSpec) (helper : IRInternalFunctionDef) :
    List String :=
  CompilationModel.internalFunctionYulParamNames callee.params ++ helper.rets

def internalHelperBodyRuntime
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat)) :
    SourceSemantics.RuntimeState :=
  { world := initialWorld, bindings := bindings }

def internalHelperBodySourceResult
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (helperFuel : Nat) : SourceSemantics.StmtResult :=
  SourceSemantics.execStmtListWithHelpers spec (SourceSemantics.effectiveFields spec)
    helperFuel (internalHelperBodyRuntime initialWorld bindings) callee.body

noncomputable def internalHelperBodyIRExec
    (runtimeContract : IRContract) (helper : IRInternalFunctionDef)
    (callerState : IRState) (args : List Nat) (extraFuel : Nat) :
    IRExecResultWithInternals :=
  execIRStmtsWithInternals runtimeContract (sizeOf helper.body + extraFuel + 1)
    (prepareInternalCalleeState callerState helper args) helper.body

def internalHelperResultOfStmtResult
    (initialWorld : Verity.ContractState) : SourceSemantics.StmtResult →
    SourceSemantics.InternalFunctionResult
  | .continue finalState => SourceSemantics.successInternalResult finalState.world none
  | .stop finalState => SourceSemantics.successInternalResult finalState.world none
  | .return value finalState => SourceSemantics.successInternalResult finalState.world (some value)
  | .revert => SourceSemantics.revertedInternalResult initialWorld

/-- Helper-entry source bindings: the raw source argument bindings extended with
zero-initialized compiled helper return slots. -/
def internalHelperEntryBindings
    (sourceBindings : List (String × Nat)) (helper : IRInternalFunctionDef) :
    List (String × Nat) :=
  helper.rets.foldl (fun acc name => SourceSemantics.bindValue acc name 0) sourceBindings

/-- Extensional source-binding agreement away from a reserved name set.  This is
the right notion for source-execution irrelevance: `bindValue` does not preserve
list order, while source reads go through `lookupValue`/`lookupBinding?`. -/
private def sourceBindingsAgreeOutside
    (reserved : List String) (lhs rhs : List (String × Nat)) : Prop :=
  ∀ name, name ∉ reserved →
    SourceSemantics.lookupValue lhs name = SourceSemantics.lookupValue rhs name ∧
      SourceSemantics.lookupBinding? lhs name = SourceSemantics.lookupBinding? rhs name

private theorem SourceSemantics.lookupBinding?_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    SourceSemantics.lookupBinding?
      (SourceSemantics.bindValue bindings boundName value)
      queryName =
    SourceSemantics.lookupBinding? bindings queryName := by
  simpa [FunctionBody.lookupBinding?, SourceSemantics.lookupBinding?] using
    (FunctionBody.lookupBinding?_bindValue_ne bindings boundName queryName value hNe)

private theorem sourceBindingsAgreeOutside_refl
    (reserved : List String) (bindings : List (String × Nat)) :
    sourceBindingsAgreeOutside reserved bindings bindings := by
  intro name _hname
  exact ⟨rfl, rfl⟩

private theorem sourceBindingsAgreeOutside_mono
    {reserved₁ reserved₂ : List String} {lhs rhs : List (String × Nat)}
    (hagree : sourceBindingsAgreeOutside reserved₁ lhs rhs)
    (hsubset : ∀ name, name ∉ reserved₂ → name ∉ reserved₁) :
    sourceBindingsAgreeOutside reserved₂ lhs rhs := by
  intro name hname
  exact hagree name (hsubset name hname)

private theorem sourceBindingsAgreeOutside_trans
    {reserved : List String} {lhs mid rhs : List (String × Nat)}
    (hleft : sourceBindingsAgreeOutside reserved lhs mid)
    (hright : sourceBindingsAgreeOutside reserved mid rhs) :
    sourceBindingsAgreeOutside reserved lhs rhs := by
  intro name hname
  rcases hleft name hname with ⟨hvalueLeft, hbindingLeft⟩
  rcases hright name hname with ⟨hvalueRight, hbindingRight⟩
  exact ⟨hvalueLeft.trans hvalueRight, hbindingLeft.trans hbindingRight⟩

private theorem sourceBindingsAgreeOutside_bindValue
    {reserved : List String} {lhs rhs : List (String × Nat)}
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (name : String) (value : Nat) :
    sourceBindingsAgreeOutside reserved
      (SourceSemantics.bindValue lhs name value)
      (SourceSemantics.bindValue rhs name value) := by
  intro query hquery
  by_cases hsame : query = name
  · subst hsame
    simp
  · have hleft :=
      FunctionBody.lookupValue_bindValue_ne lhs name query value hsame
    have hright :=
      FunctionBody.lookupValue_bindValue_ne rhs name query value hsame
    have hleft? :=
      SourceSemantics.lookupBinding?_bindValue_ne lhs name query value hsame
    have hright? :=
      SourceSemantics.lookupBinding?_bindValue_ne rhs name query value hsame
    rcases hagree query hquery with ⟨hvalue, hbinding⟩
    exact ⟨by rw [hleft, hright, hvalue], by rw [hleft?, hright?, hbinding]⟩

private theorem sourceBindingsAgreeOutside_bindValue_left_reserved
    {reserved : List String} {lhs rhs : List (String × Nat)}
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    {name : String} (hname : name ∈ reserved) (value : Nat) :
    sourceBindingsAgreeOutside reserved
      (SourceSemantics.bindValue lhs name value) rhs := by
  intro query hquery
  have hne : query ≠ name := by
    intro hsame
    subst hsame
    exact hquery hname
  have hleft :=
    FunctionBody.lookupValue_bindValue_ne lhs name query value hne
  have hleft? :=
    SourceSemantics.lookupBinding?_bindValue_ne lhs name query value hne
  rcases hagree query hquery with ⟨hvalue, hbinding⟩
  exact ⟨by rw [hleft, hvalue], by rw [hleft?, hbinding]⟩

private theorem sourceBindingsAgreeOutside_internalHelperEntryBindings
    (sourceBindings : List (String × Nat)) (helper : IRInternalFunctionDef) :
    sourceBindingsAgreeOutside helper.rets
      (internalHelperEntryBindings sourceBindings helper) sourceBindings := by
  unfold internalHelperEntryBindings
  induction helper.rets generalizing sourceBindings with
  | nil =>
      exact sourceBindingsAgreeOutside_refl [] sourceBindings
  | cons ret rest ih =>
      simp only [List.foldl_cons]
      have htail : sourceBindingsAgreeOutside (ret :: rest)
          (rest.foldl (fun acc name => SourceSemantics.bindValue acc name 0)
            (SourceSemantics.bindValue sourceBindings ret 0))
          (SourceSemantics.bindValue sourceBindings ret 0) := by
        refine sourceBindingsAgreeOutside_mono
          (ih (SourceSemantics.bindValue sourceBindings ret 0)) ?_
        intro query hquery hmem
        exact hquery (by simp [hmem])
      have hhead : sourceBindingsAgreeOutside (ret :: rest)
          (SourceSemantics.bindValue sourceBindings ret 0) sourceBindings :=
        sourceBindingsAgreeOutside_bindValue_left_reserved
          (sourceBindingsAgreeOutside_refl (ret :: rest) sourceBindings)
          (by simp) 0
      exact sourceBindingsAgreeOutside_trans htail hhead

theorem lookupValue_internalHelperEntryBindings_of_not_mem
    (sourceBindings : List (String × Nat)) (helper : IRInternalFunctionDef)
    {name : String} (hname : name ∉ helper.rets) :
    SourceSemantics.lookupValue
      (internalHelperEntryBindings sourceBindings helper) name =
    SourceSemantics.lookupValue sourceBindings name :=
  (sourceBindingsAgreeOutside_internalHelperEntryBindings sourceBindings helper
    name hname).1

theorem lookupBinding?_internalHelperEntryBindings_of_not_mem
    (sourceBindings : List (String × Nat)) (helper : IRInternalFunctionDef)
    {name : String} (hname : name ∉ helper.rets) :
    SourceSemantics.lookupBinding?
      (internalHelperEntryBindings sourceBindings helper) name =
    SourceSemantics.lookupBinding? sourceBindings name :=
  (sourceBindingsAgreeOutside_internalHelperEntryBindings sourceBindings helper
    name hname).2

/-- Internal-helper return slot bindings are invisible to every explicitly named
source read outside the helper return-name set.  This is intentionally a lookup
lemma rather than a statement-result equality: `StmtResult` stores final
bindings, so adding an unread return-slot binding can still change the raw
result state. -/
theorem internalHelperEntryBindings_source_reads_irrelevant
    (sourceBindings : List (String × Nat)) (helper : IRInternalFunctionDef)
    (readNames : List String)
    (hfresh : ∀ name, name ∈ readNames → name ∉ helper.rets) :
    (∀ name ∈ readNames,
        SourceSemantics.lookupValue
          (internalHelperEntryBindings sourceBindings helper) name =
        SourceSemantics.lookupValue sourceBindings name) ∧
      (∀ name ∈ readNames,
        SourceSemantics.lookupBinding?
          (internalHelperEntryBindings sourceBindings helper) name =
        SourceSemantics.lookupBinding? sourceBindings name) := by
  constructor
  · intro name hmem
    exact lookupValue_internalHelperEntryBindings_of_not_mem
      sourceBindings helper (hfresh name hmem)
  · intro name hmem
    exact lookupBinding?_internalHelperEntryBindings_of_not_mem
      sourceBindings helper (hfresh name hmem)

/-- Assumptions needed to apply the generic helper-body theorem at an internal
helper entry.  `bodyBindings` is the remaining ret-slot/source-binding seam:
the generic theorem needs bindings for compiled return slots, while
`interpretInternalFunctionFuel` starts from raw `bindInternalArgs` bindings. -/
structure InternalHelperBodyExecContext
    (runtimeContract : IRContract) (spec : CompilationModel)
    (callee : FunctionSpec) (helper : IRInternalFunctionDef)
    (callerState : IRState) (initialWorld : Verity.ContractState)
    (args : List Nat) (sourceBindings entryBindings : List (String × Nat))
    (helperFuel : Nat) : Prop where
  bindArgs : SourceSemantics.bindInternalArgs callee.params args = some sourceBindings
  helperParams : helper.params = CompilationModel.internalFunctionYulParamNames callee.params
  generic : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
    (SourceSemantics.effectiveFields spec) (internalHelperBodyScope callee helper) callee.body
  bodyCompile : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
    [] [] .calldata [] false (internalHelperBodyScope callee helper)
    [] callee.body spec.functions = Except.ok helper.body
  bodyBindings : internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel =
    internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel
  scope : FunctionBody.scopeNamesPresent (internalHelperBodyScope callee helper) entryBindings
  exact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
    (internalHelperBodyScope callee helper) entryBindings
    (prepareInternalCalleeState callerState helper args)
  bounded : FunctionBody.bindingsBounded entryBindings
  noEvents : spec.events = []
  noErrors : spec.errors = []
  runtime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields spec)
    (internalHelperBodyRuntime initialWorld entryBindings)
    (prepareInternalCalleeState callerState helper args)

/-- Helper-entry/body correspondence for the N1a internal-helper path. -/
theorem internal_helper_body_exec_matches_of_bindInternalArgs_and_generic
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {args : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel) :
    stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) ∧
      SourceSemantics.interpretInternalFunctionFuel spec helperFuel callee initialWorld args =
        internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel) := by
  have hgeneric' : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
      (SourceSemantics.effectiveFields spec) (helper.params ++ helper.rets) callee.body := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.generic
  have hbodyCompile' : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
      [] [] .calldata [] false (helper.params ++ helper.rets)
      [] callee.body spec.functions = Except.ok helper.body := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.bodyCompile
  have hscope' : FunctionBody.scopeNamesPresent (helper.params ++ helper.rets) entryBindings := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.scope
  have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
      (helper.params ++ helper.rets) entryBindings
      (prepareInternalCalleeState callerState helper args) := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.exact
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel
      (runtime := internalHelperBodyRuntime initialWorld entryBindings)
      (state := prepareInternalCalleeState callerState helper args)
      (scope := helper.params ++ helper.rets) (stmts := callee.body)
      (helperFuel := helperFuel) (extraFuel := extraFuel)
      hfuelPos hgeneric' hscope' hexact' ctx.bounded ctx.noEvents ctx.noErrors ctx.runtime with
    ⟨bodyIR, hcompile, hmatch⟩
  have hbodyEq : bodyIR = helper.body := by
    rw [hbodyCompile'] at hcompile
    injection hcompile with hbodyEq
    exact hbodyEq.symm
  subst bodyIR
  refine ⟨?_, ?_⟩
  · have hmatch' : stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) := by
      simpa [internalHelperBodySourceResult, internalHelperBodyIRExec] using hmatch
    rw [ctx.bodyBindings] at hmatch'
    exact hmatch'
  · simp [internalHelperBodySourceResult, internalHelperResultOfStmtResult,
      SourceSemantics.interpretInternalFunctionFuel, ctx.bindArgs]
    rfl

end Compiler.Proofs.IRGeneration
