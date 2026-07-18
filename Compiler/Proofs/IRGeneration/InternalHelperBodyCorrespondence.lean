import Compiler.Proofs.IRGeneration.GenericInduction.Helpers
import Compiler.Proofs.IRGeneration.HelperBodyBridge

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

def internalHelperBodyScope (callee : FunctionSpec) (helper : IRInternalFunctionDef) :
    List String :=
  CompilationModel.internalFunctionYulParamNames callee.params ++ helper.rets

def internalHelperBodyRuntime
    (initialWorld : Verity.ContractState) (selector : Nat) (bindings : List (String × Nat)) :
    SourceSemantics.RuntimeState :=
  { world := initialWorld, selector := selector, bindings := bindings }

def internalHelperBodySourceResult
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat) (bindings : List (String × Nat))
    (helperFuel : Nat) : SourceSemantics.StmtResult :=
  SourceSemantics.execStmtListWithHelpers spec (SourceSemantics.effectiveFields spec)
    helperFuel (internalHelperBodyRuntime initialWorld selector bindings) callee.body

noncomputable def internalHelperBodyIRExec
    (runtimeContract : IRContract) (helper : IRInternalFunctionDef)
    (callerState : IRState) (irArgs : List Nat) (extraFuel : Nat) :
    IRExecResultWithInternals :=
  execIRStmtsWithInternals runtimeContract (sizeOf helper.body + extraFuel + 1)
    (prepareInternalCalleeState callerState helper irArgs) helper.body

def internalHelperResultOfStmtResult
    (initialWorld : Verity.ContractState) : SourceSemantics.StmtResult →
    SourceSemantics.InternalFunctionResult
  | .continue finalState => SourceSemantics.successInternalResult finalState.world none
  | .stop finalState => SourceSemantics.successInternalResult finalState.world none
  | .return value finalState => SourceSemantics.successInternalResult finalState.world (some value)
  | .revert => SourceSemantics.revertedInternalResult initialWorld

theorem interpretInternalFunctionFuel_eq_internalHelperResultOfStmtResult_of_bindInternalArgs
    {spec : CompilationModel} {callee : FunctionSpec}
    {initialWorld : Verity.ContractState} {args : List Nat}
    {sourceBindings : List (String × Nat)}
    (helperFuel : Nat)
    (hbind : SourceSemantics.bindInternalArgs callee.params args = some sourceBindings) :
    SourceSemantics.interpretInternalFunctionFuel spec helperFuel callee initialWorld args =
      internalHelperResultOfStmtResult initialWorld
        (internalHelperBodySourceResult spec callee initialWorld 0 sourceBindings helperFuel) := by
  simp [SourceSemantics.interpretInternalFunctionFuel, internalHelperBodySourceResult,
    internalHelperBodyRuntime, internalHelperResultOfStmtResult, hbind]
  rfl

/-- Projection-level helper body agreement.  This is the payload consumed by
`InternalHelperSummaryContract`: success flag, optional return value, and final
world.  It deliberately ignores final source bindings, which may differ when
compiled helper return slots were prebound at helper entry. -/
def internalHelperBodyResultProjection
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat)
    (sourceBindings entryBindings : List (String × Nat))
    (helperFuel : Nat) : Prop :=
  internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld selector sourceBindings helperFuel) =
    internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld selector entryBindings helperFuel)

theorem internalHelperBodyResultProjection_of_stmtResult_eq
    {spec : CompilationModel} {callee : FunctionSpec}
    {initialWorld : Verity.ContractState} {selector : Nat}
    {sourceBindings entryBindings : List (String × Nat)}
    {helperFuel : Nat}
    (hbody :
      internalHelperBodySourceResult spec callee initialWorld selector entryBindings helperFuel =
        internalHelperBodySourceResult spec callee initialWorld selector sourceBindings helperFuel) :
    internalHelperBodyResultProjection spec callee initialWorld selector
      sourceBindings entryBindings helperFuel := by
  simp [internalHelperBodyResultProjection, hbody]

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
/-- The selector-aware counterpart of `interpretInternalFunctionFuel` used at an
internal helper entry.  The source interpreter's public helper entry point uses
its default selector; an IR helper instead inherits the caller selector. -/
def internalHelperBodyInterpretation
    (spec : CompilationModel) (helperFuel : Nat) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat) (logicalArgs : List Nat) :
    SourceSemantics.InternalFunctionResult :=
  match SourceSemantics.bindInternalArgs callee.params logicalArgs with
  | none => SourceSemantics.revertedInternalResult initialWorld
  | some bindings => internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld selector bindings helperFuel)

/-- Binding names read by the source statement cases covered by
`InternalHelperStmtListProjectionCore`.  Other statements return `[]` here and
are excluded by that fragment predicate. -/
def internalHelperStmtProjectionReadNames : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .require value _
  | .return value => FunctionBody.exprBoundNames value
  | _ => []

def internalHelperStmtListProjectionReadNames : List Stmt → List String
  | [] => []
  | .return value :: _ => FunctionBody.exprBoundNames value
  | .stop :: _ => []
  | stmt :: rest =>
      internalHelperStmtProjectionReadNames stmt ++
        internalHelperStmtListProjectionReadNames rest

inductive InternalHelperExprProjectionCore : Expr → Prop where
  | literal (value : Nat) : InternalHelperExprProjectionCore (.literal value)
  | param (name : String) : InternalHelperExprProjectionCore (.param name)
  | localVar (name : String) : InternalHelperExprProjectionCore (.localVar name)

inductive InternalHelperExprListProjectionCore : List Expr → Prop where
  | nil : InternalHelperExprListProjectionCore []
  | cons {expr : Expr} {rest : List Expr} :
      InternalHelperExprProjectionCore expr →
      InternalHelperExprListProjectionCore rest →
      InternalHelperExprListProjectionCore (expr :: rest)

inductive InternalHelperStmtListProjectionCore : List Stmt → Prop where
  | nil : InternalHelperStmtListProjectionCore []
  | letVar {name : String} {value : Expr} {rest : List Stmt} :
      InternalHelperExprProjectionCore value →
      InternalHelperStmtListProjectionCore rest →
      InternalHelperStmtListProjectionCore (.letVar name value :: rest)
  | assignVar {name : String} {value : Expr} {rest : List Stmt} :
      InternalHelperExprProjectionCore value →
      InternalHelperStmtListProjectionCore rest →
      InternalHelperStmtListProjectionCore (.assignVar name value :: rest)
  | require_ {cond : Expr} {msg : String} {rest : List Stmt} :
      InternalHelperExprProjectionCore cond →
      InternalHelperStmtListProjectionCore rest →
      InternalHelperStmtListProjectionCore (.require cond msg :: rest)
  | return_ {value : Expr} {rest : List Stmt} :
      InternalHelperExprProjectionCore value →
      InternalHelperStmtListProjectionCore (.return value :: rest)
  | stop {rest : List Stmt} :
      InternalHelperStmtListProjectionCore (.stop :: rest)

private theorem sourceBindingsAgreeOutside_symm
    {reserved : List String} {lhs rhs : List (String × Nat)}
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs) :
    sourceBindingsAgreeOutside reserved rhs lhs := by
  intro name hname
  rcases hagree name hname with ⟨hvalue, hbinding⟩
  exact ⟨hvalue.symm, hbinding.symm⟩

theorem evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)} {expr : Expr}
    (hcore : InternalHelperExprProjectionCore expr)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh : ∀ name, name ∈ FunctionBody.exprBoundNames expr → name ∉ reserved) :
    SourceSemantics.evalExprWithHelpers spec fields fuel { runtime with bindings := lhs } expr =
      SourceSemantics.evalExprWithHelpers spec fields fuel { runtime with bindings := rhs } expr := by
  cases hcore with
  | literal value => simp [SourceSemantics.evalExprWithHelpers]
  | param name | localVar name =>
      have hlookup := (hagree name (hfresh name (by simp [FunctionBody.exprBoundNames]))).1
      simp [SourceSemantics.evalExprWithHelpers, hlookup]

theorem evalExprListWithHelpers_eq_of_internalHelperExprListProjectionCore
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)} {exprs : List Expr}
    (hcore : InternalHelperExprListProjectionCore exprs)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh : ∀ name, name ∈ FunctionBody.exprListBoundNames exprs → name ∉ reserved) :
    SourceSemantics.evalExprListWithHelpers spec fields fuel
        { runtime with bindings := lhs } exprs =
      SourceSemantics.evalExprListWithHelpers spec fields fuel
        { runtime with bindings := rhs } exprs := by
  induction hcore with
  | nil => simp [SourceSemantics.evalExprListWithHelpers]
  | cons hhead _ hrest =>
      have hheadEq := evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
        (spec := spec) (fields := fields) (fuel := fuel) (runtime := runtime)
        hhead hagree
        (by intro name hmem; exact hfresh name (by simp [FunctionBody.exprListBoundNames, hmem]))
      have hrestEq := hrest
        (by intro name hmem; exact hfresh name (by simp [FunctionBody.exprListBoundNames, hmem]))
      simp [SourceSemantics.evalExprListWithHelpers, hheadEq, hrestEq]

private theorem internalHelperResultOfStmtListProjectionCore_eq_return
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {initialWorld : Verity.ContractState} {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)}
    {value : Expr} {rest : List Stmt}
    (hvalue : InternalHelperExprProjectionCore value)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh :
      ∀ name, name ∈ internalHelperStmtListProjectionReadNames (.return value :: rest) →
        name ∉ reserved) :
    internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := lhs } (.return value :: rest)) =
      internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := rhs } (.return value :: rest)) := by
  have hvalueEq := evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
    (spec := spec) (fields := fields) (fuel := fuel) (runtime := runtime)
    hvalue hagree
    (by
      intro name hmem
      exact hfresh name (by
        simp [internalHelperStmtListProjectionReadNames,
          internalHelperStmtProjectionReadNames, hmem]))
  cases hleft :
      SourceSemantics.evalExprWithHelpers spec fields fuel
        { runtime with bindings := lhs } value with
  | none =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = none := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult, hleft, hright]
  | some resolved =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = some resolved := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult, hleft, hright]

private theorem internalHelperStmtListProjectionReadNames_fresh_tail_letVar
    {name : String} {value : Expr} {rest : List Stmt} {reserved : List String}
    (hfresh : ∀ query,
      query ∈ internalHelperStmtListProjectionReadNames (.letVar name value :: rest) →
        query ∉ reserved) :
    ∀ query, query ∈ internalHelperStmtListProjectionReadNames rest → query ∉ reserved := by
  intro query hmem
  exact hfresh query (by
    simp [internalHelperStmtListProjectionReadNames,
      internalHelperStmtProjectionReadNames, hmem])

private theorem internalHelperStmtListProjectionReadNames_fresh_tail_assignVar
    {name : String} {value : Expr} {rest : List Stmt} {reserved : List String}
    (hfresh : ∀ query,
      query ∈ internalHelperStmtListProjectionReadNames (.assignVar name value :: rest) →
        query ∉ reserved) :
    ∀ query, query ∈ internalHelperStmtListProjectionReadNames rest → query ∉ reserved := by
  intro query hmem
  exact hfresh query (by
    simp [internalHelperStmtListProjectionReadNames,
      internalHelperStmtProjectionReadNames, hmem])

private theorem internalHelperStmtListProjectionReadNames_fresh_tail_require
    {cond : Expr} {msg : String} {rest : List Stmt} {reserved : List String}
    (hfresh : ∀ query,
      query ∈ internalHelperStmtListProjectionReadNames (.require cond msg :: rest) →
        query ∉ reserved) :
    ∀ query, query ∈ internalHelperStmtListProjectionReadNames rest → query ∉ reserved := by
  intro query hmem
  exact hfresh query (by
    simp [internalHelperStmtListProjectionReadNames,
      internalHelperStmtProjectionReadNames, hmem])

private theorem internalHelperResultOfStmtListProjectionCore_eq_letVar
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {initialWorld : Verity.ContractState} {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)}
    {name : String} {value : Expr} {rest : List Stmt}
    (hvalue : InternalHelperExprProjectionCore value)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh :
      ∀ query, query ∈ internalHelperStmtListProjectionReadNames (.letVar name value :: rest) →
        query ∉ reserved)
    (hrestEq : ∀ resolved,
      internalHelperResultOfStmtResult initialWorld
          (SourceSemantics.execStmtListWithHelpers spec fields fuel
            { runtime with bindings := SourceSemantics.bindValue lhs name resolved } rest) =
        internalHelperResultOfStmtResult initialWorld
          (SourceSemantics.execStmtListWithHelpers spec fields fuel
            { runtime with bindings := SourceSemantics.bindValue rhs name resolved } rest)) :
    internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := lhs } (.letVar name value :: rest)) =
      internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := rhs } (.letVar name value :: rest)) := by
  have hvalueEq := evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
    (spec := spec) (fields := fields) (fuel := fuel) (runtime := runtime)
    hvalue hagree
    (by
      intro query hmem
      exact hfresh query (by
        simp [internalHelperStmtListProjectionReadNames,
          internalHelperStmtProjectionReadNames, hmem]))
  cases hleft :
      SourceSemantics.evalExprWithHelpers spec fields fuel
        { runtime with bindings := lhs } value with
  | none =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = none := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult, hleft, hright]
  | some resolved =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = some resolved := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        hleft, hright, hrestEq resolved]

private theorem internalHelperResultOfStmtListProjectionCore_eq_assignVar
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {initialWorld : Verity.ContractState} {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)}
    {name : String} {value : Expr} {rest : List Stmt}
    (hvalue : InternalHelperExprProjectionCore value)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh :
      ∀ query, query ∈ internalHelperStmtListProjectionReadNames (.assignVar name value :: rest) →
        query ∉ reserved)
    (hrestEq : ∀ resolved,
      internalHelperResultOfStmtResult initialWorld
          (SourceSemantics.execStmtListWithHelpers spec fields fuel
            { runtime with bindings := SourceSemantics.bindValue lhs name resolved } rest) =
        internalHelperResultOfStmtResult initialWorld
          (SourceSemantics.execStmtListWithHelpers spec fields fuel
            { runtime with bindings := SourceSemantics.bindValue rhs name resolved } rest)) :
    internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := lhs } (.assignVar name value :: rest)) =
      internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := rhs } (.assignVar name value :: rest)) := by
  have hvalueEq := evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
    (spec := spec) (fields := fields) (fuel := fuel) (runtime := runtime)
    hvalue hagree
    (by
      intro query hmem
      exact hfresh query (by
        simp [internalHelperStmtListProjectionReadNames,
          internalHelperStmtProjectionReadNames, hmem]))
  cases hleft :
      SourceSemantics.evalExprWithHelpers spec fields fuel
        { runtime with bindings := lhs } value with
  | none =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = none := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult, hleft, hright]
  | some resolved =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } value = some resolved := by
        simpa [hleft] using hvalueEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        hleft, hright, hrestEq resolved]

private theorem internalHelperResultOfStmtListProjectionCore_eq_require
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {initialWorld : Verity.ContractState} {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)}
    {cond : Expr} {msg : String} {rest : List Stmt}
    (hcond : InternalHelperExprProjectionCore cond)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh : ∀ query,
      query ∈ internalHelperStmtListProjectionReadNames (.require cond msg :: rest) →
      query ∉ reserved)
    (hrestEq :
      internalHelperResultOfStmtResult initialWorld (SourceSemantics.execStmtListWithHelpers
        spec fields fuel { runtime with bindings := lhs } rest) =
      internalHelperResultOfStmtResult initialWorld (SourceSemantics.execStmtListWithHelpers
        spec fields fuel { runtime with bindings := rhs } rest)) :
    internalHelperResultOfStmtResult initialWorld (SourceSemantics.execStmtListWithHelpers
        spec fields fuel { runtime with bindings := lhs } (.require cond msg :: rest)) =
      internalHelperResultOfStmtResult initialWorld (SourceSemantics.execStmtListWithHelpers
        spec fields fuel { runtime with bindings := rhs } (.require cond msg :: rest)) := by
  have hcondEq := evalExprWithHelpers_eq_of_internalHelperExprProjectionCore
    (spec := spec) (fields := fields) (fuel := fuel) (runtime := runtime)
    hcond hagree
    (by
      intro query hmem
      exact hfresh query (by simp [internalHelperStmtListProjectionReadNames,
        internalHelperStmtProjectionReadNames, hmem]))
  cases hleft : SourceSemantics.evalExprWithHelpers spec fields fuel
      { runtime with bindings := lhs } cond with
  | none =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } cond = none := by
        simpa [hleft] using hcondEq.symm
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult, hleft, hright]
  | some resolved =>
      have hright :
          SourceSemantics.evalExprWithHelpers spec fields fuel
            { runtime with bindings := rhs } cond = some resolved := by
        simpa [hleft] using hcondEq.symm
      by_cases hnonzero : resolved != 0
      · simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
          hleft, hright, hnonzero, hrestEq]
      · simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
          internalHelperResultOfStmtResult, hleft, hright, hnonzero]

private theorem internalHelperResultOfStmtListProjectionCore_eq
    {spec : CompilationModel} {fields : List Field} {fuel : Nat}
    {initialWorld : Verity.ContractState} {runtime : SourceSemantics.RuntimeState}
    {reserved : List String} {lhs rhs : List (String × Nat)}
    {stmts : List Stmt}
    (hcore : InternalHelperStmtListProjectionCore stmts)
    (hagree : sourceBindingsAgreeOutside reserved lhs rhs)
    (hfresh :
      ∀ name, name ∈ internalHelperStmtListProjectionReadNames stmts → name ∉ reserved) :
    internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := lhs } stmts) =
      internalHelperResultOfStmtResult initialWorld
        (SourceSemantics.execStmtListWithHelpers spec fields fuel
          { runtime with bindings := rhs } stmts) := by
  induction hcore generalizing runtime lhs rhs with
  | nil =>
      simp [SourceSemantics.execStmtListWithHelpers, internalHelperResultOfStmtResult]
  | letVar hvalue _ ih =>
      refine internalHelperResultOfStmtListProjectionCore_eq_letVar
        hvalue hagree hfresh ?_
      intro resolved
      exact ih
        (sourceBindingsAgreeOutside_bindValue hagree _ resolved)
        (internalHelperStmtListProjectionReadNames_fresh_tail_letVar hfresh)
  | assignVar hvalue _ ih =>
      refine internalHelperResultOfStmtListProjectionCore_eq_assignVar
        hvalue hagree hfresh ?_
      intro resolved
      exact ih
        (sourceBindingsAgreeOutside_bindValue hagree _ resolved)
        (internalHelperStmtListProjectionReadNames_fresh_tail_assignVar hfresh)
  | require_ hcond _ ih =>
      refine internalHelperResultOfStmtListProjectionCore_eq_require
        hcond hagree hfresh ?_
      exact ih hagree (internalHelperStmtListProjectionReadNames_fresh_tail_require hfresh)
  | return_ hvalue =>
      exact internalHelperResultOfStmtListProjectionCore_eq_return hvalue hagree hfresh
  | stop =>
      simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
        internalHelperResultOfStmtResult]

/-- Source-semantics discharge for the helper-entry binding projection seam over
the current projection-core fragment: empty bodies, `stop`, `return`, and
sequencing through `letVar`, `assignVar`, and `require` with literal,
parameter, or local-variable expressions.  Branches, loops, events, storage
effects, and helper calls remain for the larger helper-aware source induction. -/
theorem internalHelperBodyResultProjection_of_entryBindings_projectionCore
    {spec : CompilationModel} {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {initialWorld : Verity.ContractState} {selector : Nat}
    {sourceBindings : List (String × Nat)}
    {helperFuel : Nat}
    (hcore : InternalHelperStmtListProjectionCore callee.body)
    (hfresh :
      ∀ name, name ∈ internalHelperStmtListProjectionReadNames callee.body →
        name ∉ helper.rets) :
    internalHelperBodyResultProjection spec callee initialWorld selector sourceBindings
      (internalHelperEntryBindings sourceBindings helper) helperFuel := by
  exact internalHelperResultOfStmtListProjectionCore_eq
    (spec := spec) (fields := SourceSemantics.effectiveFields spec)
    (fuel := helperFuel) (initialWorld := initialWorld)
    (runtime := internalHelperBodyRuntime initialWorld selector sourceBindings)
    (reserved := helper.rets)
    (lhs := sourceBindings)
    (rhs := internalHelperEntryBindings sourceBindings helper)
    hcore
    (sourceBindingsAgreeOutside_symm
      (sourceBindingsAgreeOutside_internalHelperEntryBindings sourceBindings helper))
    hfresh

/-- Assumptions needed to apply the generic helper-body theorem at an internal
helper entry. The generic theorem compiles an external-mode body, so this bridge
is limited to return-family-free bodies. `bodyResultProjection` relates the
helper-summary payload without asserting false equality of final bindings. -/
structure InternalHelperBodyExecContext
    (runtimeContract : IRContract) (spec : CompilationModel)
    (callee : FunctionSpec) (helper : IRInternalFunctionDef)
    (callerState : IRState) (initialWorld : Verity.ContractState)
    (logicalArgs irArgs : List Nat) (sourceBindings entryBindings : List (String × Nat))
    (helperFuel : Nat) : Prop where
  /-- Source arguments have one value per source parameter, whereas `irArgs`
  has one value per lowered Yul parameter. -/
  bindArgs : SourceSemantics.bindInternalArgs callee.params logicalArgs = some sourceBindings
  helperParams : helper.params = CompilationModel.internalFunctionYulParamNames callee.params
  generic : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
    (SourceSemantics.effectiveFields spec) (internalHelperBodyScope callee helper) callee.body
  bodyCompile : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
    spec.events spec.errors .calldata helper.rets true (internalHelperBodyScope callee helper)
    [] callee.body spec.functions = Except.ok helper.body
  returnFree : stmtListUsesReturnFamily callee.body = false
  /-- This bridge returns an internal-function result, so bodies that can
   propagate `.stop` to the IR caller are excluded at this boundary. -/
  noStop : stmtListUsesStop callee.body = false
  bodyResultProjection : internalHelperBodyResultProjection spec callee initialWorld
    callerState.selector sourceBindings entryBindings helperFuel
  scope : FunctionBody.scopeNamesPresent (internalHelperBodyScope callee helper) entryBindings
  exact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
    (internalHelperBodyScope callee helper) entryBindings
    (prepareInternalCalleeState callerState helper irArgs)
  bounded : FunctionBody.bindingsBounded entryBindings
  runtime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields spec)
    (internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
    (prepareInternalCalleeState callerState helper irArgs)

/-- Helper-entry/body correspondence for the N1a internal-helper path.

The compiled helper body is matched against source execution from
`entryBindings`, which include prebound helper return slots.  The source helper
summary payload is related by the explicit projection seam, so callers need not
prove false raw equality of final `StmtResult` bindings. -/
theorem internal_helper_body_exec_matches_entryBindings_and_projected_result_of_bindInternalArgs_and_generic
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {logicalArgs irArgs : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld logicalArgs irArgs sourceBindings entryBindings helperFuel) :
    stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld callerState.selector entryBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState irArgs extraFuel) ∧
      internalHelperBodyInterpretation spec helperFuel callee initialWorld callerState.selector logicalArgs =
        internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld callerState.selector entryBindings helperFuel) := by
  refine ⟨?_, ?_⟩
  · rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel_step
        (runtimeContract := runtimeContract) (spec := spec)
        (fields := SourceSemantics.effectiveFields spec)
        (runtime := internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
        (state := prepareInternalCalleeState callerState helper irArgs)
        (scope := internalHelperBodyScope callee helper) (stmts := callee.body)
        helperFuel extraFuel hfuelPos ctx.generic ctx.scope ctx.exact ctx.bounded
        ctx.runtime with ⟨bodyIR, hcompile, hstep⟩
    have hmatch :=
      stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep
    have hmode :=
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        (SourceSemantics.effectiveFields spec) spec.events spec.errors .calldata
        helper.rets true (internalHelperBodyScope callee helper) []
        Verity.Core.Intrinsics.HardFork.cancun callee.body spec.functions ctx.returnFree
    have hbody : bodyIR = helper.body := by
      apply Except.ok.inj
      calc
        Except.ok bodyIR =
            CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              spec.events spec.errors .calldata [] false (internalHelperBodyScope callee helper)
              [] callee.body spec.functions := hcompile.symm
        _ = CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              spec.events spec.errors .calldata helper.rets true
              (internalHelperBodyScope callee helper) [] callee.body spec.functions := by
          simpa only [CompilationModel.compileStmtList] using hmode.symm
        _ = Except.ok helper.body := ctx.bodyCompile
    subst bodyIR
    simpa [internalHelperBodySourceResult, internalHelperBodyIRExec] using hmatch
  · simpa [internalHelperBodyInterpretation, ctx.bindArgs] using ctx.bodyResultProjection

end Compiler.Proofs.IRGeneration
