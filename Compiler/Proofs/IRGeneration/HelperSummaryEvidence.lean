import Compiler.Proofs.IRGeneration.InternalHelperBodyCorrespondence

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open SourceSemantics

private theorem eraseDups_nodup_and_mem_aux_local [BEq α] [LawfulBEq α]
    (n : Nat) (l : List α) (hlen : l.length ≤ n) :
    (l.eraseDups).Nodup ∧ (∀ a, a ∈ l.eraseDups ↔ a ∈ l) := by
  induction n generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst this
      exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | succ n ih =>
      match l with
      | [] => exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
      | x :: xs =>
          rw [List.eraseDups_cons]
          have hfilt_len : (xs.filter fun b => !b == x).length ≤ n := by
            have := List.length_filter_le (fun b => !b == x) xs
            simp [List.length_cons] at hlen
            omega
          have ⟨ihNd, ihMem⟩ := ih _ hfilt_len
          constructor
          · rw [List.nodup_cons]
            constructor
            · intro h
              have hmf := (ihMem x).mp h
              rw [List.mem_filter] at hmf
              have := hmf.2
              simp at this
            · exact ihNd
          · intro a
            constructor
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · exact Or.inr (List.mem_filter.mp ((ihMem a).mp h)).1
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · by_cases heq : a == x
                · exact Or.inl (beq_iff_eq.mp heq)
                · exact Or.inr ((ihMem a).mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

private theorem List.mem_of_mem_eraseDups_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l :=
  ((eraseDups_nodup_and_mem_aux_local l.length l (Nat.le_refl _)).2 a).mp h

private theorem List.mem_eraseDups_of_mem_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  ((eraseDups_nodup_and_mem_aux_local l.length l (Nat.le_refl _)).2 a).mpr h

/-- Canonical selector-aware helper summary. -/
def exactInternalHelperSummary
    (spec : CompilationModel)
    (fn : FunctionSpec) : InternalHelperSummaryContract where
  post fuel selector initialWorld args success returnValue finalWorld :=
    let result := internalHelperBodyInterpretation
      spec fuel fn initialWorld selector args
    success = result.success ∧
      returnValue = result.returnValue ∧
      finalWorld = result.world

theorem exactInternalHelperSummary_soundAtSelector
    (selector : Nat) (spec : CompilationModel) (fn : FunctionSpec) :
    InternalHelperSummarySoundAtSelector selector spec fn
      (exactInternalHelperSummary spec fn) := by
  intro fuel initialWorld args
  exact ⟨rfl, rfl, rfl⟩

/-- Legacy selector-free soundness of the exact summary, recovered via the
selector-0 bridge from `InternalHelperSummarySoundAtSelector`. -/
theorem exactInternalHelperSummary_sound
    (spec : CompilationModel)
    (fn : FunctionSpec) :
    InternalHelperSummarySound spec fn (exactInternalHelperSummary spec fn) :=
  InternalHelperSummarySound_of_soundAtSelector_zero
    (exactInternalHelperSummary_soundAtSelector 0 spec fn)

/-- Expressions admitted in read-only helper bodies. This reuses the existing
call-surface classifier: storage, transient-storage, calldata, memory, and
environment reads are admitted, while helper calls, foreign calls, and low-level
effectful calls are excluded. -/
def helperExprReadOnly (expr : Expr) : Bool :=
  exprTouchesUnsupportedCallSurface expr = false

/-- Statement heads that preserve `RuntimeState.world` in the helper-aware
source semantics. The slice admits local binding updates and pure/read-only
control flow, but excludes storage/mapping writes, memory/transient writes,
returns, logs, helper calls, foreign calls, ECMs, and unsafe/Yul surfaces. -/
def helperStmtReadOnly : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .require value _ =>
      helperExprReadOnly value
  | .stop => true
  | _ => false

/-- List lift of `helperStmtReadOnly`. -/
def helperStmtListReadOnly : List Stmt → Bool
  | [] => true
  | stmt :: rest => helperStmtReadOnly stmt && helperStmtListReadOnly rest

/-- Syntactic, compositional world-preservation predicate for internal helpers.
It admits non-empty view-style bodies with local lets/assignments and state
reads, while rejecting every source form that can mutate the world on success. -/
def helperBodyNoWorldMutationOnSuccess (fn : FunctionSpec) : Prop :=
  helperStmtListReadOnly fn.body = true

private def stmtResultWorldEq
    (initialWorld : Verity.ContractState) : StmtResult → Prop
  | .continue state | .stop state | .return _ state => state.world = initialWorld
  | .revert => True

private theorem stmtResultWorldEq_of_eq
    {initialWorld : Verity.ContractState}
    {result actual : StmtResult}
    (hactual : stmtResultWorldEq initialWorld actual)
    (heq : actual = result) :
    stmtResultWorldEq initialWorld result := by
  subst result
  exact hactual

private theorem execStmtWithHelpers_readOnly_world_eq
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {stmt : Stmt}
    (hreadonly : helperStmtReadOnly stmt = true) :
    stmtResultWorldEq state.world
      (execStmtWithHelpers spec fields fuel state stmt) := by
  cases stmt <;> simp [helperStmtReadOnly] at hreadonly ⊢
  case letVar name value =>
    unfold execStmtWithHelpers
    cases evalExprWithHelpers spec fields fuel state value <;>
      simp [stmtResultWorldEq]
  case assignVar name value =>
    unfold execStmtWithHelpers
    cases evalExprWithHelpers spec fields fuel state value <;>
      simp [stmtResultWorldEq]
  case require cond message =>
    unfold execStmtWithHelpers
    cases evalExprWithHelpers spec fields fuel state cond with
    | none => simp [stmtResultWorldEq]
    | some resolved =>
        by_cases hcond : resolved != 0
        · simp [hcond, stmtResultWorldEq]
        · simp [hcond, stmtResultWorldEq]
  case stop =>
    unfold execStmtWithHelpers
    simp [stmtResultWorldEq]

private theorem execStmtListWithHelpers_readOnly_world_eq
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {stmts : List Stmt}
    (hreadonly : helperStmtListReadOnly stmts = true) :
    stmtResultWorldEq state.world
      (execStmtListWithHelpers spec fields fuel state stmts) := by
  cases stmts with
  | nil =>
      unfold execStmtListWithHelpers
      simp [stmtResultWorldEq]
  | cons stmt rest =>
      simp [helperStmtListReadOnly] at hreadonly
      rcases hreadonly with ⟨hstmt, hrest⟩
      unfold execStmtListWithHelpers
      have hstmtWorld :=
        execStmtWithHelpers_readOnly_world_eq
          (spec := spec) (fields := fields) (fuel := fuel)
          (state := state) (stmt := stmt) hstmt
      cases hresult : execStmtWithHelpers spec fields fuel state stmt
      · rename_i next
        simp [hresult, stmtResultWorldEq] at hstmtWorld ⊢
        have hrestWorld :=
          execStmtListWithHelpers_readOnly_world_eq
            (spec := spec) (fields := fields) (fuel := fuel)
            (state := next) (stmts := rest) hrest
        cases hfinal : execStmtListWithHelpers spec fields fuel next rest <;>
          simp [hfinal, stmtResultWorldEq] at hrestWorld ⊢
        · exact hrestWorld.trans hstmtWorld
        · exact hrestWorld.trans hstmtWorld
        · exact hrestWorld.trans hstmtWorld
      · simpa [hresult, stmtResultWorldEq] using hstmtWorld
      · simpa [hresult, stmtResultWorldEq] using hstmtWorld
      · simp [hresult, stmtResultWorldEq]

theorem exactInternalHelperSummary_preservesWorldOnSuccess_of_readOnly_body
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hbody : helperBodyNoWorldMutationOnSuccess fn) :
    InternalHelperSummaryPreservesWorldOnSuccess
      (exactInternalHelperSummary spec fn) := by
  intro fuel selector initialWorld args success returnValue finalWorld hpost hsuccess
  change
    success = (internalHelperBodyInterpretation spec fuel fn initialWorld selector args).success ∧
      returnValue = (internalHelperBodyInterpretation spec fuel fn initialWorld selector args).returnValue ∧
      finalWorld = (internalHelperBodyInterpretation spec fuel fn initialWorld selector args).world
    at hpost
  rcases hpost with ⟨hsuccessEq, _hret, hworld⟩
  have hsuccess' :
      (internalHelperBodyInterpretation spec fuel fn initialWorld selector args).success =
        true := by
    simpa [hsuccessEq] using hsuccess
  rw [hworld]
  unfold internalHelperBodyInterpretation at hsuccess' ⊢
  cases hbind : bindInternalArgs fn.params args with
  | none =>
      simp [hbind, revertedInternalResult] at hsuccess'
  | some bindings =>
      simp [hbind, internalHelperBodySourceResult, internalHelperBodyRuntime] at hsuccess' ⊢
      have hreadonly :=
        execStmtListWithHelpers_readOnly_world_eq
          (spec := spec) (fields := effectiveFields spec) (fuel := fuel)
          (state := { world := initialWorld, bindings := bindings, selector := selector })
          (stmts := fn.body) hbody
      -- Case on the statement result; keyword constructors need `rename_i`.
      generalize hresult :
        execStmtListWithHelpers spec (effectiveFields spec) fuel
          { world := initialWorld, bindings := bindings, selector := selector } fn.body =
        result
      match result, hresult, hreadonly, hsuccess' with
      | StmtResult.continue state, hresult, hreadonly, hsuccess' =>
          simp [hresult, internalHelperResultOfStmtResult, successInternalResult,
            stmtResultWorldEq] at hreadonly ⊢
          exact hreadonly
      | StmtResult.stop state, hresult, hreadonly, hsuccess' =>
          simp [hresult, internalHelperResultOfStmtResult, successInternalResult,
            stmtResultWorldEq] at hreadonly ⊢
          exact hreadonly
      | StmtResult.return value state, hresult, hreadonly, hsuccess' =>
          simp [hresult, internalHelperResultOfStmtResult, successInternalResult,
            stmtResultWorldEq] at hreadonly ⊢
          exact hreadonly
      | StmtResult.revert, hresult, hreadonly, hsuccess' =>
          simp [hresult, internalHelperResultOfStmtResult, revertedInternalResult] at hsuccess'

theorem exactInternalHelperSummary_preservesWorldOnSuccess_of_empty_body
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hbody : fn.body = []) :
    InternalHelperSummaryPreservesWorldOnSuccess
      (exactInternalHelperSummary spec fn) := by
  apply exactInternalHelperSummary_preservesWorldOnSuccess_of_readOnly_body
  simp [helperBodyNoWorldMutationOnSuccess, hbody, helperStmtListReadOnly]

/-- Concrete rank assignment for an internal-helper table. Earlier functions in
`spec.functions` receive larger ranks, so a topologically ordered helper table
can prove every direct callee decreases rank. -/
def internalHelperTableRank (spec : CompilationModel) (helperName : String) : Nat :=
  spec.functions.length - (spec.functions.map (·.name)).idxOf helperName

/-- Call-graph topological-order obligation for the concrete rank assignment:
every direct helper edge points to a strictly smaller concrete rank. -/
def InternalHelperTableRanksDecrease (spec : CompilationModel) : Prop :=
  ∀ caller, caller ∈ spec.functions →
    ∀ calleeName, calleeName ∈ helperCallNames caller →
      calleeName ∈ spec.functions.map (·.name) →
      internalHelperTableRank spec calleeName <
        internalHelperTableRank spec caller.name

/-- Input support needed to build an exact supported-helper witness for one
callee. The generated witness uses `exactInternalHelperSummary` and the concrete
table rank; callers do not provide a summary contract. -/
structure ExactInternalHelperSupport
    (spec : CompilationModel)
    (calleeName : String) where
  callee : FunctionSpec
  nameEq : callee.name = calleeName
  present : callee ∈ spec.functions
  internal : callee.isInternal = true
  nonSpecialEntrypoint : isInteropEntrypointName callee.name = false
  params : SupportedParamProfile callee.params
  returns : SupportedReturnProfile callee
  core : SupportedBodyCoreInterface callee
  state : SupportedBodyStateInterface callee
  foreign : stmtListTouchesUnsupportedForeignSurface callee.body = false
  lowLevel : stmtListTouchesUnsupportedLowLevelSurface callee.body = false
  effects : SupportedBodyEffectInterface callee
  constructorRawCalldataSurfaceClosed :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface callee.body = false
  noLocalObligations : callee.localObligations = []

def ExactInternalHelperSupport.toWitness
    {spec : CompilationModel}
    {calleeName : String}
    (support : ExactInternalHelperSupport spec calleeName) :
    SupportedInternalHelperWitness spec calleeName where
  callee := support.callee
  nameEq := support.nameEq
  summary := {
    present := support.present
    internal := support.internal
    nonSpecialEntrypoint := support.nonSpecialEntrypoint
    helperRank := internalHelperTableRank spec calleeName
    params := support.params
    returns := support.returns
    core := support.core
    state := support.state
    foreign := support.foreign
    lowLevel := support.lowLevel
    effects := support.effects
    constructorRawCalldataSurfaceClosed :=
      support.constructorRawCalldataSurfaceClosed
    contract := exactInternalHelperSummary spec support.callee
    noLocalObligations := support.noLocalObligations
  }

theorem exactInternalHelperSupport_toWitness_contract_eq_exact
    {spec : CompilationModel}
    {calleeName : String}
    (support : ExactInternalHelperSupport spec calleeName) :
    support.toWitness.summary.contract =
      exactInternalHelperSummary spec support.callee := rfl

theorem exactInternalHelperSupport_toWitness_summary_sound
    {spec : CompilationModel}
    {calleeName : String}
    (support : ExactInternalHelperSupport spec calleeName) :
    InternalHelperSummarySound spec
      (ExactInternalHelperSupport.toWitness support).callee
      (ExactInternalHelperSupport.toWitness support).summary.contract := by
  exact exactInternalHelperSummary_sound spec support.callee

theorem exactInternalHelperSupport_toWitness_summary_soundAtSelector
    {spec : CompilationModel} {calleeName : String}
    (support : ExactInternalHelperSupport spec calleeName) (selector : Nat) :
    InternalHelperSummarySoundAtSelector selector spec
      (ExactInternalHelperSupport.toWitness support).callee
      (ExactInternalHelperSupport.toWitness support).summary.contract := by
  exact exactInternalHelperSummary_soundAtSelector selector spec support.callee

theorem exactInternalHelperSupport_toWitness_preservesWorldOnSuccess
    {spec : CompilationModel}
    {calleeName : String}
    (support : ExactInternalHelperSupport spec calleeName)
    (hbody : helperBodyNoWorldMutationOnSuccess support.callee) :
    InternalHelperSummaryPreservesWorldOnSuccess
      (ExactInternalHelperSupport.toWitness support).summary.contract := by
  exact exactInternalHelperSummary_preservesWorldOnSuccess_of_readOnly_body
    (spec := spec) (fn := support.callee) hbody

/-- Build the existing body-helper interface from exact-summary witnesses and
the concrete decreasing-rank evidence. -/
def supportedBodyHelperInterface_of_exactSummariesAndRanks
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hcaller : fn ∈ spec.functions)
    (hdecrease : InternalHelperTableRanksDecrease spec)
    (supportOf :
      ∀ calleeName, calleeName ∈ helperCallNames fn →
        ExactInternalHelperSupport spec calleeName)
    (exprPreserves :
      ∀ calleeName (hmem : calleeName ∈ exprHelperCallNames fn),
        let hcall : calleeName ∈ helperCallNames fn :=
          exprHelperCallNames_subset_helperCallNames hmem
        helperBodyNoWorldMutationOnSuccess
          (supportOf calleeName hcall).callee) :
    SupportedBodyHelperInterface spec fn := by
  refine {
    helperRank := internalHelperTableRank spec fn.name
    callNamesNodup := helperCallNames_nodup fn
    summaryOf := ?_
    calleeRanksDecrease := ?_
    exprCallsPreserveWorld := ?_
  }
  · intro calleeName hmem
    exact (supportOf calleeName hmem).toWitness
  · intro calleeName hmem
    have hcalleePresent : calleeName ∈ spec.functions.map (·.name) := by
      exact List.mem_map.mpr
        ⟨(supportOf calleeName hmem).callee,
          (supportOf calleeName hmem).present,
          (supportOf calleeName hmem).nameEq⟩
    simpa [ExactInternalHelperSupport.toWitness] using
      hdecrease fn hcaller calleeName hmem hcalleePresent
  · intro calleeName hmem
    exact exactInternalHelperSupport_toWitness_preservesWorldOnSuccess
      (supportOf calleeName (exprHelperCallNames_subset_helperCallNames hmem))
      (exprPreserves calleeName hmem)

/-- One-step soundness catalog produced by exact helper support. -/
theorem supportedBodyHelperSummariesSound_of_exactSummaries
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hexact :
      ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
        hHelpers.summaryContractOfCall hmem =
          exactInternalHelperSummary spec (hHelpers.summaryOfCall hmem).callee) :
    SupportedBodyHelperSummariesSound spec fn hHelpers := by
  intro calleeName hmem
  rw [hexact calleeName hmem]
  exact exactInternalHelperSummary_sound spec (hHelpers.summaryOfCall hmem).callee

/-- Exact supported-helper evidence is sound at every inherited selector. -/
theorem supportedBodyHelperSummariesSoundAtSelector_of_exactSummaries
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hexact :
      ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
        hHelpers.summaryContractOfCall hmem =
          exactInternalHelperSummary spec (hHelpers.summaryOfCall hmem).callee)
    (selector : Nat) :
    ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
      InternalHelperSummarySoundAtSelector selector spec
        (hHelpers.summaryOfCall hmem).callee
        (hHelpers.summaryContractOfCall hmem) := by
  intro calleeName hmem
  rw [hexact calleeName hmem]
  exact exactInternalHelperSummary_soundAtSelector selector spec
    (hHelpers.summaryOfCall hmem).callee

namespace Regression

private theorem mem_helperB_eraseDups_singleton
    {calleeName : String}
    (hmem : calleeName ∈ (["helperB"] : List String).eraseDups) :
    calleeName = "helperB" := by
  have hraw : calleeName ∈ (["helperB"] : List String) :=
    List.mem_of_mem_eraseDups_local hmem
  simpa using hraw

private def helperB : FunctionSpec :=
  { name := "helperB"
    params := []
    returnType := none
    returns := []
    isInternal := true
    body := [
      Stmt.letVar "x" (Expr.literal 7),
      Stmt.assignVar "x" (Expr.add (Expr.localVar "x") (Expr.literal 1))
    ] }

private def helperA : FunctionSpec :=
  { name := "helperA"
    params := []
    returnType := none
    returns := []
    isInternal := true
    body := [Stmt.letVar "x" (Expr.internalCall "helperB" [])] }

private def twoHelperSpec : CompilationModel :=
  { name := "TwoHelperEvidence"
    fields := []
    constructor := none
    functions := [helperA, helperB] }

private def helperB_support :
    ExactInternalHelperSupport twoHelperSpec "helperB" := by
  refine {
    callee := helperB
    nameEq := rfl
    present := ?_
    internal := rfl
    nonSpecialEntrypoint := rfl
    params := ?_
    returns := ?_
    core := ?_
    state := ?_
    foreign := rfl
    lowLevel := rfl
    effects := ?_
    constructorRawCalldataSurfaceClosed := rfl
    noLocalObligations := rfl
  }
  · right
    left
  · refine {
      namesNodup := ?_
      supported := ?_
      calldataThreshold := ?_
    }
    · simp [helperB]
    · intro param hmem
      simp [helperB] at hmem
    · simp [helperB, Compiler.Constants.evmModulus]
  · exact ⟨⟨[], rfl, by simp [SupportedExternalReturnProfile]⟩⟩
  · exact ⟨rfl⟩
  · exact ⟨rfl⟩
  · exact ⟨rfl⟩

private theorem twoHelperRanksDecrease :
    InternalHelperTableRanksDecrease twoHelperSpec := by
  intro caller hcaller calleeName hmem _hcalleePresent
  simp [twoHelperSpec, helperA, helperB] at hcaller
  rcases hcaller with rfl | hcaller
  · have hname : calleeName = "helperB" := by
      apply mem_helperB_eraseDups_singleton
      simpa [helperCallNames, stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames, exprInternalHelperCallNames,
        exprListInternalHelperCallNames] using hmem
    subst calleeName
    decide
  · rcases hcaller with rfl | hnil
    · simp [helperCallNames, stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames, exprInternalHelperCallNames,
        exprListInternalHelperCallNames] at hmem

theorem helperB_exactSummary_sound :
    InternalHelperSummarySound twoHelperSpec helperB
      (exactInternalHelperSummary twoHelperSpec helperB) :=
  exactInternalHelperSummary_sound twoHelperSpec helperB

theorem helperB_exactSummary_preservesWorld :
    InternalHelperSummaryPreservesWorldOnSuccess
      (exactInternalHelperSummary twoHelperSpec helperB) :=
  exactInternalHelperSummary_preservesWorldOnSuccess_of_readOnly_body
    (spec := twoHelperSpec) (fn := helperB) (by
      simp [helperBodyNoWorldMutationOnSuccess, helperB,
        helperStmtListReadOnly, helperStmtReadOnly, helperExprReadOnly,
        exprTouchesUnsupportedCallSurface])

def helperA_supportedBodyHelperInterface :
    SupportedBodyHelperInterface twoHelperSpec helperA := by
  refine supportedBodyHelperInterface_of_exactSummariesAndRanks
    (spec := twoHelperSpec)
    (fn := helperA)
    ?_ twoHelperRanksDecrease ?_ ?_
  · simp [twoHelperSpec, helperA]
  · intro calleeName hmem
    have hname : calleeName = "helperB" := by
      apply mem_helperB_eraseDups_singleton
      simpa [helperA, helperCallNames, stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames, exprInternalHelperCallNames,
        exprListInternalHelperCallNames] using hmem
    subst calleeName
    exact helperB_support
  · intro calleeName hmem
    have hname : calleeName = "helperB" := by
      apply mem_helperB_eraseDups_singleton
      simpa [helperA, exprHelperCallNames, stmtListExprHelperCallNames,
        stmtExprHelperCallNames, exprInternalHelperCallNames,
        exprListInternalHelperCallNames] using hmem
    subst calleeName
    change helperStmtListReadOnly helperB.body = true
    simp [helperB, helperStmtListReadOnly, helperStmtReadOnly,
      helperExprReadOnly, exprTouchesUnsupportedCallSurface]

/-- Non-vacuous witness for the positive helper-rich supported fragment.
`helperA` contains the expression-position call `helperB()`, whose exact
summary, decreasing rank, and successful world preservation are supplied by
`helperA_supportedBodyHelperInterface`. -/
def helperA_supportedHelperRichBodyFragment :
    SupportedHelperRichBodyFragment twoHelperSpec helperA := by
  refine {
    hasInternalHelperCall := ?_
    coreSupported := rfl
    expressionsInScope := by
      simp [helperA, stmtListHelperRichExprsInScope, stmtHelperRichExprsInScope,
        stmtNextScope]
    state := ⟨rfl⟩
    calls :=
      { helpers := helperA_supportedBodyHelperInterface
        foreign := rfl
        lowLevel := rfl }
    effects := ⟨rfl⟩
    constructorRawCalldataSurfaceClosed := rfl
    noLocalObligations := rfl
  }
  exact ⟨"helperB", by
    apply List.mem_eraseDups_of_mem_local
    simp [helperA, stmtListInternalHelperCallNames,
      stmtInternalHelperCallNames, exprInternalHelperCallNames,
    exprListInternalHelperCallNames]⟩

/-- Function-boundary witness for the genuine helper caller.  This is the
non-vacuous inhabitant that the legacy `SupportedFunction` gate could not
express. -/
def helperA_supportedFunctionWithHelpers :
    SupportedFunctionWithHelpers twoHelperSpec helperA := by
  refine {
    nonSpecialEntrypoint := by simp [helperA, isInteropEntrypointName]
    noNonReentrant := rfl
    params := ?_
    returns := ?_
    body := .helperRich helperA_supportedHelperRichBodyFragment
  }
  · refine ⟨by simp [helperA], ?_, ?_⟩
    · simp [helperA]
    · simp [helperA, Compiler.Constants.evmModulus]
  · exact { resolved := ⟨[], rfl, trivial⟩ }

private def helperB_supportedFunctionWithHelpers :
    SupportedFunctionWithHelpers twoHelperSpec helperB := by
  refine {
    nonSpecialEntrypoint := by simp [helperB, isInteropEntrypointName]
    noNonReentrant := rfl
    params := ?_
    returns := ?_
    body := .internalHelper helperB_support.toWitness.summary
  }
  · refine ⟨by simp [helperB], ?_, ?_⟩
    · simp [helperB]
    · simp [helperB, Compiler.Constants.evmModulus]
  · exact { resolved := ⟨[], rfl, trivial⟩ }

/-- Whole-spec regression: a model containing an internal helper caller and
its callee now inhabits the helper-aware support inventory without any
helper-free premise. -/
noncomputable def twoHelper_supportedSpecWithHelpers :
    SupportedSpecWithHelpers twoHelperSpec [] := by
  refine {
    invariants := ?_
    surface := ?_
    constructor := ?_
    functions := ?_
  }
  · refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp [twoHelperSpec]
    · simp [twoHelperSpec, helperA, helperB]
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [contractUsesCheckedArithmetic, twoHelperSpec]
      constructor
      · simp [helperA, stmtListMayUseCheckedArithmetic, stmtMayUseCheckedArithmetic]
      · simp [helperB, stmtListMayUseCheckedArithmetic, stmtMayUseCheckedArithmetic]
    · rw [templateIntrinsicItems, twoHelperSpec, helperA, helperB]
      unfold collectTemplateIntrinsicsFromStmts
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      repeat rw [collectTemplateIntrinsicsFromStmt.eq_def]
      simp [Stmt.directMetadata, Stmt.childLists,
        collectTemplateIntrinsicsFromExpr, Expr.children]
    · simp [twoHelperSpec, helperA, helperB]
    · simp [twoHelperSpec, helperA, helperB]
  · intro ctor hctor
    simp [twoHelperSpec] at hctor
  · intro fn hfn
    simp [twoHelperSpec] at hfn
    by_cases hA : fn = helperA
    · subst fn
      exact helperA_supportedFunctionWithHelpers
    · have hB : fn = helperB := Or.resolve_left hfn hA
      subst fn
      exact helperB_supportedFunctionWithHelpers

/-- Explicit source-syntax evidence that the positive witness is genuinely
helper-rich, rather than inhabited through an empty call inventory. -/
theorem helperA_contains_internal_helper_call :
    Stmt.letVar "x" (Expr.internalCall "helperB" []) ∈ helperA.body := by
  simp [helperA]

theorem helperA_helperB_occurs_in_call_inventory :
    "helperB" ∈ helperCallNames helperA := by
  apply List.mem_eraseDups_of_mem_local
  simp [helperA, stmtListInternalHelperCallNames,
    stmtInternalHelperCallNames, exprInternalHelperCallNames,
    exprListInternalHelperCallNames]

theorem helperA_supportedBodyHelperInterface_summary_sound :
    SupportedBodyHelperSummariesSound twoHelperSpec helperA
      helperA_supportedBodyHelperInterface := by
  apply supportedBodyHelperSummariesSound_of_exactSummaries
  intro calleeName hmem
  have hname : calleeName = "helperB" := by
    apply mem_helperB_eraseDups_singleton
    simpa [helperA, helperCallNames, stmtListInternalHelperCallNames,
      stmtInternalHelperCallNames, exprInternalHelperCallNames,
      exprListInternalHelperCallNames] using hmem
  subst calleeName
  rfl

theorem helperA_calls_helperB_rank_decreases :
    internalHelperTableRank twoHelperSpec "helperB" <
      internalHelperTableRank twoHelperSpec "helperA" := by
  simpa [internalHelperTableRank, twoHelperSpec, helperA, helperB]

end Regression

end Compiler.Proofs.IRGeneration
