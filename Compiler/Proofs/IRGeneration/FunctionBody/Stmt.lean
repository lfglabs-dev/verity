import Compiler.Proofs.IRGeneration.FunctionBody.Base

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace FunctionBody

theorem runtimeStateMatchesIR_setVar_bindValue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (boundName : String)
    (value : Nat) :
    runtimeStateMatchesIR fields
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings boundName value }
      (state.setVar boundName value) := by
  cases runtime
  cases state
  simpa [runtimeStateMatchesIR, IRState.setVar]

theorem runtimeStateMatchesIR_setVar_irrelevant
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Nat}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    runtimeStateMatchesIR fields runtime (state.setVar name value) := by
  cases state
  simpa [runtimeStateMatchesIR, IRState.setVar] using hmatch

theorem runtimeStateMatchesIR_setVars_irrelevant
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {updates : List (String × Nat)}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    runtimeStateMatchesIR fields runtime (state.setVars updates) := by
  induction updates generalizing state with
  | nil =>
      simpa [IRState.setVars] using hmatch
  | cons update updates ih =>
      cases update with
      | mk name value =>
          simp [IRState.setVars]
          exact ih (runtimeStateMatchesIR_setVar_irrelevant
            (state := state) (name := name) (value := value) hmatch)

def stmtResultMatchesIRExecExact :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .stop runtime, .stop state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .return _ runtime, .return _ state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .revert, .revert _ => True
  | _, _ => False

/-- Statement fragment whose correctness can already be discharged using the
expression core, without storage, calls, or ABI encoding. -/
inductive StmtCompileCore : Stmt → Prop where
  | letVar {name : String} {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.letVar name value)
  | assignVar {name : String} {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.assignVar name value)
  | require_ {cond : Expr} {message : String} :
      ExprCompileCore cond → StmtCompileCore (.require cond message)
  | return_ {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.return value)
  | stop :
      StmtCompileCore .stop
  | mstore {offset value : Expr} :
      ExprCompileCore offset → ExprCompileCore value →
        StmtCompileCore (.mstore offset value)
  | tstore {offset value : Expr} :
      ExprCompileCore offset → ExprCompileCore value →
        StmtCompileCore (.tstore offset value)

theorem compileStmt_core_ok
    {fields : List Field}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR, CompilationModel.compileStmt fields [] [] .calldata [] false [] [] stmt = Except.ok bodyIR := by
  cases hcore with
  | letVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.let_ name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | assignVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.assign name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | require_ hcond =>
      rename_i cond message
      rcases compileRequireFailCond_core_ok hcond with ⟨failCond, hfailCond⟩
      exact ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)], by
        rw [CompilationModel.compileStmt, hfailCond]
        rfl⟩
  | return_ hvalue =>
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | stop =>
      exact ⟨[YulStmt.expr (YulExpr.call "stop" [])], by
        rw [CompilationModel.compileStmt]
        rfl⟩
  | mstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])], by
        rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
        rfl⟩
  | tstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])], by
        rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
        rfl⟩

theorem runtimeStateMatchesIR_setBothMemory
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (offset : Nat) (value : Nat)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            memory := fun o => if o = offset then value else runtime.world.memory o
          } }
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel, hcd, hcds, hmem, hret, hevt⟩ := hmatch
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel, hcd, hcds, ?_, hret, hevt⟩
  · rw [hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · -- memory
    funext o
    by_cases ho : o = offset
    · subst ho
      simp only [ite_true, Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hvalue]
    · simp [ho]
      exact congrFun hmem o

/-- Rebuild `runtimeStateMatchesIR` after a proof step has already established
the exact low-level memory and event-log alignment for the updated source/IR
states. This is the reusable postcondition shape for event emission, where the
compiler writes scratch memory and appends a Yul log entry. -/
theorem runtimeStateMatchesIR_updateMemoryEvents
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (sourceMemory : Nat → Verity.Core.Uint256)
    (irMemory : Nat → Nat)
    (sourceEvents : List Verity.Event)
    (irEvents : List (List Nat))
    (hmemory : irMemory = fun o => (sourceMemory o).val)
    (hevents : irEvents = SourceSemantics.encodeEvents sourceEvents) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            memory := sourceMemory
            events := sourceEvents } }
      { state with
          memory := irMemory
          events := irEvents } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel,
    hcd, hcds, hmem, hret, hevt⟩ := hmatch
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel,
    hcd, hcds, hmemory, hret, hevents⟩
  rw [hstor]
  funext slot
  exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)

theorem runtimeStateMatchesIR_setTransientStorage
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (offset : Nat) (value : Nat)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            transientStorage := fun o => if o = offset then value else runtime.world.transientStorage o
          } }
      { state with
          transientStorage := fun o => if o = offset then value else state.transientStorage o } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel, hcd, hcds, hmem, hret, hevt⟩ := hmatch
  refine ⟨?_, ?_, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, hsel, hcd, hcds, hmem, hret, hevt⟩
  · -- storage: encodeStorageAt doesn't depend on transientStorage
    rw [hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · -- transientStorage
    funext o
    by_cases ho : o = offset
    · subst ho
      simp only [ite_true, Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hvalue]
    · simp [ho]
      exact congrFun htrans o

theorem bindingsExactlyMatchIRVars_setMemory
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVars bindings
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  intro name
  simpa [IRState.getVar] using hexact name

theorem bindingsExactlyMatchIRVarsOnScope_setMemory
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  intro name hname
  simpa [IRState.getVar] using hexact name hname

theorem bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {tempName : String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hfresh : tempName ∉ scope) :
    bindingsExactlyMatchIRVarsOnScope scope bindings (state.setVar tempName value) := by
  intro name hname
  by_cases hEq : name = tempName
  · subst hEq
    exact False.elim (hfresh hname)
  · rw [getVar_setVar_ne state tempName name value hEq]
    exact hexact name hname

theorem bindingsExactlyMatchIRVarsOnScope_setVars_irrelevant
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {updates : List (String × Nat)}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hfresh : ∀ update ∈ updates, update.1 ∉ scope) :
    bindingsExactlyMatchIRVarsOnScope scope bindings (state.setVars updates) := by
  induction updates generalizing state with
  | nil =>
      simpa [IRState.setVars] using hexact
  | cons update updates ih =>
      cases update with
      | mk name value =>
          simp [IRState.setVars]
          apply ih
          · exact bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
              (state := state) (tempName := name) (value := value)
              hexact (hfresh (name, value) (by simp))
          · intro update hmem
            exact hfresh update (by simp [hmem])

theorem bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {boundName : String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    bindingsExactlyMatchIRVarsOnScope (boundName :: scope)
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro name hname
  simp at hname
  rcases hname with rfl | hname
  · simp [lookupBinding?_bindValue_eq]
  · by_cases hEq : name = boundName
    · subst hEq
      simp [lookupBinding?_bindValue_eq]
    · rw [lookupBinding?_bindValue_ne bindings boundName name value hEq]
      rw [getVar_setVar_ne state boundName name value hEq]
      exact hexact name hname

@[simp] theorem encodeEvents_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    SourceSemantics.encodeEvents (SourceSemantics.withTransactionContext world tx).events =
      SourceSemantics.encodeEvents world.events := by
  rfl

@[simp] theorem encodeStorage_withTransactionContext
    (spec : CompilationModel)
    (world : Verity.ContractState)
    (tx : IRTransaction) :
    SourceSemantics.encodeStorage spec (SourceSemantics.withTransactionContext world tx) =
      SourceSemantics.encodeStorage spec world := by
  simpa using SourceSemantics.encodeStorage_withTransactionContext spec world tx

def stmtResultMatchesIRExec
    (fields : List Field) :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state => runtimeStateMatchesIR fields runtime state
  | .stop runtime, .stop state => runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧ runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

def stmtResultToSourceResult
    (spec : CompilationModel)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.StmtResult → SourceSemantics.SourceContractResult
  | .continue runtime => SourceSemantics.successResult spec runtime.world none
  | .stop runtime => SourceSemantics.successResult spec runtime.world none
  | .return value runtime => SourceSemantics.successResult spec runtime.world (some value)
  | .revert => SourceSemantics.revertedResult spec initialWorld

def sourceResultMatchesIRResult
    (source : SourceSemantics.SourceContractResult)
    (ir : IRResult) : Prop :=
  source.success = ir.success ∧
  source.returnValue = ir.returnValue ∧
  (fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (source.finalStorage s.toNat)) =
    ir.finalStorage ∧
  source.events = ir.events

/-- Helper: `eval_compileExpr_core` implies both `evalIRExpr` and source `evalExpr`
succeed with the same `Nat` value. This factored lemma avoids repeating the
monadic-bind unfold in every statement proof. -/
theorem eval_compileExpr_core_split
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    ∃ v, evalIRExpr state exprIR = some v ∧
         SourceSemantics.evalExpr fields runtime expr = some v ∧
         v < Compiler.Constants.evmModulus := by
  have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
  rw [hcompile] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state exprIR with _ | v
  · simp [hIR, Option.bind] at heval
  · refine ⟨v, rfl, ?_, ?_⟩
    · simp [hIR, Option.bind] at heval
      exact heval.symm
    · have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      simp [hIR, Option.bind] at heval
      rw [heval.symm] at hlt
      -- hlt : some v < evmModulus, which Lean elaborates as v < evmModulus
      exact hlt

theorem exec_compileStmt_letVar_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] (.letVar name value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.letVar name value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
  refine ⟨[YulStmt.let_ name valueIR], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · -- Get the bridge: both evaluations succeed with same value
    have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- heval now relates evalIRExpr and evalExpr via Option bind
    -- Source: execStmt letVar does match evalExpr ... with some v => continue | none => revert
    -- IR: execIRStmts on [let_ name valueIR] does match evalIRExpr state valueIR with some v => continue (setVar) | none => revert
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt]
    -- Now we need to case-split on evalIRExpr state valueIR
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- evalIRExpr returns none → but eval_compileExpr_core says it returns some
      simp [hIR, Option.bind] at heval
    · -- evalIRExpr returns some v
      simp [hIR, Option.bind] at heval
      -- heval : some v = evalExpr fields runtime value (up to wrapping)
      -- Now source side: evalExpr returns some v too
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      rw [heval.symm] at hlt
      exact ⟨hruntime, bindingsExactlyMatchIRVars_setVar_bindValue hexact name v,
             bindingsBounded_bindValue hbounded name v hlt⟩

theorem exec_compileStmt_assignVar_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] (.assignVar name value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.assignVar name value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
  refine ⟨[YulStmt.assign name valueIR], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      rw [heval.symm] at hlt
      exact ⟨hruntime, bindingsExactlyMatchIRVars_setVar_bindValue hexact name v,
             bindingsBounded_bindValue hbounded name v hlt⟩

theorem exec_compileStmt_return_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] (.return value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.return value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
  refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt, evalIRExpr,
               evalIRExprs]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      have hlt : v < Verity.Core.Uint256.modulus := by
        have := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
        rw [heval.symm] at this; exact this
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      exact ⟨runtimeStateMatchesIR_setBothMemory hruntime 0 v hlt, hexact, hbounded⟩

theorem exec_compileStmt_return_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {value : Expr}
    (extraFuel : Nat)
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] (.return value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.return value)
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
  refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      have hlt : v < Verity.Core.Uint256.modulus := by
        have := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
        rw [heval.symm] at this; exact this
      -- Reduce source side
      simp only [SourceSemantics.execStmt, List.length]
      -- Compute the IR execution result
      have hexec : execIRStmts (2 + extraFuel + 1) state
          [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
          .return v { state with memory := fun o => if o = 0 then v else state.memory o } := by
        have : 2 + extraFuel + 1 = Nat.succ (Nat.succ (Nat.succ extraFuel)) := by omega
        rw [this]
        -- Now simp can unfold because fuel is Nat.succ form
        simp only [execIRStmts, execIRStmt, evalIRExpr, evalIRExprs, hIR, Option.bind,
                   ite_true, ite_false]
      set runtime' : SourceSemantics.RuntimeState :=
        { runtime with world := { runtime.world with
            memory := fun o => if o = 0 then Verity.Core.Uint256.ofNat v else runtime.world.memory o } }
      show stmtResultMatchesIRExec fields (.return v runtime') _ ∧
           stmtResultMatchesIRExecExact (.return v runtime') _
      rw [hexec]
      exact ⟨⟨rfl, runtimeStateMatchesIR_setBothMemory hruntime 0 v hlt⟩, hexact, hbounded⟩

theorem exec_compileStmt_stop_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] .stop = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime .stop
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  refine ⟨[YulStmt.expr (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt]
    rfl
  · constructor
    · have hirExec :
          execIRStmts ([YulStmt.expr (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
        simp [execIRStmts]
      rw [SourceSemantics.execStmt, hirExec]
      exact hruntime
    · have hirExec :
          execIRStmts ([YulStmt.expr (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
        simp [execIRStmts]
      rw [SourceSemantics.execStmt, hirExec]
      exact ⟨hexact, hbounded⟩

theorem exec_compileStmt_stop_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (extraFuel : Nat)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] [] .stop = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime .stop
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  refine ⟨[YulStmt.expr (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt]
    rfl
  · have hirExec :
        execIRStmts
          ([YulStmt.expr (YulExpr.call "stop" [])].length + extraFuel + 1)
          state
          [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
      simp [execIRStmts]
    constructor
    · rw [SourceSemantics.execStmt, hirExec]
      exact hruntime
    · rw [SourceSemantics.execStmt, hirExec]
      exact ⟨hexact, hbounded⟩

def scopeNamesPresent (scope : List String) (bindings : List (String × Nat)) : Prop :=
  ∀ name, name ∈ scope → ∃ value, lookupBinding? bindings name = some value

def scopeNamesIncluded
    (scope inScopeNames : List String) : Prop :=
  ∀ name, name ∈ scope → name ∈ inScopeNames

-- exprBoundNamesInScope is now in ExprCore.lean

theorem bindingsExactlyMatchIRVarsOnScope_implies_onExpr
    {scope : List String}
    {expr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hinScope : exprBoundNamesInScope expr scope) :
    bindingsExactlyMatchIRVarsOnExpr expr bindings state := by
  intro name hname
  exact hexact name (hinScope name hname)

theorem eval_compileExpr_core_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope expr scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) :=
  eval_compileExpr_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

theorem evalExpr_lt_evmModulus_core_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope expr scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus :=
  evalExpr_lt_evmModulus_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

theorem eval_compileRequireFailCond_core_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    (hcore : ExprCompileCore cond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent cond runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
      evalIRExpr state failCond =
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)) :=
  eval_compileRequireFailCond_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

theorem bindingsExactlyMatchIRVarsOnScope_of_included
    {scope largerScope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope largerScope bindings state)
    (hincluded : scopeNamesIncluded scope largerScope) :
    bindingsExactlyMatchIRVarsOnScope scope bindings state := by
  intro name hname
  exact hexact name (hincluded name hname)

theorem exprBoundNamesPresent_of_scope
    {expr : Expr}
    {scope : List String}
    {bindings : List (String × Nat)}
    (hscope : scopeNamesPresent scope bindings)
    (hinScope : exprBoundNamesInScope expr scope) :
    exprBoundNamesPresent expr bindings := by
  intro name hname
  exact hscope name (hinScope name hname)

theorem scopeNamesPresent_of_included
    {scope largerScope : List String}
    {bindings : List (String × Nat)}
    (hscope : scopeNamesPresent largerScope bindings)
    (hincluded : scopeNamesIncluded scope largerScope) :
    scopeNamesPresent scope bindings := by
  intro name hname
  exact hscope name (hincluded name hname)

theorem scopeNamesPresent_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {boundName : String}
    {value : Nat}
    (hscope : scopeNamesPresent scope bindings) :
    scopeNamesPresent scope (SourceSemantics.bindValue bindings boundName value) := by
  intro name hmem
  rcases hscope name hmem with ⟨found, hfound⟩
  by_cases hEq : name = boundName
  · subst hEq
    exact ⟨value, lookupBinding?_bindValue_eq bindings name value⟩
  · exact ⟨found, by
      rw [lookupBinding?_bindValue_ne bindings boundName name value hEq, hfound]⟩

theorem scopeNamesPresent_cons_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {boundName : String}
    {value : Nat}
    (hscope : scopeNamesPresent scope bindings) :
    scopeNamesPresent (boundName :: scope) (SourceSemantics.bindValue bindings boundName value) := by
  intro name hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · exact ⟨value, lookupBinding?_bindValue_eq bindings name value⟩
  · exact (scopeNamesPresent_bindValue hscope) name hmem

-- StmtListCompileCore and StmtListTerminalCore are now in ExprCore.lean

theorem stmtListTerminalCore_return_tail_compileCore
    {scope : List String}
    {value : Expr}
    {rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.return value :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | return_ _ _ hrest =>
      exact hrest

theorem stmtListTerminalCore_stop_tail_compileCore
    {scope : List String}
    {rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.stop :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | stop hrest =>
      exact hrest

theorem stmtListTerminalCore_ite_tail_compileCore
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.ite cond thenBranch elseBranch :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | ite _ _ _ _ hrest =>
      exact hrest

theorem stmtListTerminalCore_ne_nil
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    stmts ≠ [] := by
  cases hterminal <;> simp

theorem compileStmt_core_ok_any_scope
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR,
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames [] stmt = Except.ok bodyIR := by
  cases hcore with
  | letVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.let_ name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | assignVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.assign name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | require_ hcond =>
      rename_i cond message
      rcases compileRequireFailCond_core_ok hcond with ⟨failCond, hfailCond⟩
      exact ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)], by
        rw [CompilationModel.compileStmt, hfailCond]
        rfl⟩
  | return_ hvalue =>
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | stop =>
      exact ⟨[YulStmt.expr (YulExpr.call "stop" [])], by
        rw [CompilationModel.compileStmt]
        rfl⟩
  | mstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])], by
        rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
        rfl⟩
  | tstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])], by
        rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
        rfl⟩

/-! ### Scope-independence of compileStmt / compileStmtList success

`compileStmt` uses `inScopeNames` only in `ite` (for `pickFreshName` + recursive
`compileStmtList` on branches) and `forEach` (for recursive `compileStmtList` on body).
Since `pickFreshName` is total and `compileExpr` / all other helpers ignore `inScopeNames`,
compilation success is scope-independent: if it succeeds with one scope, it succeeds
with any other. -/

private theorem compileStmt_ok_any_scope_aux
    (n : Nat)
    (fields : List Field) :
    (∀ (stmt : Stmt) (scope1 scope2 : List String),
      sizeOf stmt < n →
      (∃ ir, CompilationModel.compileStmt fields [] [] .calldata [] false scope1 [] stmt =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmt fields [] [] .calldata [] false scope2 [] stmt =
        Except.ok ir') ∧
    (∀ (stmts : List Stmt) (scope1 scope2 : List String),
      sizeOf stmts < n →
      (∃ ir, CompilationModel.compileStmtList fields [] [] .calldata [] false scope1 [] stmts =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmtList fields [] [] .calldata [] false scope2 [] stmts =
        Except.ok ir') := by
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
                    fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    constructor
    · -- compileStmt part
      intro stmt scope1 scope2 hlt hok
      cases stmt with
      | ite cond thenBranch elseBranch =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcond : CompilationModel.compileExpr fields .calldata cond with
          | error e => simp [hcond] at hir
          | ok condIR =>
            simp only [hcond] at hir ⊢
            cases hthen1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false scope1 [] thenBranch with
            | error e => simp [hthen1] at hir
            | ok thenIR1 =>
              simp only [hthen1] at hir
              cases helse1 : CompilationModel.compileStmtList
                  fields [] [] .calldata [] false scope1 [] elseBranch with
              | error e => simp [helse1] at hir
              | ok elseIR1 =>
                rcases ih.2 thenBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨thenIR1, hthen1⟩
                  with ⟨thenIR2, hthen2⟩
                rcases ih.2 elseBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨elseIR1, helse1⟩
                  with ⟨elseIR2, helse2⟩
                simp only [hthen2, helse2]
                cases elseBranch.isEmpty <;> exact ⟨_, rfl⟩
      | forEach varName count body =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcount : CompilationModel.compileExpr fields .calldata count with
          | error e => simp [hcount] at hir
          | ok countIR =>
            simp only [hcount] at hir ⊢
            cases hbody1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false
                (CompilationModel.forEachBodyScope scope1 varName count body) [] body with
            | error e => simp [hbody1] at hir
            | ok bodyIR1 =>
              rcases ih.2 body (CompilationModel.forEachBodyScope scope1 varName count body)
                  (CompilationModel.forEachBodyScope scope2 varName count body)
                  (by simp [Stmt.forEach.sizeOf_spec] at hlt; omega) ⟨bodyIR1, hbody1⟩
                with ⟨bodyIR2, hbody2⟩
              simp only [hbody2]
              exact ⟨_, rfl⟩
      | unsafeBlock _ body =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt] at hir ⊢
          rcases ih.2 body scope1 scope2
              (by simp [Stmt.unsafeBlock.sizeOf_spec] at hlt; omega) ⟨ir, hir⟩
            with ⟨bodyIR2, hbody2⟩
          exact ⟨bodyIR2, hbody2⟩
      | matchAdt adtName scrutinee branches =>
          rcases hok with ⟨ir, hir⟩
          simp [CompilationModel.compileStmt, lookupAdtTypeDef, Except.bind, bind] at hir
      -- All remaining cases: inScopeNames is unused, so the result is identical
      | letVar | assignVar | setStorage | setStorageAddr | setStorageWord | storageArrayPush
      | storageArrayPop | setStorageArrayElement | setMapping | setMappingWord
      | setMappingPackedWord | setMapping2 | setMapping2Word | setMappingUint
      | setMappingChain | setStructMember | setStructMember2 | require
      | requireError | revertError | «return» | returnValues | returnArray
      | returnBytes | returnStorageWords | returnCodeData | mstore | tstore | calldatacopy
      | returndataCopy | revertReturndata | stop | emit | internalCall
      | internalCallAssign | externalCallBind | tryExternalCallBind | ecm | rawLog
      | unsafeYul =>
          simp only [CompilationModel.compileStmt] at hok ⊢; exact hok
    · -- compileStmtList part
      intro stmts scope1 scope2 hlt hok
      cases stmts with
      | nil => exact ⟨[], rfl⟩
      | cons s ss =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmtList, bind, Except.bind] at hir ⊢
          cases hs1 : CompilationModel.compileStmt
              fields [] [] .calldata [] false scope1 [] s with
          | error e => simp [hs1] at hir
          | ok headIR1 =>
            simp only [hs1] at hir
            cases hss1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false (collectStmtNames s ++ scope1) [] ss with
            | error e => simp [hss1] at hir
            | ok tailIR1 =>
              rcases ih.1 s scope1 scope2 (by simp [List.cons.sizeOf_spec] at hlt; omega)
                  ⟨headIR1, hs1⟩ with ⟨headIR2, hs2⟩
              rcases ih.2 ss (collectStmtNames s ++ scope1) (collectStmtNames s ++ scope2)
                  (by simp [List.cons.sizeOf_spec] at hlt; omega) ⟨tailIR1, hss1⟩
                with ⟨tailIR2, hss2⟩
              simp only [hs2, hss2]
              exact ⟨_, rfl⟩

theorem compileStmt_ok_any_scope
    {fields : List Field}
    {scope1 scope2 : List String}
    {stmt : Stmt}
    (hok : ∃ ir, CompilationModel.compileStmt
      fields [] [] .calldata [] false scope1 [] stmt = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmt
      fields [] [] .calldata [] false scope2 [] stmt = Except.ok ir' :=
  (compileStmt_ok_any_scope_aux (sizeOf stmt + 1) fields).1 stmt scope1 scope2
    (Nat.lt_succ_of_le (Nat.le_refl _)) hok

private theorem compileStmt_ok_any_scope_with_surface_aux
    (n : Nat)
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    (∀ (stmt : Stmt) (scope1 scope2 : List String),
      sizeOf stmt < n →
      (∃ ir, CompilationModel.compileStmt fields events errors .calldata [] false scope1 [] stmt =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmt fields events errors .calldata [] false scope2 [] stmt =
        Except.ok ir') ∧
    (∀ (stmts : List Stmt) (scope1 scope2 : List String),
      sizeOf stmts < n →
      (∃ ir, CompilationModel.compileStmtList fields events errors .calldata [] false scope1 [] stmts =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmtList fields events errors .calldata [] false scope2 [] stmts =
        Except.ok ir') := by
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
                    fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    constructor
    · intro stmt scope1 scope2 hlt hok
      cases stmt with
      | ite cond thenBranch elseBranch =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcond : CompilationModel.compileExpr fields .calldata cond with
          | error e => simp [hcond] at hir
          | ok condIR =>
            simp only [hcond] at hir ⊢
            cases hthen1 : CompilationModel.compileStmtList
                fields events errors .calldata [] false scope1 [] thenBranch with
            | error e => simp [hthen1] at hir
            | ok thenIR1 =>
              simp only [hthen1] at hir
              cases helse1 : CompilationModel.compileStmtList
                  fields events errors .calldata [] false scope1 [] elseBranch with
              | error e => simp [helse1] at hir
              | ok elseIR1 =>
                rcases ih.2 thenBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨thenIR1, hthen1⟩
                  with ⟨thenIR2, hthen2⟩
                rcases ih.2 elseBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨elseIR1, helse1⟩
                  with ⟨elseIR2, helse2⟩
                simp only [hthen2, helse2]
                cases elseBranch.isEmpty <;> exact ⟨_, rfl⟩
      | forEach varName count body =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcount : CompilationModel.compileExpr fields .calldata count with
          | error e => simp [hcount] at hir
          | ok countIR =>
            simp only [hcount] at hir ⊢
            cases hbody1 : CompilationModel.compileStmtList
                fields events errors .calldata [] false
                (CompilationModel.forEachBodyScope scope1 varName count body) [] body with
            | error e => simp [hbody1] at hir
            | ok bodyIR1 =>
              rcases ih.2 body (CompilationModel.forEachBodyScope scope1 varName count body)
                  (CompilationModel.forEachBodyScope scope2 varName count body)
                  (by simp [Stmt.forEach.sizeOf_spec] at hlt; omega) ⟨bodyIR1, hbody1⟩
                with ⟨bodyIR2, hbody2⟩
              simp only [hbody2]
              exact ⟨_, rfl⟩
      | unsafeBlock reason body =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt] at hir ⊢
          exact ih.2 body scope1 scope2
            (by simp [Stmt.unsafeBlock.sizeOf_spec] at hlt; omega)
            ⟨ir, hir⟩
      | matchAdt adtName scrutinee branches =>
          rcases hok with ⟨ir, hir⟩
          simp [CompilationModel.compileStmt, lookupAdtTypeDef, Except.bind, bind] at hir
      | letVar | assignVar | setStorage | setStorageAddr | setStorageWord | storageArrayPush
      | storageArrayPop | setStorageArrayElement | setMapping | setMappingWord
      | setMappingPackedWord | setMapping2 | setMapping2Word | setMappingUint
      | setMappingChain | setStructMember | setStructMember2 | require
      | requireError | revertError | «return» | returnValues | returnArray
      | returnBytes | returnStorageWords | returnCodeData | mstore | tstore | calldatacopy
      | returndataCopy | revertReturndata | stop | emit | internalCall
      | internalCallAssign | externalCallBind | tryExternalCallBind
      | ecm | rawLog | unsafeYul =>
          simp only [CompilationModel.compileStmt] at hok ⊢; exact hok
    · intro stmts scope1 scope2 hlt hok
      cases stmts with
      | nil => exact ⟨[], rfl⟩
      | cons s ss =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmtList, bind, Except.bind] at hir ⊢
          cases hs1 : CompilationModel.compileStmt
              fields events errors .calldata [] false scope1 [] s with
          | error e => simp [hs1] at hir
          | ok headIR1 =>
            simp only [hs1] at hir
            cases hss1 : CompilationModel.compileStmtList
                fields events errors .calldata [] false (collectStmtNames s ++ scope1) [] ss with
            | error e => simp [hss1] at hir
            | ok tailIR1 =>
              rcases ih.1 s scope1 scope2 (by simp [List.cons.sizeOf_spec] at hlt; omega)
                  ⟨headIR1, hs1⟩ with ⟨headIR2, hs2⟩
              rcases ih.2 ss (collectStmtNames s ++ scope1) (collectStmtNames s ++ scope2)
                  (by simp [List.cons.sizeOf_spec] at hlt; omega) ⟨tailIR1, hss1⟩
                with ⟨tailIR2, hss2⟩
              simp only [hs2, hss2]
              exact ⟨_, rfl⟩

theorem compileStmt_ok_any_scope_with_surface
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope1 scope2 : List String}
    {stmt : Stmt}
    (hok : ∃ ir, CompilationModel.compileStmt
      fields events errors .calldata [] false scope1 [] stmt = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmt
      fields events errors .calldata [] false scope2 [] stmt = Except.ok ir' :=
  (compileStmt_ok_any_scope_with_surface_aux (sizeOf stmt + 1) fields events errors).1
    stmt scope1 scope2 (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmtList_ok_any_scope_with_surface
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope1 scope2 : List String}
    {stmts : List Stmt}
    (hok : ∃ ir, CompilationModel.compileStmtList
      fields events errors .calldata [] false scope1 [] stmts = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmtList
      fields events errors .calldata [] false scope2 [] stmts = Except.ok ir' :=
  (compileStmt_ok_any_scope_with_surface_aux (sizeOf stmts + 1) fields events errors).2
    stmts scope1 scope2 (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmtList_ok_any_scope
    {fields : List Field}
    {scope1 scope2 : List String}
    {stmts : List Stmt}
    (hok : ∃ ir, CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope1 [] stmts = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope2 [] stmts = Except.ok ir' :=
  (compileStmt_ok_any_scope_aux (sizeOf stmts + 1) fields).2 stmts scope1 scope2
    (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmtList_cons_ok_of_compileStmt_ok_with_surface
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    {headIR tailIR : List YulStmt}
    (hhead :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] stmt = Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList
        fields events errors .calldata [] false
          (collectStmtNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    CompilationModel.compileStmtList
      fields events errors .calldata [] false inScopeNames [] (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  rw [CompilationModel.compileStmtList, hhead]
  dsimp
  rw [htail]
  rfl

theorem compileStmtList_cons_ok_of_compileStmt_ok
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    {headIR tailIR : List YulStmt}
    (hhead :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames [] stmt = Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  rw [CompilationModel.compileStmtList, hhead]
  dsimp
  rw [htail]
  rfl

theorem compileStmtList_cons_ok_inv
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {adtTypes : List AdtTypeDef}
    {stmt : Stmt}
    {rest : List Stmt}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmtList
        fields events errors .calldata [] false inScopeNames adtTypes (stmt :: rest) =
          Except.ok bodyIR) :
    ∃ headIR tailIR,
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames adtTypes stmt = Except.ok headIR ∧
      CompilationModel.compileStmtList
        fields events errors .calldata [] false
          (collectStmtNames stmt ++ inScopeNames) adtTypes rest = Except.ok tailIR ∧
      bodyIR = headIR ++ tailIR := by
  rw [CompilationModel.compileStmtList] at hcompile
  cases hhead : CompilationModel.compileStmt
      fields events errors .calldata [] false inScopeNames adtTypes stmt with
  | error err =>
      simp [hhead] at hcompile
      cases hcompile
  | ok headIR =>
      cases htail : CompilationModel.compileStmtList
          fields events errors .calldata [] false
            (collectStmtNames stmt ++ inScopeNames) adtTypes rest with
      | error err =>
          simp [hhead, htail] at hcompile
          cases hcompile
      | ok tailIR =>
          simp [hhead, htail] at hcompile
          injection hcompile with hbody
          subst hbody
          refine ⟨headIR, tailIR, ?_, ?_, rfl⟩
          · simpa [hhead]
          · simpa [htail]

theorem compileStmt_terminal_ite_ok_inv
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {bodyIR : List YulStmt}
    (helseNonempty : elseBranch.isEmpty = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames []
          (.ite cond thenBranch elseBranch) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR tempName,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] elseBranch = Except.ok elseIR ∧
      tempName =
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR =
        [YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] := by
  unfold CompilationModel.compileStmt at hcompile
  cases hcond : CompilationModel.compileExpr fields .calldata cond with
  | error err =>
      simp [hcond] at hcompile
      cases hcompile
  | ok condIR =>
      cases hthen : CompilationModel.compileStmtList
          fields [] [] .calldata [] false inScopeNames [] thenBranch with
      | error err =>
          simp [hcond, hthen] at hcompile
          cases hcompile
      | ok thenIR =>
          cases helse : CompilationModel.compileStmtList
              fields [] [] .calldata [] false inScopeNames [] elseBranch with
          | error err =>
              simp [hcond, hthen, helse] at hcompile
              cases hcompile
          | ok elseIR =>
              simp [hcond, hthen, helse, helseNonempty] at hcompile
              refine ⟨condIR, thenIR, elseIR,
                CompilationModel.pickFreshName "__ite_cond"
                  (inScopeNames ++ collectExprNames cond ++
                    collectStmtListNames thenBranch ++ collectStmtListNames elseBranch),
                ?_, ?_, ?_, rfl, ?_⟩
              · simpa [hcond]
              · simpa [hthen]
              · simpa [helse]
              · injection hcompile with hbody
                simpa [List.append_assoc] using hbody.symm

theorem compileStmtList_terminal_ite_ok_inv
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {bodyIR : List YulStmt}
    (helseNonempty : elseBranch.isEmpty = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames []
          (.ite cond thenBranch elseBranch :: rest) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR tailIR tempName,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] elseBranch = Except.ok elseIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames) [] rest =
          Except.ok tailIR ∧
      tempName =
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR =
        [YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++
          tailIR := by
  rcases compileStmtList_cons_ok_inv
      (fields := fields)
      (inScopeNames := inScopeNames)
      (stmt := .ite cond thenBranch elseBranch)
      (rest := rest)
      hcompile with
    ⟨headIR, tailIR, hhead, htail, hbody⟩
  rcases compileStmt_terminal_ite_ok_inv
      (fields := fields)
      (inScopeNames := inScopeNames)
      (cond := cond)
      (thenBranch := thenBranch)
      (elseBranch := elseBranch)
      (bodyIR := headIR)
      helseNonempty
      hhead with
    ⟨condIR, thenIR, elseIR, tempName, hcond, hthen, helse, htemp, hheadIR⟩
  refine ⟨condIR, thenIR, elseIR, tailIR, tempName, hcond, hthen, helse, htail, htemp, ?_⟩
  simpa [hheadIR] using hbody

theorem compileStmtList_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hcore : StmtListCompileCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hcore generalizing inScopeNames
  case nil =>
      exact ⟨[], rfl⟩
  case letVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .letVar name value) (.letVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case assignVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .assignVar name value) (.assignVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case require_ scope cond message rest hcond _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .require cond message) (.require_ hcond) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case return_ scope value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .return value) (.return_ hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.return value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case stop scope rest hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .stop) StmtCompileCore.stop with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.stop) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case mstore scope offset value rest hoffset _ hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .mstore offset value) (.mstore hoffset hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.mstore offset value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case tstore scope offset value rest hoffset _ hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .tstore offset value) (.tstore hoffset hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.tstore offset value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl

theorem compileStmtList_terminal_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hterminal generalizing inScopeNames
  case letVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .letVar name value) (.letVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case assignVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .assignVar name value) (.assignVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case require_ scope cond message rest hcond _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .require cond message) (.require_ hcond) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case return_ scope value rest hvalue _ hrest =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .return value) (.return_ hvalue) with ⟨headIR, hheadIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case stop scope rest hrest =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .stop) StmtCompileCore.stop with ⟨headIR, hheadIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case mstore scope offset value rest hoffset _ hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .mstore offset value) (.mstore hoffset hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.mstore offset value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case tstore scope offset value rest hoffset _ hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .tstore offset value) (.tstore hoffset hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.tstore offset value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case ite scope cond thenBranch elseBranch rest hcond _ hthen helse hrest ihThen ihElse =>
      rcases compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
      rcases ihThen (inScopeNames := inScopeNames) with ⟨thenIR, hthenIR⟩
      rcases ihElse (inScopeNames := inScopeNames) with ⟨elseIR, helseIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil =>
            exfalso
            exact stmtListTerminalCore_ne_nil helse rfl
        | cons =>
            simp
      refine
        ⟨[YulStmt.block [
            YulStmt.let_
              (CompilationModel.pickFreshName "__ite_cond"
                (inScopeNames ++ collectExprNames cond ++
                  collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))
              condIR,
            YulStmt.if_
              (YulExpr.ident
                (CompilationModel.pickFreshName "__ite_cond"
                  (inScopeNames ++ collectExprNames cond ++
                    collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)))
              thenIR,
            YulStmt.if_
              (YulExpr.call "iszero"
                [YulExpr.ident
                  (CompilationModel.pickFreshName "__ite_cond"
                    (inScopeNames ++ collectExprNames cond ++
                      collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))])
              elseIR
          ]] ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList]
      unfold CompilationModel.compileStmt
      rw [hcondIR, hthenIR, helseIR]
      dsimp
      rw [htailIR]
      simp [helseNonempty]
      rfl

theorem compileStmtList_terminal_core_ok_nonempty
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hterminal : StmtListTerminalCore scope stmts)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR) :
    bodyIR ≠ [] := by
  induction hterminal generalizing inScopeNames bodyIR with
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .letVar name value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .assignVar name value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      rcases compileRequireFailCond_core_ok (fields := fields) hcond with ⟨failCond, hfailCond⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .require cond message) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hfailCond] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | return_ hvalue hinScope hrest =>
      rename_i scope value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .return value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | stop hrest =>
      rename_i scope rest
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .stop) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | mstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      rcases compileExpr_core_ok (fields := fields) hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .mstore offset value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | tstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      rcases compileExpr_core_ok (fields := fields) hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .tstore offset value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hoffsetIR, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      rename_i scope cond thenBranch elseBranch rest
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .ite cond thenBranch elseBranch) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil =>
            exfalso
            exact stmtListTerminalCore_ne_nil helse rfl
        | cons =>
            simp
      rcases compileExpr_core_ok (fields := fields) hcond with ⟨condIR', hcondOk⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (scope := scope) (inScopeNames := inScopeNames) (stmts := thenBranch) hthen with
        ⟨thenIR', hthenOk⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (scope := scope) (inScopeNames := inScopeNames) (stmts := elseBranch) helse with
        ⟨elseIR', helseOk⟩
      cases hcondIR : CompilationModel.compileExpr fields .calldata cond with
      | error err =>
          rw [hcondOk] at hcondIR
          cases hcondIR
      | ok condIR =>
          cases hthenIR :
              CompilationModel.compileStmtList
                fields [] [] .calldata [] false inScopeNames [] thenBranch with
          | error err =>
              rw [hthenOk] at hthenIR
              cases hthenIR
          | ok thenIR =>
              cases helseIR :
                  CompilationModel.compileStmtList
                    fields [] [] .calldata [] false inScopeNames [] elseBranch with
              | error err =>
                  rw [helseOk] at helseIR
                  cases helseIR
              | ok elseIR =>
                  simp [CompilationModel.compileStmt, helseNonempty, hcondIR, hthenIR, helseIR] at hhead
                  injection hhead with hheadEq
                  subst hheadEq
                  simp [hbody]

private theorem yulStmtList_length_le_sizeOf : (stmts : List YulStmt) → stmts.length ≤ sizeOf stmts
  | [] => by simp
  | _ :: rest => by
      have hrest := yulStmtList_length_le_sizeOf rest
      simp
      omega

private theorem compiledIteBlockSize_ge_thenBranchLength
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    thenIR.length + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  have hthenLen : thenIR.length ≤ sizeOf thenIR :=
    yulStmtList_length_le_sizeOf thenIR
  simp
  omega

private theorem compiledIteBlockSize_ge_thenBranchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf thenIR + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_thenBranchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf thenIR + 5 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchLength
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    elseIR.length + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  have helseLen : elseIR.length ≤ sizeOf elseIR :=
    yulStmtList_length_le_sizeOf elseIR
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf elseIR + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf elseIR + 5 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

theorem compiled_terminal_ite_body_size_ge_branchFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    thenIR.length + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    elseIR.length + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      thenIR.length + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchLength tempName condIR thenIR elseIR
  have helse :
      elseIR.length + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchLength tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem compiled_terminal_ite_body_size_ge_branchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    sizeOf elseIR + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      sizeOf thenIR + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchSizeOf tempName condIR thenIR elseIR
  have helse :
      sizeOf elseIR + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchSizeOf tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem compiled_terminal_ite_body_size_ge_branchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR + 5 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    sizeOf elseIR + 5 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      sizeOf thenIR + 5 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchExecFuel tempName condIR thenIR elseIR
  have helse :
      sizeOf elseIR + 5 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchExecFuel tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem yulStmtList_sizeOf_cons_ge_tailFuel
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest + 1 ≤ sizeOf (stmt :: rest) := by
  simp
  omega

theorem yulStmtList_sizeOf_cons_extraFuel_eq
    (extraFuel : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt :: rest) + extraFuel =
      sizeOf rest +
        (sizeOf (stmt :: rest) - (sizeOf rest + 1) + extraFuel) + 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt rest
  omega

theorem yulStmtList_sizeOf_cons_tailExecFuel_eq
    (extraFuel : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest +
        (sizeOf (stmt :: rest) - (sizeOf rest + 1) + extraFuel) =
      sizeOf (stmt :: rest) + extraFuel - 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt rest
  omega

theorem yulStmtList_sizeOf_two_cons_extraFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt1 :: stmt2 :: rest) + extraFuel =
      sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) + 1 := by
  have htail : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  omega

theorem yulStmtList_sizeOf_two_cons_secondExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) =
      sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 1 := by
  have htail : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  omega

theorem yulStmtList_sizeOf_two_cons_tail_extraFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) =
      sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) + 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem yulStmtList_sizeOf_two_cons_tailExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) =
      sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 2 := by
  have htail₁ : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  have htail₂ : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem yulStmtList_sizeOf_two_cons_wholeExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt1 :: stmt2 :: rest) + extraFuel =
      sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) + 2 := by
  have htail₁ : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  have htail₂ : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem compiled_terminal_ite_body_size_ge_blockFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] + 2 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  simp
  omega

private theorem execIRStmts_cons_of_execIRStmt_continue
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .continue next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      execIRStmts (rest.length + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .continue next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      execIRStmts (rest.length + extraFuel + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .continue next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      execIRStmts fuel next rest := by
  cases fuel with
  | zero =>
      cases stmt with
      | funcDef name params rets body =>
          have hnext : next = state := by
            simpa [execIRStmt] using hstmt.symm
          subst hnext
          rfl
      | _ =>
          simp [execIRStmt] at hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .continue next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      execIRStmts (fuel + 1) next rest := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_continue_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .continue next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      execIRStmts (sizeOf (stmt :: rest) + extraFuel) next rest := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .continue next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel) next rest := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (irExec : IRExecResult)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .continue next)
    (htail :
      execIRStmts
        (sizeOf rest +
          (sizeOf ([stmt] ++ rest) - (sizeOf rest + 1) + extraFuel) + 1)
        next rest = irExec) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) = irExec := by
  rw [execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt]
  have hfuelEq :
      sizeOf rest +
          (sizeOf ([stmt] ++ rest) - (sizeOf rest + 1) + extraFuel) + 1 =
        sizeOf ([stmt] ++ rest) + extraFuel := by
    simpa using (yulStmtList_sizeOf_cons_extraFuel_eq extraFuel stmt rest).symm
  rw [hfuelEq] at htail
  exact htail

private theorem execIRStmts_cons_of_execIRStmt_return
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .return value next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .return value next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .return value next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .return value next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt fuel state stmt = .return value next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .return value next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt] at hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (fuel + 1) state stmt = .return value next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .return value next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_return_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_return_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .return value next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .return value next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_return_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_return_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .return value next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .return value next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_return_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_stop
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .stop next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .stop next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .stop next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .stop next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .stop next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .stop next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt] at hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .stop next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .stop next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_stop_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_stop_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .stop next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .stop next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_stop_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_stop_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .stop next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .stop next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_stop_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_revert
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .revert next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .revert next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .revert next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .revert next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .revert next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .revert next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt, execIRStmts] at hstmt ⊢ <;> simpa using hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .revert next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .revert next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_revert_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_revert_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .revert next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .revert next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_revert_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .revert next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .revert next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_revert_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_two_of_execIRStmt_continue
    (state mid : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt)
    (hstmt1 : execIRStmt (rest.length + 2) state stmt1 = .continue mid) :
    execIRStmts (rest.length + 3) state (stmt1 :: stmt2 :: rest) =
      execIRStmts (rest.length + 2) mid (stmt2 :: rest) := by
  simp [execIRStmts, hstmt1]

private theorem execIRStmts_two_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state mid : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt)
    (hstmt1 : execIRStmt (rest.length + extraFuel + 2) state stmt1 = .continue mid) :
    execIRStmts (rest.length + extraFuel + 3) state (stmt1 :: stmt2 :: rest) =
      execIRStmts (rest.length + extraFuel + 2) mid (stmt2 :: rest) := by
  simp [execIRStmts, hstmt1]

private theorem execIRStmts_two_of_continue_then_return
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (rest.length + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (rest.length + 1) mid stmt2 = .return value next) :
    execIRStmts (rest.length + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_two_of_execIRStmt_continue state mid stmt1 stmt2 rest hstmt1]
  exact execIRStmts_cons_of_execIRStmt_return mid next stmt2 rest value hstmt2

private theorem execIRStmts_two_of_continue_then_return_extraFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (rest.length + extraFuel + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (rest.length + extraFuel + 1) mid stmt2 = .return value next) :
    execIRStmts (rest.length + extraFuel + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_two_of_execIRStmt_continue_extraFuel extraFuel state mid stmt1 stmt2 rest hstmt1]
  exact execIRStmts_cons_of_execIRStmt_return_extraFuel extraFuel mid next stmt2 rest value hstmt2

private theorem execIRStmts_two_of_continue_then_return_anyFuel
    (fuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt fuel state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (fuel - 1) mid stmt2 = .return value next) :
    execIRStmts (fuel + 1) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel fuel state mid stmt1 (stmt2 :: rest) hstmt1]
  cases fuel with
  | zero =>
      cases stmt2 <;> simp [execIRStmt] at hstmt2
  | succ fuel =>
      simpa using
        (execIRStmts_cons_of_execIRStmt_return_anyFuel fuel mid next stmt2 rest value hstmt2)

private theorem execIRStmts_two_of_continue_then_return_stepFuel
    (fuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (fuel + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (fuel + 1) mid stmt2 = .return value next) :
    execIRStmts (fuel + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_two_of_continue_then_return_anyFuel
      (fuel := fuel + 2)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      (by simpa [Nat.add_assoc] using hstmt2))

private theorem execIRStmts_two_of_continue_then_return_wholeFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 :
      execIRStmt (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel) state stmt1 = .continue mid)
    (hstmt2 :
      execIRStmt (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 1) mid stmt2 =
        .return value next) :
    execIRStmts (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel + 1) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_two_of_continue_then_return_anyFuel
      (fuel := sizeOf (stmt1 :: stmt2 :: rest) + extraFuel)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      hstmt2)

private theorem execIRStmts_two_append_of_continue_then_return_wholeFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 :
      execIRStmt (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel) state stmt1 = .continue mid)
    (hstmt2 :
      execIRStmt (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel - 1) mid stmt2 =
        .return value next) :
    execIRStmts (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel + 1) state ([stmt1, stmt2] ++ rest) =
      .return value next := by
  simpa using
    (execIRStmts_two_of_continue_then_return_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      hstmt2)

private theorem execIRStmt_block_of_execIRStmts_continue
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .continue next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_continue_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .continue next) :
    execIRStmt fuel state (YulStmt.block body) = .continue next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_continue fuel state next body hbody

private theorem execIRStmt_block_of_execIRStmts_return
    (fuel : Nat) (state next : IRState) (body : List YulStmt) (value : Nat)
    (hbody : execIRStmts fuel state body = .return value next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .return value next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_return_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .return value next) :
    execIRStmt fuel state (YulStmt.block body) = .return value next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_return fuel state next body value hbody

private theorem execIRStmt_block_of_execIRStmts_stop
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .stop next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .stop next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .stop next) :
    execIRStmt fuel state (YulStmt.block body) = .stop next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_stop fuel state next body hbody

private theorem execIRStmt_block_of_execIRStmts_revert
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .revert next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .revert next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .revert next) :
    execIRStmt fuel state (YulStmt.block body) = .revert next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_revert fuel state next body hbody

private theorem execIRStmt_if_true_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value ≠ 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = execIRStmts fuel state body := by
  simp [execIRStmt, hcond, hvalue]

private theorem execIRStmt_if_true_of_eval_nonzeroFuel
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value ≠ 0) :
    execIRStmt fuel state (YulStmt.if_ cond body) = execIRStmts (fuel - 1) state body := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_if_true_of_eval fuel state cond body value hcond hvalue

private theorem execIRStmt_if_false_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value = 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = .continue state := by
  simp [execIRStmt, hcond, hvalue]

private theorem execIRStmt_if_false_of_eval_nonzeroFuel
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value = 0) :
    execIRStmt fuel state (YulStmt.if_ cond body) = .continue state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_if_false_of_eval fuel state cond body value hcond hvalue

private theorem execIRStmt_let_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state (YulStmt.let_ name valueExpr) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem execIRStmt_let_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state (YulStmt.let_ name valueExpr) =
      .continue (state.setVar name value) := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_let_of_eval_anyFuel fuel state name valueExpr value heval

private theorem execIRStmt_assign_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state (YulStmt.assign name valueExpr) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem execIRStmt_assign_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state (YulStmt.assign name valueExpr) =
      .continue (state.setVar name value) := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_assign_of_eval_anyFuel fuel state name valueExpr value heval

private theorem execIRStmt_mstore_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue { state with memory := fun o => if o = offset then value else state.memory o } := by
  simp [execIRStmt, evalIRExpr, heval]

private theorem execIRStmt_mstore_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state
      (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue { state with memory := fun o => if o = offset then value else state.memory o } := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_mstore_of_eval_anyFuel fuel state offset valueExpr value heval

private theorem execIRStmt_return32_of_memory_anyFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
      .return (state.memory offset) state := by
  simp [execIRStmt, evalIRExpr]

private theorem execIRStmt_return32_of_memory_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (hfuel : fuel ≠ 0) :
    execIRStmt fuel state
      (YulStmt.expr (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
      .return (state.memory offset) state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_return32_of_memory_anyFuel fuel state offset

private theorem execIRStmt_stop_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (hfuel : fuel ≠ 0) :
    execIRStmt fuel state (YulStmt.expr (YulExpr.call "stop" [])) = .stop state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_stop_succ fuel state

private theorem evalIRExpr_iszero_of_eval
    (state : IRState)
    (expr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "iszero" [expr]) =
      some (if value = 0 then 1 else 0) := by
  simpa [boolWord_eq_if] using evalIRExpr_iszero_of_lt heval hvalueLt

private inductive RevertPrefixStmt : YulStmt → Prop where
  | mstore_lit {offset value : Nat} :
      RevertPrefixStmt (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.lit value]))
  | mstore_hex {offset value : Nat} :
      RevertPrefixStmt (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex value]))

private theorem execIRStmt_revertPrefix_continue
    (fuel : Nat) (state : IRState) {stmt : YulStmt}
    (hstmt : RevertPrefixStmt stmt) :
    ∃ next, execIRStmt (Nat.succ fuel) state stmt = .continue next := by
  cases hstmt with
  | mstore_lit =>
      rename_i offset value
      let next :=
        { state with
          memory := fun o => if o = offset then value else state.memory o }
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]
  | mstore_hex =>
      rename_i offset value
      let next :=
        { state with
          memory := fun o => if o = offset then value else state.memory o }
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]

private theorem execIRStmts_revertPrefix_then_revert
    (fuel : Nat) (state : IRState)
    (prefixStmts : List YulStmt)
    (offset size : Nat)
    (hprefix : ∀ stmt ∈ prefixStmts, RevertPrefixStmt stmt) :
    ∃ next,
      execIRStmts fuel state
        (prefixStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit offset, YulExpr.lit size])]) =
          .revert next := by
  induction fuel generalizing state prefixStmts with
  | zero =>
      cases prefixStmts <;> refine ⟨state, ?_⟩ <;> simp [execIRStmts]
  | succ fuel ih =>
      cases prefixStmts with
      | nil =>
          refine ⟨state, ?_⟩
          cases fuel <;> simp [execIRStmts, execIRStmt]
      | cons stmt rest =>
          have hstmtPred : RevertPrefixStmt stmt := hprefix stmt (by simp)
          cases fuel with
          | zero =>
              cases hstmtPred <;> refine ⟨state, ?_⟩ <;> simp [execIRStmts, execIRStmt]
          | succ fuel =>
              rcases execIRStmt_revertPrefix_continue fuel state hstmtPred with ⟨mid, hstmt⟩
              have hrestPred : ∀ stmt' ∈ rest, RevertPrefixStmt stmt' := by
                intro stmt' hmem
                exact hprefix stmt' (by simp [hmem])
              rcases ih mid rest hrestPred with ⟨next, hrestExec⟩
              refine ⟨next, ?_⟩
              simp [execIRStmts, hstmt, hrestExec]

theorem execIRStmts_revertWithMessage_revert
    (fuel : Nat) (state : IRState) (message : String) :
    ∃ next,
      execIRStmts fuel state (CompilationModel.revertWithMessage message) = .revert next := by
  let bytes := CompilationModel.bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (CompilationModel.chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := CompilationModel.wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  have hprefix : ∀ stmt ∈ header ++ dataStmts, RevertPrefixStmt stmt := by
    intro stmt hmem
    rcases List.mem_append.mp hmem with hhead | hdata
    · simp [header] at hhead
      rcases hhead with rfl | rfl | rfl
      · exact RevertPrefixStmt.mstore_hex
      · exact RevertPrefixStmt.mstore_lit
      · exact RevertPrefixStmt.mstore_lit
    · unfold dataStmts at hdata
      simp only [List.mem_map] at hdata
      rcases hdata with ⟨pair, _, rfl⟩
      exact RevertPrefixStmt.mstore_hex
  simpa [CompilationModel.revertWithMessage, bytes, len, paddedLen, header, dataStmts,
    List.append_assoc] using
    execIRStmts_revertPrefix_then_revert (fuel := fuel) (state := state)
      (prefixStmts := header ++ dataStmts) (offset := 0) (size := 68 + paddedLen) hprefix

theorem exec_compileStmtList_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hcore : StmtListCompileCore scope stmts)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  induction hcore generalizing runtime state inScopeNames with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      constructor
      · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
      · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
          And.intro hexact hbounded
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      -- Get the eval_compileExpr_core result (elaborated via monadic binding)
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      -- Extract the Nat value from the IR evaluation
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · -- evalIRExpr = none: contradicts eval_compileExpr_core
        simp [hIR, Option.bind] at heval
      · -- evalIRExpr = some valueNat
        simp [hIR, Option.bind] at heval
        -- heval : some valueNat = evalExpr fields runtime value, so evalExpr = some valueNat
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
          bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
            hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (tailIR.length + 1) state (YulStmt.let_ name valueIR) =
                .continue state' := by
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + 2) state
                (YulStmt.let_ name valueIR :: tailIR) =
                execIRStmts (tailIR.length + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue state state'
                (YulStmt.let_ name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · simpa [hirExec, runtime'] using htailSem
          · simpa [hirExec, runtime'] using htailExact
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
          bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
            hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (tailIR.length + 1) state (YulStmt.assign name valueIR) =
                .continue state' := by
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + 2) state
                (YulStmt.assign name valueIR :: tailIR) =
                execIRStmts (tailIR.length + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue state state'
                (YulStmt.assign name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · simpa [hirExec, runtime'] using htailSem
          · simpa [hirExec, runtime'] using htailExact
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      -- First, establish that evalExpr cond is some, using eval_compileExpr_core
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core hcond hexact hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        -- Get the fail condition IR
        rcases eval_compileRequireFailCond_core_onExpr hcond
            (bindingsExactlyMatchIRVars_implies_onExpr hexact)
            hbounded hpresent hruntime with
          ⟨failCond, hfailCompile, hfailEval⟩
        rcases ih (runtime := runtime) (state := state)
            (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
            hscope hexact hbounded hruntime with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hfailCompile]
          simp [htailCompile]
          exact rfl
        · rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc]
          by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length) (state := state) message with
              ⟨revState, hrev⟩
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
            have hstmt :
                execIRStmt (tailIR.length + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .revert revState := by
              simp [execIRStmt, hfailEval', hrev]
            have hirExec :
                execIRStmts (tailIR.length + 2) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    .revert revState := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_revert state revState
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
            simp [hzero, hirExec, stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
            have hstmt :
                execIRStmt (tailIR.length + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .continue state := by
              simp [execIRStmt, hfailEval']
            have hirExec :
                execIRStmts (tailIR.length + 2) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    execIRStmts (tailIR.length + 1) state tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue state state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
            simp [hzero, hirExec]
            constructor
            · simpa [hirExec] using htailSem
            · simpa [hirExec] using htailExact
  | return_ hvalue hinScope hrest ih =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      -- Establish that evalExpr value is some, using eval_compileExpr_core
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | retVal
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some retVal :=
          heval.symm
        have hlt : retVal < Verity.Core.Uint256.modulus := by
          have := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime
          rw [hEvalSrc] at this; exact this
        let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
        let runtime' : SourceSemantics.RuntimeState :=
          { runtime with world := { runtime.world with
              memory := fun o => if o = 0 then retVal else runtime.world.memory o } }
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
            hscope
            (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
            hbounded
            (runtimeStateMatchesIR_setBothMemory hruntime 0 retVal hlt) with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setBothMemory hruntime 0 retVal hlt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
          have hmstore :
              execIRStmt (tailIR.length + 2) state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
                .continue state' := by
            simp [execIRStmt, evalIRExpr, hIR, state']
          have hreturn :
              execIRStmt (tailIR.length + 1) state'
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
                .return retVal state' := by
            simp [execIRStmt, evalIRExpr, state']
          have hirExec :
              execIRStmts (tailIR.length + 3)
                state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                  YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                  tailIR) =
                .return retVal state' := by
            simpa using
              (execIRStmts_two_of_continue_then_return state state' state'
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
                tailIR retVal hmstore hreturn)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [state', runtime']
          constructor
          · simpa [hirExec] using (show
              stmtResultMatchesIRExec fields
                (SourceSemantics.StmtResult.return retVal runtime')
                (.return retVal state') from ⟨rfl, hruntime'⟩)
          · simpa [hirExec] using (show
              stmtResultMatchesIRExecExact
                (SourceSemantics.StmtResult.return retVal runtime')
                (.return retVal state') from ⟨hexact', hbounded⟩)
  | stop hrest ih =>
      rename_i scope rest
      rcases ih (runtime := runtime) (state := state)
          (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
          hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem, htailExact⟩
      refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
      · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
      · have hstmt :
            execIRStmt (tailIR.length + 1) state (YulStmt.expr (YulExpr.call "stop" [])) =
              .stop state := by
          simp [execIRStmt]
        have hirExec :
            execIRStmts (tailIR.length + 2) state
              (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
              .stop state := by
          simpa using
            (execIRStmts_cons_of_execIRStmt_stop state state
              (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
        rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
        simp [hirExec]
        exact ⟨hruntime, ⟨hexact, hbounded⟩⟩
  | mstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core hoffset hexact hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core hvalue hexact hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                memory := fun o => if o = offsetNat then valueNat else runtime.world.memory o
              } }
          let state' := { state with memory := fun o => if o = offsetNat then valueNat else state.memory o }
          have hvalueLt := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setBothMemory hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact offsetNat valueNat
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          rcases ih (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.mstore offset value) ++ inScopeNames)
              hscope hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem, htailExact⟩
          refine ⟨[YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (tailIR.length + 1) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) = .continue state' := by
              simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :
                execIRStmts (tailIR.length + 2) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + 1) state' tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue state state'
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) tailIR hstmt)
            rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
            simp [hirExec]
            exact ⟨htailSem, htailExact⟩
  | tstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core hoffset hexact hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core hvalue hexact hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                transientStorage := fun o => if o = offsetNat then valueNat else runtime.world.transientStorage o
              } }
          let state' := { state with transientStorage := fun o => if o = offsetNat then valueNat else state.transientStorage o }
          have hvalueLt := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setTransientStorage hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' := by
            intro name; simpa [IRState.getVar, state'] using hexact name
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          rcases ih (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.tstore offset value) ++ inScopeNames)
              hscope hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem, htailExact⟩
          refine ⟨[YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (tailIR.length + 1) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) = .continue state' := by
              simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :
                execIRStmts (tailIR.length + 2) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + 1) state' tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue state state'
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) tailIR hstmt)
            rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
            simp [hirExec]
            exact ⟨htailSem, htailExact⟩

theorem exec_compileStmtList_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hcore : StmtListCompileCore scope stmts)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  induction hcore generalizing runtime state inScopeNames with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      constructor
      · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
      · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
          And.intro hexact hbounded
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
          bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
            hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.let_ name valueIR) =
                .continue state' := by
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + extraFuel + 2) state
                (YulStmt.let_ name valueIR :: tailIR) =
                execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                (YulStmt.let_ name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.let_ name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailSem
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.let_ name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailExact
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
          bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
            hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.assign name valueIR) =
                .continue state' := by
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + extraFuel + 2) state
                (YulStmt.assign name valueIR :: tailIR) =
                execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                (YulStmt.assign name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.assign name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailSem
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.assign name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailExact
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      -- First, establish that evalExpr cond is some, using eval_compileExpr_core
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core hcond hexact hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        -- Get the fail condition IR
        rcases eval_compileRequireFailCond_core_onExpr hcond
            (bindingsExactlyMatchIRVars_implies_onExpr hexact)
            hbounded hpresent hruntime with
          ⟨failCond, hfailCompile, hfailEval⟩
        rcases ih (runtime := runtime) (state := state)
            (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
            hscope hexact hbounded hruntime with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hfailCompile]
          simp [htailCompile]
          exact rfl
        · rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc]
          by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length + extraFuel)
                (state := state) message with
              ⟨revState, hrev⟩
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
            have hstmt :
                execIRStmt (tailIR.length + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .revert revState := by
              simp [execIRStmt, hfailEval', hrev]
            have hirExec :
                execIRStmts (tailIR.length + extraFuel + 2) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    .revert revState := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_revert_extraFuel extraFuel state revState
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                  hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    .revert revState := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            simp [hzero, hirExec', stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
            have hstmt :
                execIRStmt (tailIR.length + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .continue state := by
              simp [execIRStmt, hfailEval']
            have hirExec :
                execIRStmts (tailIR.length + extraFuel + 2) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                  hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            simp [hzero, hirExec']
            constructor
            · exact htailSem
            · exact htailExact
  | return_ hvalue hinScope hrest ih =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      -- Establish that evalExpr value is some, using eval_compileExpr_core
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | retVal
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some retVal :=
          heval.symm
        have hlt : retVal < Verity.Core.Uint256.modulus := by
          have := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime
          rw [hEvalSrc] at this; exact this
        let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
        let runtime' : SourceSemantics.RuntimeState :=
          { runtime with world := { runtime.world with
              memory := fun o => if o = 0 then retVal else runtime.world.memory o } }
        rcases ih (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
            hscope
            (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
            hbounded
            (runtimeStateMatchesIR_setBothMemory hruntime 0 retVal hlt) with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setBothMemory hruntime 0 retVal hlt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
          have hmstore :
              execIRStmt (tailIR.length + extraFuel + 2) state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
                .continue state' := by
            simp [execIRStmt, evalIRExpr, hIR, state']
          have hreturn :
              execIRStmt (tailIR.length + extraFuel + 1) state'
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
                .return retVal state' := by
            simp [execIRStmt, evalIRExpr, state']
          have hirExec :
              execIRStmts (tailIR.length + extraFuel + 3)
                state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                  YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                  tailIR) =
                .return retVal state' := by
            simpa using
              (execIRStmts_two_of_continue_then_return_extraFuel extraFuel state state' state'
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
                tailIR retVal hmstore hreturn)
          have hirExec' :
              execIRStmts (tailIR.length + 1 + 1 + extraFuel + 1)
                state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                  YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                  tailIR) =
                .return retVal state' := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [state', runtime']
          constructor
          · simpa [hirExec'] using (show
              stmtResultMatchesIRExec fields
                (SourceSemantics.StmtResult.return retVal runtime')
                (.return retVal state') from ⟨rfl, hruntime'⟩)
          · simpa [hirExec'] using (show
              stmtResultMatchesIRExecExact
                (SourceSemantics.StmtResult.return retVal runtime')
                (.return retVal state') from ⟨hexact', hbounded⟩)
  | stop hrest ih =>
      rename_i scope rest
      rcases ih (runtime := runtime) (state := state)
          (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
          hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem, htailExact⟩
      refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
      · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
      · have hstmt :
            execIRStmt (tailIR.length + extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "stop" [])) =
              .stop state := by
          simp [execIRStmt]
        have hirExec :
            execIRStmts (tailIR.length + extraFuel + 2) state
              (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
              .stop state := by
          simpa using
            (execIRStmts_cons_of_execIRStmt_stop_extraFuel extraFuel state state
              (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
        have hirExec' :
            execIRStmts (tailIR.length + 1 + extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
              .stop state := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
        rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
        simp [hirExec']
        exact ⟨hruntime, ⟨hexact, hbounded⟩⟩
  | mstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core hoffset hexact hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core hvalue hexact hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                memory := fun o => if o = offsetNat then valueNat else runtime.world.memory o
              } }
          let state' := { state with memory := fun o => if o = offsetNat then valueNat else state.memory o }
          have hvalueLt := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setBothMemory hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact offsetNat valueNat
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          rcases ih (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.mstore offset value) ++ inScopeNames)
              hscope hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem, htailExact⟩
          refine ⟨[YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (tailIR.length + extraFuel + 1) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) = .continue state' := by
              simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :
                execIRStmts (tailIR.length + extraFuel + 2) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) tailIR hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
            simp [hirExec']
            exact ⟨htailSem, htailExact⟩
  | tstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core hoffset hexact hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core hvalue hexact hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                transientStorage := fun o => if o = offsetNat then valueNat else runtime.world.transientStorage o
              } }
          let state' := { state with transientStorage := fun o => if o = offsetNat then valueNat else state.transientStorage o }
          have hvalueLt := evalExpr_lt_evmModulus_core_onExpr hvalue
            (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setTransientStorage hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' := by
            intro name; simpa [IRState.getVar, state'] using hexact name
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          rcases ih (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.tstore offset value) ++ inScopeNames)
              hscope hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem, htailExact⟩
          refine ⟨[YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (tailIR.length + extraFuel + 1) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) = .continue state' := by
              simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :
                execIRStmts (tailIR.length + extraFuel + 2) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa using
                (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) tailIR hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR]) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
            simp [hirExec']
            exact ⟨htailSem, htailExact⟩

private theorem compiled_terminal_ite_body_block_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 1 =
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR ] + 2) +
          extraFuel) + 1 := by
  have hblock :=
    compiled_terminal_ite_body_size_ge_blockFuel tempName condIR thenIR elseIR tailIR
  omega

private theorem compiled_terminal_ite_body_thenBranch_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 =
      sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) + 1 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseBranch_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 =
      sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) + 1 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_thenBranch_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 := by
  simpa using
    (compiled_terminal_ite_body_thenBranch_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem compiled_terminal_ite_body_thenBranch_tailExecFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 5 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseBranch_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 := by
  simpa using
    (compiled_terminal_ite_body_elseBranch_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem compiled_terminal_ite_body_elseBranch_tailExecFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 5 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_letFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 2 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_thenIfFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 3 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseIfFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 4 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_blockStmtFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel ≠ 0 := by
  have hblock :=
    compiled_terminal_ite_body_size_ge_blockFuel tempName condIR thenIR elseIR tailIR
  omega

private theorem compiled_terminal_ite_body_block_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] +
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
        (sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] + 2) +
        extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 1 := by
  simpa using
    (compiled_terminal_ite_body_block_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem execIRStmt_compiled_terminal_ite_let
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcond : evalIRExpr state condIR = some condValue) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        state
        (YulStmt.let_ tempName condIR) =
      .continue (state.setVar tempName condValue) := by
  simpa using
    execIRStmt_let_of_eval_nonzeroFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (name := tempName)
      (valueExpr := condIR)
      (value := condValue)
      (compiled_terminal_ite_body_letFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      hcond

private theorem evalIRExpr_compiled_terminal_ite_elseCond_of_zero
    (state : IRState)
    (tempName : String)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    evalIRExpr (state.setVar tempName condValue)
      (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hcondZero,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

/-- Entering the taken `then` branch of a compiled terminal `ite` re-expresses
the remaining fuel in the branch-local schema expected by recursive body
simulation proofs. -/
theorem execIRStmt_compiled_terminal_ite_then_branch_entry
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondNonzero : condValue ≠ 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR := by
  have hident :
      evalIRExpr (state.setVar tempName condValue) (YulExpr.ident tempName) = some condValue := by
    simp [evalIRExpr]
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue) thenIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.ident tempName)
        (body := thenIR)
        (value := condValue)
        (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hident
        hcondNonzero
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 4 =
        sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1 := by
    simpa using
      (compiled_terminal_ite_body_thenBranch_execFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue) thenIR := hstep
    _ =
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR := by
          rw [hfuelEq]

private theorem execIRStmt_compiled_terminal_ite_thenIf_false
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      .continue (state.setVar tempName condValue) := by
  have hident :
      evalIRExpr (state.setVar tempName condValue) (YulExpr.ident tempName) = some condValue := by
    simp [evalIRExpr]
  simpa using
    execIRStmt_if_false_of_eval_nonzeroFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 3)
      (state := state.setVar tempName condValue)
      (cond := YulExpr.ident tempName)
      (body := thenIR)
      (value := condValue)
      (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      hident
      hcondZero

/-- Entering the taken `else` branch of a compiled terminal `ite` still has one
token available for the branch body itself, so the resulting branch-local fuel
keeps the trailing `+ 1`. -/
theorem execIRStmt_compiled_terminal_ite_else_branch_entry
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) elseIR := by
  have hiszero :
      evalIRExpr (state.setVar tempName condValue)
        (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 :=
    evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue) elseIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.call "iszero" [YulExpr.ident tempName])
        (body := elseIR)
        (value := 1)
        (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hiszero
        (by decide)
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 4 =
        sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1 := by
    simpa using
      (compiled_terminal_ite_body_elseBranch_execFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue) elseIR := hstep
    _ =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) elseIR := by
          rw [hfuelEq]

/-- Entering the taken `else` branch after the outer `if` token has already been
spent re-expresses the remaining fuel in the smaller branch-local schema needed
by the Layer 2 terminal-body induction. -/
theorem execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR := by
  have hiszero :
      evalIRExpr (state.setVar tempName condValue)
        (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 :=
    evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 5)
          (state.setVar tempName condValue) elseIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.call "iszero" [YulExpr.ident tempName])
        (body := elseIR)
        (value := 1)
        (compiled_terminal_ite_body_elseIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hiszero
        (by decide)
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 5 =
        sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) := by
    simpa using
      (compiled_terminal_ite_body_elseBranch_tailExecFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 5)
        (state.setVar tempName condValue) elseIR := hstep
    _ =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR := by
          rw [hfuelEq]

private theorem execIRStmts_compiled_terminal_ite_then_of_irExec
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondNonzero : condValue ≠ 0)
    (hthenExec :
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) = irExec := by
  have hlet :=
    execIRStmt_compiled_terminal_ite_let
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcond
  have hthenStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) = irExec := by
    rw [execIRStmt_compiled_terminal_ite_then_branch_entry
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondNonzero]
    exact hthenExec
  have hafterLet :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        (state.setVar tempName condValue)
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .return value next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_return_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            (value := value)
            hthenStmt')
    · rename_i next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .stop next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_stop_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            hthenStmt')
    · rename_i next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .revert next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_revert_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            hthenStmt')
  have hinner :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1)
        state
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 2) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.let_ tempName condIR)
      (rest :=
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
      hlet]
    exact hafterLet
  have hblock :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel)
        state
        (YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) = irExec := by
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .return value next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_return_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (value := value)
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .stop next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .revert next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
  cases hir : irExec
  · rename_i next
    exact False.elim (hirNoContinue next hir)
  · rename_i value next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .return value next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_return_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
          (value := value)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .stop next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_stop_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .revert next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_revert_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')

private theorem execIRStmts_compiled_terminal_ite_else_of_irExec
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondZero : condValue = 0)
    (helseExec :
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) = irExec := by
  have hlet :=
    execIRStmt_compiled_terminal_ite_let
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcond
  have hthenStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      .continue (state.setVar tempName condValue) := by
    exact execIRStmt_compiled_terminal_ite_thenIf_false
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero
  have helseStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) = irExec := by
    rw [execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero]
    exact helseExec
  have hafterThen :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        (state.setVar tempName condValue)
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 3)
      (state := state.setVar tempName condValue)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
      (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
      hthenStmt]
    have hfuelEq' :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
      omega
    rw [hfuelEq']
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .return value next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_return_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            (value := value)
            helseStmt')
    · rename_i next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .stop next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_stop_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            helseStmt')
    · rename_i next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .revert next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_revert_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            helseStmt')
  have hinner :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1)
        state
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 2) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.let_ tempName condIR)
      (rest :=
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
      hlet]
    exact hafterThen
  have hblock :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel)
        state
        (YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) = irExec := by
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .return value next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_return_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (value := value)
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .stop next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .revert next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
  cases hir : irExec
  · rename_i next
    exact False.elim (hirNoContinue next hir)
  · rename_i value next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .return value next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_return_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
          (value := value)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .stop next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_stop_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .revert next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_revert_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')

theorem execStmtList_terminal_core_not_continue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∀ next, SourceSemantics.execStmtList fields runtime stmts ≠ .continue next := by
  induction hterminal generalizing runtime with
  | letVar hvalue hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | assignVar hvalue hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | require_ hcond hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases heval : SourceSemantics.evalExpr fields runtime _ with
      | none => simp
      | some resolved =>
          simp only [heval]
          by_cases hne : resolved != 0 <;> simp_all
  | return_ hvalue hinScope hrest =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp
  | stop hrest =>
      intro next
      simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  | mstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | tstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | ite hcond hinScope hthen helse hrest ih_then ih_else =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases heval : SourceSemantics.evalExpr fields runtime _ with
      | none => simp
      | some resolved =>
          simp only [heval]
          by_cases hne : resolved != 0
          · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
            have hbranch := ih_then (runtime := runtime)
            cases hexec : SourceSemantics.execStmtList fields runtime _ with
            | «continue» next' => exact absurd hexec (hbranch next')
            | stop _ | «return» _ _ | revert => simp [hexec]
          · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
            have hbranch := ih_else (runtime := runtime)
            cases hexec : SourceSemantics.execStmtList fields runtime _ with
            | «continue» next' => exact absurd hexec (hbranch next')
            | stop _ | «return» _ _ | revert => simp [hexec]

theorem stmtResultMatchesIRExec_ir_not_continue_of_source_not_continue
    {fields : List Field}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hsourceNoContinue : ∀ next, sourceResult ≠ .continue next)
    (hmatch : stmtResultMatchesIRExec fields sourceResult irExec) :
    ∀ next, irExec ≠ .continue next := by
  intro next hcontinue
  cases sourceResult <;> cases irExec <;> simp [stmtResultMatchesIRExec] at hmatch hcontinue
  rename_i runtime state
  exact hsourceNoContinue runtime rfl

theorem stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {stmts : List Stmt}
    {irExec : IRExecResult}
    (hterminal : StmtListTerminalCore scope stmts)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime stmts)
        irExec) :
    ∀ next, irExec ≠ .continue next := by
  exact stmtResultMatchesIRExec_ir_not_continue_of_source_not_continue
    (fields := fields)
    (sourceResult := SourceSemantics.execStmtList fields runtime stmts)
    (irExec := irExec)
    (execStmtList_terminal_core_not_continue
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := stmts)
      hterminal)
    hmatch

theorem execStmtList_terminal_core_ite_then_eq
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {condValue : Nat}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondTrue : condValue != 0) :
    SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
      SourceSemantics.execStmtList fields runtime thenBranch := by
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondEval, hcondTrue, ↓reduceIte]
  cases hthenExec : SourceSemantics.execStmtList fields runtime thenBranch <;> simp [hthenExec]
  rename_i next
  exact False.elim <|
    execStmtList_terminal_core_not_continue
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := thenBranch)
      hthen next hthenExec

theorem execStmtList_terminal_core_ite_else_eq
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {condValue : Nat}
    (helse : StmtListTerminalCore scope elseBranch)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondFalse : (condValue != 0) = false) :
    SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
      SourceSemantics.execStmtList fields runtime elseBranch := by
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondEval, hcondFalse, ↓reduceIte]
  cases helseExec : SourceSemantics.execStmtList fields runtime elseBranch <;> simp [helseExec]
  rename_i next
  exact False.elim <|
    execStmtList_terminal_core_not_continue
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := elseBranch)
      helse next helseExec

theorem stmtResultMatchesIRExec_compiled_terminal_ite_then
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {extraFuel : Nat}
    {tempName : String}
    {condIR : YulExpr}
    {thenIR elseIR tailIR : List YulStmt}
    {condValue : Nat}
    {sourceCondValue : Nat}
    {irExec : IRExecResult}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime thenBranch)
        irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondTrue : sourceCondValue != 0)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondNonzero : condValue ≠ 0)
    (hthenExec :
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR = irExec) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR)) := by
  have hirNoContinue :
      ∀ next, irExec ≠ .continue next := by
    exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := thenBranch)
      (irExec := irExec)
      hthen
      hmatch
  have hsourceEq :
      SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
        SourceSemantics.execStmtList fields runtime thenBranch :=
    execStmtList_terminal_core_ite_then_eq
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (cond := cond)
      (thenBranch := thenBranch)
      (elseBranch := elseBranch)
      (rest := rest)
      (condValue := sourceCondValue)
      hthen
      hcondEval
      hcondTrue
  have hirEq :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) =
      irExec :=
    execIRStmts_compiled_terminal_ite_then_of_irExec
      extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
      hcond hcondNonzero hthenExec hirNoContinue
  rw [hsourceEq, hirEq]
  exact hmatch

theorem stmtResultMatchesIRExec_compiled_terminal_ite_else
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {extraFuel : Nat}
    {tempName : String}
    {condIR : YulExpr}
    {thenIR elseIR tailIR : List YulStmt}
    {condValue : Nat}
    {sourceCondValue : Nat}
    {irExec : IRExecResult}
    (helse : StmtListTerminalCore scope elseBranch)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime elseBranch)
        irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondFalse : (sourceCondValue != 0) = false)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondZero : condValue = 0)
    (helseExec :
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR = irExec) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR)) := by
  have hirNoContinue :
      ∀ next, irExec ≠ .continue next := by
    exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := elseBranch)
      (irExec := irExec)
      helse
      hmatch
  have hsourceEq :
      SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
        SourceSemantics.execStmtList fields runtime elseBranch :=
    execStmtList_terminal_core_ite_else_eq
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (cond := cond)
      (thenBranch := thenBranch)
      (elseBranch := elseBranch)
      (rest := rest)
      (condValue := sourceCondValue)
      helse
      hcondEval
      hcondFalse
  have hirEq :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) =
      irExec :=
    execIRStmts_compiled_terminal_ite_else_of_irExec
      extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
      hcond hcondZero helseExec hirNoContinue
  rw [hsourceEq, hirEq]
  exact hmatch

theorem execIRStmts_compiled_return_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {value : Expr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    let retVal := (SourceSemantics.evalExpr fields runtime value).getD 0
    let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
    ∃ valueIR,
      CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
      execIRStmts
        (sizeOf
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel + 1)
        state
        ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR) =
        .return retVal state' := by
  rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
  have heval := eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
    have hRetVal : (SourceSemantics.evalExpr fields runtime value).getD 0 = v := by
      rw [hEvalSrc]; rfl
    rw [hRetVal]
    set retVal := v
    set state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
    have hmstoreFuelNeZero :
        sizeOf
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel ≠ 0 := by
      have hprefixLen :
          2 ≤
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR).length := by
        simp
      have hlen :
          ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
            tailIR).length ≤
            sizeOf
              ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                tailIR) := by
        exact yulStmtList_length_le_sizeOf _
      omega
    have hreturnFuelNeZero :
        sizeOf
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel - 1 ≠ 0 := by
      have hprefixLen :
          2 ≤
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR).length := by
        simp
      have hlen :
          ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
            tailIR).length ≤
            sizeOf
              ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                tailIR) := by
        exact yulStmtList_length_le_sizeOf _
      omega
    have hmstore :
        execIRStmt
            (sizeOf
                ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                 , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                  tailIR) + extraFuel)
            state
            (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
          .continue state' := by
      simpa [state'] using
        execIRStmt_mstore_of_eval_nonzeroFuel
          (fuel :=
            sizeOf
              ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                tailIR) + extraFuel)
          (state := state)
          (offset := 0)
          (valueExpr := valueIR)
          (value := retVal)
          hmstoreFuelNeZero
          hIR
    have hreturn :
        execIRStmt
            (sizeOf
                ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                 , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                  tailIR) + extraFuel - 1)
            state'
            (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
          .return retVal state' := by
      simpa [state', retVal] using
        execIRStmt_return32_of_memory_nonzeroFuel
          (fuel :=
            sizeOf
              ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                tailIR) + extraFuel - 1)
          (state := state')
          (offset := 0)
          hreturnFuelNeZero
    refine ⟨valueIR, hvalueIR, ?_⟩
    exact execIRStmts_two_append_of_continue_then_return_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (mid := state')
      (next := state')
      (stmt1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
      (stmt2 := YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
      (rest := tailIR)
      (value := retVal)
      hmstore
      hreturn

theorem execIRStmts_compiled_stop_core_append_wholeFuel
    {state : IRState}
    {tailIR : List YulStmt}
    {extraFuel : Nat} :
    execIRStmts
      (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) =
      .stop state := by
  have hstopFuelNeZero :
      sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel ≠ 0 := by
    have hprefixLen :
        1 ≤ ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR).length := by
      simp
    have hlen :
        ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR).length ≤
          sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) := by
      exact yulStmtList_length_le_sizeOf _
    omega
  have hstop :
      execIRStmt
          (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
          state
          (YulStmt.expr (YulExpr.call "stop" [])) =
        .stop state := by
    exact execIRStmt_stop_nonzeroFuel
      (fuel := sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
      (state := state)
      hstopFuelNeZero
  exact execIRStmts_singleton_append_of_execIRStmt_stop_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.expr (YulExpr.call "stop" []))
    (rest := tailIR)
    hstop

private theorem sizeOf_singleton_append_extraFuel_ne_zero
    (stmt : YulStmt)
    (tailIR : List YulStmt)
    (extraFuel : Nat) :
    sizeOf ([stmt] ++ tailIR) + extraFuel ≠ 0 := by
  have hprefixLen : 1 ≤ ([stmt] ++ tailIR).length := by
    simp
  have hlen : ([stmt] ++ tailIR).length ≤ sizeOf ([stmt] ++ tailIR) := by
    exact yulStmtList_length_le_sizeOf _
  omega

theorem execIRStmts_compiled_let_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    ∃ valueIR,
      CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
      execIRStmts
        (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.let_ name valueIR] ++ tailIR) =
        execIRStmts
          (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
          state'
          tailIR ∧
      runtimeStateMatchesIR fields runtime' state' ∧
      bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
      bindingsBounded runtime'.bindings ∧
      scopeNamesPresent (name :: scope) runtime'.bindings := by
  rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
  have hpresent : exprBoundNamesPresent value runtime.bindings :=
    exprBoundNamesPresent_of_scope hscope hinScope
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  have heval :=
    eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp only [Except.toOption] at heval
  have heval' : evalIRExpr state valueIR = some valueNat := by
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [hValueEval] at heval
      simpa using heval
  have hvalueLt :=
    evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hValueEval] at hvalueLt; simp at hvalueLt
  have hstmt :
      execIRStmt
        (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
        state
        (YulStmt.let_ name valueIR) =
      .continue state' := by
    exact execIRStmt_let_of_eval_nonzeroFuel
      (fuel := sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
      (state := state)
      (name := name)
      (valueExpr := valueIR)
      (value := valueNat)
      (sizeOf_singleton_append_extraFuel_ne_zero
        (stmt := YulStmt.let_ name valueIR)
        (tailIR := tailIR)
        (extraFuel := extraFuel))
      heval'
  refine ⟨valueIR, hvalueIR, ?_, ?_⟩
  · exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := state')
      (stmt := YulStmt.let_ name valueIR)
      (rest := tailIR)
      hstmt
  · refine ⟨runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat, ?_⟩
    refine ⟨bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact, ?_⟩
    exact ⟨bindingsBounded_bindValue hbounded name valueNat hvalueLt,
      scopeNamesPresent_cons_bindValue hscope⟩

theorem execIRStmts_compiled_let_core_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {irExec : IRExecResult}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat)
    (htail :
      execIRStmts
        (sizeOf tailIR +
          (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
            (sizeOf tailIR + 1) +
            extraFuel) + 1)
        (state.setVar name valueNat)
        tailIR = irExec) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    execIRStmts
      (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.let_ name valueIR] ++ tailIR) = irExec ∧
    runtimeStateMatchesIR fields runtime' state' ∧
    bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
    bindingsBounded runtime'.bindings ∧
    scopeNamesPresent (name :: scope) runtime'.bindings := by
  rcases execIRStmts_compiled_let_core_append_wholeFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (name := name)
      (value := value)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      hcore hexact hinScope hscope hbounded hruntime hValueEval with
    ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
  rw [hvalueIR] at hvalueIR'
  injection hvalueIR' with hEq
  subst hEq
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
  exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := state')
      (stmt := YulStmt.let_ name valueIR)
      (rest := tailIR)
      (irExec := irExec)
      (by
        have hpresent : exprBoundNamesPresent value runtime.bindings :=
          exprBoundNamesPresent_of_scope hscope hinScope
        have heval :=
          eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
        rw [hvalueIR] at heval
        simp only [Except.toOption] at heval
        have heval' : evalIRExpr state valueIR = some valueNat := by
          rcases hIR : evalIRExpr state valueIR with _ | v
          · simp [hIR, Option.bind] at heval
          · simp [hIR, Option.bind] at heval
            rw [hValueEval] at heval
            simpa using heval
        exact execIRStmt_let_of_eval_nonzeroFuel
          (fuel := sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
          (state := state)
          (name := name)
          (valueExpr := valueIR)
          (value := valueNat)
          (sizeOf_singleton_append_extraFuel_ne_zero
            (stmt := YulStmt.let_ name valueIR)
            (tailIR := tailIR)
            (extraFuel := extraFuel))
          heval')
      htail

theorem execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    ∃ valueIR,
      CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
      execIRStmts
        (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.assign name valueIR] ++ tailIR) =
        execIRStmts
          (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
          state'
          tailIR ∧
      runtimeStateMatchesIR fields runtime' state' ∧
      bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
      bindingsBounded runtime'.bindings ∧
      scopeNamesPresent (name :: scope) runtime'.bindings := by
  rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
  have hpresent : exprBoundNamesPresent value runtime.bindings :=
    exprBoundNamesPresent_of_scope hscope hinScope
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  have heval :=
    eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval; simp only [Except.toOption] at heval
  have heval' : evalIRExpr state valueIR = some valueNat := by
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [hValueEval] at heval
      simpa using heval
  have hvalueLt :=
    evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hValueEval] at hvalueLt; simp at hvalueLt
  have hstmt :
      execIRStmt
        (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
        state
        (YulStmt.assign name valueIR) =
      .continue state' := by
    exact execIRStmt_assign_of_eval_nonzeroFuel
      (fuel := sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
      (state := state)
      (name := name)
      (valueExpr := valueIR)
      (value := valueNat)
      (sizeOf_singleton_append_extraFuel_ne_zero
        (stmt := YulStmt.assign name valueIR)
        (tailIR := tailIR)
        (extraFuel := extraFuel))
      heval'
  refine ⟨valueIR, hvalueIR, ?_, ?_⟩
  · exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := state')
      (stmt := YulStmt.assign name valueIR)
      (rest := tailIR)
      hstmt
  · refine ⟨runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat, ?_⟩
    refine ⟨bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact, ?_⟩
    exact ⟨bindingsBounded_bindValue hbounded name valueNat hvalueLt,
      scopeNamesPresent_cons_bindValue hscope⟩

theorem execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {irExec : IRExecResult}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat)
    (htail :
      execIRStmts
        (sizeOf tailIR +
          (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
            (sizeOf tailIR + 1) +
            extraFuel) + 1)
        (state.setVar name valueNat)
        tailIR = irExec) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    execIRStmts
      (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.assign name valueIR] ++ tailIR) = irExec ∧
    runtimeStateMatchesIR fields runtime' state' ∧
    bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
    bindingsBounded runtime'.bindings ∧
    scopeNamesPresent (name :: scope) runtime'.bindings := by
  rcases execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (name := name)
      (value := value)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      hcore hexact hinScope hscope hbounded hruntime hValueEval with
    ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
  rw [hvalueIR] at hvalueIR'
  injection hvalueIR' with hEq
  subst hEq
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
  exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := state')
      (stmt := YulStmt.assign name valueIR)
      (rest := tailIR)
      (irExec := irExec)
      (by
        have hpresent : exprBoundNamesPresent value runtime.bindings :=
          exprBoundNamesPresent_of_scope hscope hinScope
        have heval :=
          eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
        rw [hvalueIR] at heval
        simp only [Except.toOption] at heval
        have heval' : evalIRExpr state valueIR = some valueNat := by
          rcases hIR : evalIRExpr state valueIR with _ | v
          · simp [hIR, Option.bind] at heval
          · simp [hIR, Option.bind] at heval
            rw [hValueEval] at heval
            simpa using heval
        exact execIRStmt_assign_of_eval_nonzeroFuel
          (fuel := sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
          (state := state)
          (name := name)
          (valueExpr := valueIR)
          (value := valueNat)
          (sizeOf_singleton_append_extraFuel_ne_zero
            (stmt := YulStmt.assign name valueIR)
            (tailIR := tailIR)
            (extraFuel := extraFuel))
          heval')
      htail

theorem execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {condValue : Nat}
    (hcore : ExprCompileCore cond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondNeZero : condValue ≠ 0) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
      execIRStmts
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) =
        execIRStmts
          (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
          state
          tailIR := by
  have hpresent : exprBoundNamesPresent cond runtime.bindings :=
    exprBoundNamesPresent_of_scope hscope hinScope
  rcases eval_compileRequireFailCond_core_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (cond := cond)
      hcore hexact hinScope hbounded hpresent hruntime with
    ⟨failCond, hfailCompile, hfailEval⟩
  have hfailEval' : evalIRExpr state failCond = some 0 := by
    have hdecideFalse : decide (SourceSemantics.evalExpr fields runtime cond = some 0) = false := by
      simp [hcondEval, hcondNeZero]
    simpa [SourceSemantics.boolWord, hdecideFalse] using hfailEval
  have hstmt :
      execIRStmt
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
        state
        (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
      .continue state := by
    exact execIRStmt_if_false_of_eval_nonzeroFuel
      (fuel :=
        sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
      (state := state)
      (cond := failCond)
      (body := CompilationModel.revertWithMessage message)
      (value := 0)
      (sizeOf_singleton_append_extraFuel_ne_zero
        (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
        (tailIR := tailIR)
        (extraFuel := extraFuel))
      hfailEval'
      rfl
  refine ⟨failCond, hfailCompile, ?_⟩
  exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
    (rest := tailIR)
    hstmt

theorem execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {failCond : YulExpr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {irExec : IRExecResult}
    {condValue : Nat}
    (hcore : ExprCompileCore cond)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondNeZero : condValue ≠ 0)
    (htail :
      execIRStmts
        (sizeOf tailIR +
          (sizeOf
              ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
            (sizeOf tailIR + 1) +
            extraFuel) + 1)
        state
        tailIR = irExec) :
    execIRStmts
      (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) = irExec := by
  rcases execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (cond := cond)
      (message := message)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      hcore hexact hinScope hscope hbounded hruntime hcondEval hcondNeZero with
    ⟨failCond', hfailCompile', hwhole⟩
  rw [hfailCompile] at hfailCompile'
  injection hfailCompile' with hEq
  subst hEq
  exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
    (rest := tailIR)
    (irExec := irExec)
    (by
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases eval_compileRequireFailCond_core_of_scope
          (fields := fields)
          (runtime := runtime)
          (state := state)
          (scope := scope)
          (cond := cond)
          hcore hexact hinScope hbounded hpresent hruntime with
        ⟨failCond', hfailCompile', hfailEval⟩
      rw [hfailCompile] at hfailCompile'
      injection hfailCompile' with hEq
      subst hEq
      have hfailEval' : evalIRExpr state failCond = some 0 := by
        have hdecideFalse : decide (SourceSemantics.evalExpr fields runtime cond = some 0) = false := by
          simp [hcondEval, hcondNeZero]
        simpa [SourceSemantics.boolWord, hdecideFalse] using hfailEval
      exact execIRStmt_if_false_of_eval_nonzeroFuel
        (fuel :=
          sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
        (state := state)
        (cond := failCond)
        (body := CompilationModel.revertWithMessage message)
        (value := 0)
        (sizeOf_singleton_append_extraFuel_ne_zero
          (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
          (tailIR := tailIR)
          (extraFuel := extraFuel))
        hfailEval'
        rfl)
    htail

theorem execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hcore : ExprCompileCore cond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondZero : SourceSemantics.evalExpr fields runtime cond = some 0) :
    ∃ failCond revState,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
      execIRStmts
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) =
        .revert revState := by
  have hpresent : exprBoundNamesPresent cond runtime.bindings :=
    exprBoundNamesPresent_of_scope hscope hinScope
  rcases eval_compileRequireFailCond_core_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (cond := cond)
      hcore hexact hinScope hbounded hpresent hruntime with
    ⟨failCond, hfailCompile, hfailEval⟩
  rcases execIRStmts_revertWithMessage_revert
      (fuel := sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel - 1)
      (state := state)
      message with
    ⟨revState, hrev⟩
  have hfailEval' : evalIRExpr state failCond = some 1 := by
    simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
  have hstmt :
      execIRStmt
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
        state
        (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
      .revert revState := by
    rw [execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
        (state := state)
        (cond := failCond)
        (body := CompilationModel.revertWithMessage message)
        (value := 1)
        (sizeOf_singleton_append_extraFuel_ne_zero
          (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
          (tailIR := tailIR)
          (extraFuel := extraFuel))
        hfailEval'
        (by decide : (1 : Nat) ≠ 0)]
    simpa using hrev
  refine ⟨failCond, revState, hfailCompile, ?_⟩
  exact execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := revState)
    (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
    (rest := tailIR)
    hstmt

theorem stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat)
    (htail :
      let runtime' :=
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
      stmtResultMatchesIRExec
        fields
        (SourceSemantics.execStmtList fields runtime' rest)
        (execIRStmts
          (sizeOf tailIR +
            (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          (state.setVar name valueNat)
          tailIR)) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.letVar name value :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.let_ name valueIR] ++ tailIR)) := by
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  rcases execIRStmts_compiled_let_core_tailExtraFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (name := name)
      (value := value)
      (valueIR := valueIR)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      (irExec :=
        execIRStmts
          (sizeOf tailIR +
            (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          state'
          tailIR)
      hcore hvalueIR hexact hinScope hscope hbounded hruntime hValueEval rfl with
    ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  simp only [hValueEval]
  rw [hwhole]
  exact htail

theorem stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat)
    (htail :
      let runtime' :=
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
      stmtResultMatchesIRExec
        fields
        (SourceSemantics.execStmtList fields runtime' rest)
        (execIRStmts
          (sizeOf tailIR +
            (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          (state.setVar name valueNat)
          tailIR)) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.assignVar name value :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.assign name valueIR] ++ tailIR)) := by
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  rcases execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (name := name)
      (value := value)
      (valueIR := valueIR)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      (irExec :=
        execIRStmts
          (sizeOf tailIR +
            (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          state'
          tailIR)
      hcore hvalueIR hexact hinScope hscope hbounded hruntime hValueEval rfl with
    ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  simp only [hValueEval]
  rw [hwhole]
  exact htail

theorem stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {failCond : YulExpr}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {condValue : Nat}
    (hcore : ExprCompileCore cond)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondNeZero : condValue ≠ 0)
    (htail :
      stmtResultMatchesIRExec
        fields
        (SourceSemantics.execStmtList fields runtime rest)
        (execIRStmts
          (sizeOf tailIR +
            (sizeOf
                ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          state
          tailIR)) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.require cond message :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) +
          extraFuel + 1)
        state
        ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)) := by
  have hwhole :=
    execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (cond := cond)
      (message := message)
      (failCond := failCond)
      (tailIR := tailIR)
      (extraFuel := extraFuel)
      (irExec :=
        execIRStmts
          (sizeOf tailIR +
            (sizeOf
                ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
              (sizeOf tailIR + 1) +
              extraFuel) + 1)
          state
          tailIR)
      hcore hfailCompile hexact hinScope hscope hbounded hruntime hcondEval hcondNeZero rfl
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  simp only [hcondEval, show (condValue != 0) = true from by simp [hcondNeZero]]
  rw [hwhole]
  exact htail

theorem stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {value : Expr}
    {valueIR : YulExpr}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.return value :: rest))
      (execIRStmts
        (sizeOf
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel + 1)
        state
        ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR)) := by
  -- Use the execution theorem to rewrite the IR side
  rcases execIRStmts_compiled_return_core_append_wholeFuel_of_scope
    hcore hexact hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    (tailIR := tailIR) (extraFuel := extraFuel) with ⟨valueIR', hvalueIR', hexec⟩
  -- valueIR' must equal valueIR
  rw [hvalueIR] at hvalueIR'
  cases hvalueIR'
  rw [hexec]
  -- Now reduce the source side
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  -- Get the evaluation bridge
  have heval := eval_compileExpr_core_of_scope hcore hexact hinScope hbounded
    (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rw [hvalueIR] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
    -- Source = .return v runtime', IR = .return retVal state'
    -- retVal = (some v).getD 0 = v
    have hRetVal : (some v).getD 0 = v := rfl
    have hlt : v < Verity.Core.Uint256.modulus := by
      have := evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded
        (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm] at this
      exact this
    simp only [hRetVal, stmtResultMatchesIRExec]
    exact ⟨trivial, runtimeStateMatchesIR_setBothMemory hruntime 0 v hlt⟩

theorem stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.stop :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR)) := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  rw [execIRStmts_compiled_stop_core_append_wholeFuel
    (state := state)
    (tailIR := tailIR)
    (extraFuel := extraFuel)]
  exact hruntime

theorem scopeNamesIncluded_refl
    {scope : List String} :
    scopeNamesIncluded scope scope := by
  intro name hname
  exact hname

theorem scopeNamesIncluded_append_right
    {scope left right : List String}
    (hincluded : scopeNamesIncluded scope right) :
    scopeNamesIncluded scope (left ++ right) := by
  intro name hname
  exact List.mem_append.mpr <| Or.inr (hincluded name hname)

theorem scopeNamesIncluded_collectStmtNames_tail
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope (collectStmtNames stmt ++ inScopeNames) := by
  exact scopeNamesIncluded_append_right (left := collectStmtNames stmt) hincluded

theorem scopeNamesIncluded_collectStmtNames_letVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded (name :: scope)
      (collectStmtNames (.letVar name value) ++ inScopeNames) := by
  intro other hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · simp [collectStmtNames]
  · simp [collectStmtNames, hincluded other hmem]

theorem scopeNamesIncluded_collectStmtNames_assignVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded (name :: scope)
      (collectStmtNames (.assignVar name value) ++ inScopeNames) := by
  intro other hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · simp [collectStmtNames]
  · simp [collectStmtNames, hincluded other hmem]

theorem scopeNamesIncluded_compiled_terminal_ite_usedNames
    {scope inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope
      (inScopeNames ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) := by
  intro name hname
  simp [hincluded name hname]

theorem pickFreshName_not_mem_scope_of_subset
    {base : String}
    {scope usedNames : List String}
    (hsubset : ∀ name, name ∈ scope → name ∈ usedNames) :
    CompilationModel.pickFreshName base usedNames ∉ scope := by
  intro hmem
  exact CompilationModel.pickFreshName_not_mem_usedNames base usedNames (hsubset _ hmem)

theorem bindingsExactlyMatchIRVarsOnScope_setFreshTemp_irrelevant
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {base : String}
    {usedNames : List String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hsubset : ∀ name, name ∈ scope → name ∈ usedNames) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      (state.setVar (CompilationModel.pickFreshName base usedNames) value) := by
  apply bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact
  exact pickFreshName_not_mem_scope_of_subset hsubset

theorem compiled_terminal_ite_temp_not_mem_scope
    {scope inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    CompilationModel.pickFreshName "__ite_cond"
      (inScopeNames ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∉ scope := by
  apply pickFreshName_not_mem_scope_of_subset
  exact scopeNamesIncluded_compiled_terminal_ite_usedNames
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) hincluded

theorem bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
    {scope inScopeNames : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      (state.setVar
        (CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))
        value) := by
  apply bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact
  exact compiled_terminal_ite_temp_not_mem_scope
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) hincluded

theorem exec_compileStmtList_terminal_core_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hterminal : StmtListTerminalCore scope stmts)
    (hincluded : scopeNamesIncluded scope inScopeNames)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec := by
  induction hterminal generalizing extraFuel runtime state inScopeNames with
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' :=
          bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        have hincluded' : scopeNamesIncluded (name :: scope)
            (collectStmtNames (.letVar name value) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_letVar hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.let_ name valueIR))
            (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
            hincluded' hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel) state
                (YulStmt.let_ name valueIR) = .continue state' :=
            execIRStmt_let_of_eval_nonzeroFuel
              (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel) state name valueIR valueNat
              (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
              hIR
          have hirExec :=
            execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
              extraFuel state state' (YulStmt.let_ name valueIR) tailIR hstmt
          -- hirExec : execIRStmts (sizeOf ([let_ ...] ++ tailIR) + extraFuel + 1) state ([let_ ...] ++ tailIR) =
          --   execIRStmts (sizeOf ([let_ ...] ++ tailIR) + extraFuel) state' tailIR
          -- htailSem has fuel sizeOf tailIR + (extraFuel + sizeOf (let_ ...)) + 1
          -- which equals sizeOf ([let_ ...] ++ tailIR) + extraFuel by List sizeOf arithmetic
          simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc, hirExec]
          dsimp [runtime', state']
          convert htailSem using 2
          simp
          omega
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' :=
          bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        have hincluded' : scopeNamesIncluded (name :: scope)
            (collectStmtNames (.assignVar name value) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_assignVar hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.assign name valueIR))
            (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
            hincluded' hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel) state
                (YulStmt.assign name valueIR) = .continue state' :=
            execIRStmt_assign_of_eval_nonzeroFuel
              (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel) state name valueIR valueNat
              (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
              hIR
          have hirExec :=
            execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
              extraFuel state state' (YulStmt.assign name valueIR) tailIR hstmt
          simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc, hirExec]
          dsimp [runtime', state']
          convert htailSem using 2
          simp
          omega
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core_of_scope hcond hexact hinScope hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        rcases eval_compileRequireFailCond_core_of_scope hcond hexact hinScope
            hbounded hpresent hruntime with
          ⟨failCond, hfailCompile, hfailEval⟩
        have hincluded' : scopeNamesIncluded scope
            (collectStmtNames (.require cond message) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_tail hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)))
            (runtime := runtime) (state := state)
            (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
            hincluded' hscope hexact hbounded hruntime with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hfailCompile]
          simp [htailCompile]
          exact rfl
        · by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
            have hfuelNe : sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel ≠ 0 :=
              sizeOf_singleton_append_extraFuel_ne_zero _ _ _
            -- if_ with true cond steps into the body
            have hIfStep :=
              execIRStmt_if_true_of_eval_nonzeroFuel
                (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                state failCond (CompilationModel.revertWithMessage message) 1
                hfuelNe hfailEval' (by omega)
            rcases execIRStmts_revertWithMessage_revert
                (fuel :=
                  sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel - 1)
                (state := state) message with
              ⟨revState, hrev⟩
            have hstmt :
                execIRStmt
                  (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                  state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .revert revState := by
              rw [hIfStep, hrev]
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
                extraFuel state revState
                (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc,
              show condVal = 0 from hzero, ite_true]
            rw [hirExec]
            simp [stmtResultMatchesIRExec]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
            have hfuelNe : sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel ≠ 0 :=
              sizeOf_singleton_append_extraFuel_ne_zero _ _ _
            have hstmt :
                execIRStmt
                  (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                  state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .continue state :=
              execIRStmt_if_false_of_eval_nonzeroFuel
                (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                state failCond (CompilationModel.revertWithMessage message) 0
                hfuelNe hfailEval' rfl
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
                extraFuel state state
                (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc, hirExec]
            simp [hzero]
            convert htailSem using 2
            simp
            omega
  | return_ hvalue hinScope hrest =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_core_ok (fields := fields) (inScopeNames := collectStmtNames (.return value) ++ inScopeNames) hrest with
        ⟨tailIR, htailCompile⟩
      refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
        ?_, ?_⟩
      · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
        rw [hvalueIR]
        simp [htailCompile]
        exact rfl
      · exact stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
          hvalue hvalueIR hexact hinScope hscope hbounded hruntime
  | stop hrest =>
      rename_i scope rest
      rcases compileStmtList_core_ok (fields := fields) (inScopeNames := collectStmtNames (.stop) ++ inScopeNames) hrest with
        ⟨tailIR, htailCompile⟩
      refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
      · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
      · exact stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel hruntime
  | mstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core_of_scope hoffset hexact hinScopeOffset hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core_of_scope hvalue hexact hinScopeValue hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                memory := fun o => if o = offsetNat then valueNat else runtime.world.memory o
              } }
          let state' := { state with memory := fun o => if o = offsetNat then valueNat else state.memory o }
          have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScopeValue hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt; simp at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setBothMemory hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVarsOnScope scope runtime'.bindings state' :=
            bindingsExactlyMatchIRVarsOnScope_setMemory hexact offsetNat valueNat
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          have hscope' : scopeNamesPresent scope runtime'.bindings := by
            simpa [runtime'] using hscope
          have hincluded' : scopeNamesIncluded scope
              (collectStmtNames (.mstore offset value) ++ inScopeNames) :=
            scopeNamesIncluded_collectStmtNames_tail hincluded
          rcases ih (extraFuel + sizeOf (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])))
              (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.mstore offset value) ++ inScopeNames)
              hincluded' hscope' hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem⟩
          refine ⟨[YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (sizeOf ([YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel) state
                  (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) = .continue state' := by
              have hfuelNe : sizeOf ([YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel ≠ 0 :=
                sizeOf_singleton_append_extraFuel_ne_zero _ _ _
              cases hfuel : sizeOf ([YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel with
              | zero => exact absurd hfuel hfuelNe
              | succ n => simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
                extraFuel state state' (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) tailIR hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc, hirExec]
            dsimp [runtime', state']
            convert htailSem using 2
            simp
            omega
  | tstore hoffset hinScopeOffset hvalue hinScopeValue hrest ih =>
      rename_i scope offset value rest
      have hpresentOffset : exprBoundNamesPresent offset runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeOffset
      have hpresentValue : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScopeValue
      rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have hevalOffset := eval_compileExpr_core_of_scope hoffset hexact hinScopeOffset hbounded hpresentOffset hruntime
      rw [hoffsetIR] at hevalOffset; simp [Except.toOption] at hevalOffset
      have hevalValue := eval_compileExpr_core_of_scope hvalue hexact hinScopeValue hbounded hpresentValue hruntime
      rw [hvalueIR] at hevalValue; simp [Except.toOption] at hevalValue
      rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
      · simp [hIROffset, Option.bind] at hevalOffset
      · simp [hIROffset, Option.bind] at hevalOffset
        rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
        · simp [hIRValue, Option.bind] at hevalValue
        · simp [hIRValue, Option.bind] at hevalValue
          have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
            hevalOffset.symm
          have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
            hevalValue.symm
          let runtime' :=
            { runtime with
              world := {
                runtime.world with
                transientStorage := fun o => if o = offsetNat then valueNat else runtime.world.transientStorage o
              } }
          let state' := { state with transientStorage := fun o => if o = offsetNat then valueNat else state.transientStorage o }
          have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScopeValue hbounded hpresentValue hruntime
          rw [hValueSrc] at hvalueLt; simp at hvalueLt
          have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
            runtimeStateMatchesIR_setTransientStorage hruntime offsetNat valueNat hvalueLt
          have hexact' : bindingsExactlyMatchIRVarsOnScope scope runtime'.bindings state' := by
            intro name hname; simpa [IRState.getVar, state'] using hexact name hname
          have hbounded' : bindingsBounded runtime'.bindings := by
            simpa [runtime'] using hbounded
          have hscope' : scopeNamesPresent scope runtime'.bindings := by
            simpa [runtime'] using hscope
          have hincluded' : scopeNamesIncluded scope
              (collectStmtNames (.tstore offset value) ++ inScopeNames) :=
            scopeNamesIncluded_collectStmtNames_tail hincluded
          rcases ih (extraFuel + sizeOf (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])))
              (runtime := runtime') (state := state')
              (inScopeNames := collectStmtNames (.tstore offset value) ++ inScopeNames)
              hincluded' hscope' hexact' hbounded' hruntime' with
            ⟨tailIR, htailCompile, htailSem⟩
          refine ⟨[YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR, ?_, ?_⟩
          · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
            rw [hoffsetIR, hvalueIR]
            simp [htailCompile]
            exact rfl
          · have hstmt :
                execIRStmt (sizeOf ([YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel) state
                  (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) = .continue state' := by
              have hfuelNe : sizeOf ([YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel ≠ 0 :=
                sizeOf_singleton_append_extraFuel_ne_zero _ _ _
              cases hfuel : sizeOf ([YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] ++ tailIR) + extraFuel with
              | zero => exact absurd hfuel hfuelNe
              | succ n => simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
                extraFuel state state' (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) tailIR hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hOffsetSrc, hValueSrc, hirExec]
            dsimp [runtime', state']
            convert htailSem using 2
            simp
            omega
  | ite hcond hinScope hthen helse hrest ih_then ih_else =>
      rename_i scope cond thenBranch elseBranch rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (inScopeNames := inScopeNames) hthen with
        ⟨thenIR, hthenIR⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (inScopeNames := inScopeNames) helse with
        ⟨elseIR, helseIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (inScopeNames := collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames) hrest with
        ⟨tailIR, htailIR⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil => exfalso; exact stmtListTerminalCore_ne_nil helse rfl
        | cons => simp
      let tempName :=
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
      refine ⟨[YulStmt.block
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR,
        ?_, ?_⟩
      · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
        rw [hcondIR, hthenIR, helseIR]
        simp [helseNonempty, htailIR, tempName]
        exact rfl
      · -- Evaluate the condition
        have hCondEval := eval_compileExpr_core_of_scope hcond hexact hinScope hbounded hpresent hruntime
        rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
        rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
        · simp [hCondIRVal, Option.bind] at hCondEval
        · simp [hCondIRVal, Option.bind] at hCondEval
          have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
            hCondEval.symm
          have hexact' : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
              (state.setVar tempName condVal) :=
            bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant hexact hincluded
          by_cases hcondZero : condVal = 0
          · -- Condition is false → take else branch
            rcases ih_else (extraFuel +
                sizeOf (YulStmt.let_ tempName condIR) +
                sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                sizeOf tailIR + 1)
                (runtime := runtime) (state := state.setVar tempName condVal)
                (inScopeNames := inScopeNames)
                hincluded hscope hexact' hbounded hruntime with
              ⟨elseIR', helseCompile', helseSem⟩
            have helseEq : elseIR' = elseIR := by
              have := helseCompile'; rw [helseIR] at this; exact (Except.ok.inj this).symm
            rw [helseEq] at helseSem
            -- Prove fuel equality to convert IH fuel into helper's expected fuel
            have hfuelEq : sizeOf elseIR +
                  (extraFuel +
                    sizeOf (YulStmt.let_ tempName condIR) +
                    sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                    sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                    sizeOf tailIR + 1) + 1 =
                sizeOf elseIR +
                  (sizeOf
                    ([YulStmt.block
                        [ YulStmt.let_ tempName condIR
                        , YulStmt.if_ (YulExpr.ident tempName) thenIR
                        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                        ]] ++ tailIR) -
                    (sizeOf elseIR + 5) + extraFuel) := by
              simp only [List.singleton_append]
              have hinner : sizeOf (YulStmt.block
                      [ YulStmt.let_ tempName condIR
                      , YulStmt.if_ (YulExpr.ident tempName) thenIR
                      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                      ] :: tailIR) -
                    (sizeOf elseIR + 5) =
                  sizeOf (YulStmt.let_ tempName condIR) +
                  sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                  sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                  sizeOf tailIR + 2 := by
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec,
                  YulStmt.let_.sizeOf_spec,
                  YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
                omega
              rw [hinner]
              omega
            rw [show execIRStmts
                  (sizeOf elseIR +
                    (extraFuel +
                      sizeOf (YulStmt.let_ tempName condIR) +
                      sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                      sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                      sizeOf tailIR + 1) + 1)
                  (state.setVar tempName condVal) elseIR =
                execIRStmts
                  (sizeOf elseIR +
                    (sizeOf
                      ([YulStmt.block
                          [ YulStmt.let_ tempName condIR
                          , YulStmt.if_ (YulExpr.ident tempName) thenIR
                          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                          ]] ++ tailIR) -
                      (sizeOf elseIR + 5) + extraFuel))
                  (state.setVar tempName condVal) elseIR from by
              rw [hfuelEq]] at helseSem
            exact stmtResultMatchesIRExec_compiled_terminal_ite_else
              (scope := scope)
              (rest := rest)
              (tempName := tempName)
              (condIR := condIR)
              (thenIR := thenIR)
              (tailIR := tailIR)
              helse helseSem hCondSrc
              (by simp [hcondZero])
              hCondIRVal hcondZero rfl
          · -- Condition is true → take then branch
            rcases ih_then (extraFuel +
                sizeOf (YulStmt.let_ tempName condIR) +
                sizeOf (YulExpr.ident tempName) +
                sizeOf (YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR) +
                sizeOf tailIR + 2)
                (runtime := runtime) (state := state.setVar tempName condVal)
                (inScopeNames := inScopeNames)
                hincluded hscope hexact' hbounded hruntime with
              ⟨thenIR', hthenCompile', hthenSem⟩
            have hthenEq : thenIR' = thenIR := by
              have := hthenCompile'; rw [hthenIR] at this; exact (Except.ok.inj this).symm
            rw [hthenEq] at hthenSem
            -- Prove fuel equality to convert IH fuel into helper's expected fuel
            have hfuelEq : sizeOf thenIR +
                  (extraFuel +
                    sizeOf (YulStmt.let_ tempName condIR) +
                    sizeOf (YulExpr.ident tempName) +
                    sizeOf (YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR) +
                    sizeOf tailIR + 2) + 1 =
                sizeOf thenIR +
                  (sizeOf
                    ([YulStmt.block
                        [ YulStmt.let_ tempName condIR
                        , YulStmt.if_ (YulExpr.ident tempName) thenIR
                        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                        ]] ++ tailIR) -
                    (sizeOf thenIR + 5) + extraFuel) + 1 := by
              simp only [List.singleton_append]
              have hinner : sizeOf (YulStmt.block
                      [ YulStmt.let_ tempName condIR
                      , YulStmt.if_ (YulExpr.ident tempName) thenIR
                      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                      ] :: tailIR) -
                    (sizeOf thenIR + 5) =
                  sizeOf (YulStmt.let_ tempName condIR) +
                  sizeOf (YulExpr.ident tempName) +
                  sizeOf (YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR) +
                  sizeOf tailIR + 2 := by
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec,
                  YulStmt.let_.sizeOf_spec,
                  YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
                omega
              rw [hinner]
              omega
            rw [show execIRStmts
                  (sizeOf thenIR +
                    (extraFuel +
                      sizeOf (YulStmt.let_ tempName condIR) +
                      sizeOf (YulExpr.ident tempName) +
                      sizeOf (YulStmt.if_
                          (YulExpr.call "iszero" [YulExpr.ident tempName])
                          elseIR) +
                      sizeOf tailIR + 2) + 1)
                  (state.setVar tempName condVal) thenIR =
                execIRStmts
                  (sizeOf thenIR +
                    (sizeOf
                      ([YulStmt.block
                          [ YulStmt.let_ tempName condIR
                          , YulStmt.if_ (YulExpr.ident tempName) thenIR
                          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                          ]] ++ tailIR) -
                      (sizeOf thenIR + 5) + extraFuel) + 1)
                  (state.setVar tempName condVal) thenIR from by
              rw [hfuelEq]] at hthenSem
            exact stmtResultMatchesIRExec_compiled_terminal_ite_then
              (scope := scope)
              (rest := rest)
              (tempName := tempName)
              (condIR := condIR)
              (elseIR := elseIR)
              (tailIR := tailIR)
              hthen hthenSem hCondSrc
              (by simp [hcondZero])
              hCondIRVal hcondZero rfl

def irResultOfExecResult (rollback : IRState) : IRExecResult → IRResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

def irResultOfExecResultWithInternals (rollback : IRState) : IRExecResultWithInternals → IRResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .leave s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

theorem stmtResultToSourceResult_matches_irExecResult
    (spec : CompilationModel)
    (fields : List Field)
    (initialWorld : Verity.ContractState)
    (rollback : IRState)
    (sourceResult : SourceSemantics.StmtResult)
    (irResult : IRExecResult)
    (hrollbackStorage :
      rollback.storage = fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
        (SourceSemantics.encodeStorage spec initialWorld s.toNat))
    (hrollbackEvents :
      rollback.events = SourceSemantics.encodeEvents initialWorld.events)
    (hfields : fields = SourceSemantics.effectiveFields spec)
    (hmatch : stmtResultMatchesIRExec fields sourceResult irResult) :
    sourceResultMatchesIRResult
      (stmtResultToSourceResult spec initialWorld sourceResult)
      (irResultOfExecResult rollback irResult) := by
  subst hfields
  cases sourceResult <;> cases irResult <;>
    simp [stmtResultMatchesIRExec] at hmatch
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret, hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents, hret]
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret, hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents]
  · rcases hmatch with
      ⟨hvalue, hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hblob, _, _, hcds, _, hret,
        hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hvalue, hstorage, hevents]
  · simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.revertedResult, hrollbackStorage, hrollbackEvents]

end FunctionBody

end Compiler.Proofs.IRGeneration
