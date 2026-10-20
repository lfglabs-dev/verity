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

private theorem compileExprWithInternals_nil_ok
    {fields : List Field} {dynamicSource : DynamicDataSource} {expr : Expr} {exprIR : YulExpr}
    (h : CompilationModel.compileExpr fields dynamicSource expr = Except.ok exprIR) :
    CompilationModel.compileExprWithInternals fields dynamicSource [] expr = Except.ok exprIR := by
  simpa [CompilationModel.compileExprWithInternals_nil_eq] using h

private theorem compileRequireFailCondWithInternals_nil_ok
    {fields : List Field} {dynamicSource : DynamicDataSource} {expr : Expr} {exprIR : YulExpr}
    (h : CompilationModel.compileRequireFailCond fields dynamicSource expr = Except.ok exprIR) :
    CompilationModel.compileRequireFailCondWithInternals fields dynamicSource [] expr =
      Except.ok exprIR := by
  simpa [CompilationModel.compileRequireFailCondWithInternals_nil_eq] using h

theorem compileStmt_core_ok
    {fields : List Field}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR, CompilationModel.compileStmt fields [] [] .calldata [] false [] [] stmt = Except.ok bodyIR := by
  cases hcore with
  | letVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.let_ name valueIR],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileExprWithInternals_nil_ok hvalueIR]⟩
  | assignVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.assign name valueIR],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileExprWithInternals_nil_ok hvalueIR]⟩
  | require_ hcond =>
      rename_i cond message
      rcases compileRequireFailCond_core_ok (fields := fields) hcond with ⟨failCond, hfailCond⟩
      exact ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileRequireFailCondWithInternals_nil_ok hfailCond]⟩
  | return_ hvalue =>
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileExprWithInternals_nil_ok hvalueIR]⟩
  | stop =>
      exact ⟨[YulStmt.exprStmt (YulExpr.call "stop" [])], by
        rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork]
        rfl⟩
  | mstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok (fields := fields) hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileExprWithInternals_nil_ok hoffsetIR,
          compileExprWithInternals_nil_ok hvalueIR, Bind.bind, Except.bind, pure, Except.pure]⟩
  | tstore hoffset hvalue =>
      rename_i offset value
      rcases compileExpr_core_ok (fields := fields) hoffset with ⟨offsetIR, hoffsetIR⟩
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])],
        by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, compileExprWithInternals_nil_ok hoffsetIR,
          compileExprWithInternals_nil_ok hvalueIR, Bind.bind, Except.bind, pure, Except.pure]⟩

theorem compileStmtWithFork_cancun_eq_compileStmt
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      stmt internalFunctions =
    CompilationModel.compileStmt fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions := rfl

theorem compileStmtListWithFork_cancun_eq_compileStmtList
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmts : List Stmt)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      stmts internalFunctions =
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes stmts internalFunctions := rfl

theorem compileStmtList_nil_eq_ok
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes [] internalFunctions = Except.ok [] := by
  unfold CompilationModel.compileStmtList
  unfold CompilationModel.compileStmtListWithFork
  rfl

theorem compileStmtList_cons_eq_ok
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt) (rest : List Stmt)
    (headIR tailIR : List YulStmt)
    (hhead :
      CompilationModel.compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes stmt = Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList fields events errors dynamicSource
        internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest =
          Except.ok tailIR) :
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  unfold CompilationModel.compileStmtList
  unfold CompilationModel.compileStmtListWithFork
  rw [compileStmtWithFork_cancun_eq_compileStmt, hhead]
  simpa [bind, Except.bind, Pure.pure, Except.pure,
    compileStmtListWithFork_cancun_eq_compileStmtList, htail]

theorem compileStmtList_cons_eq_ok_with_internals
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt) (rest : List Stmt)
    (internalFunctions : List FunctionSpec)
    (headIR tailIR : List YulStmt)
    (hhead :
      CompilationModel.compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions =
          Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList fields events errors dynamicSource
        internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes
          rest internalFunctions =
          Except.ok tailIR) :
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes (stmt :: rest) internalFunctions =
        Except.ok (headIR ++ tailIR) := by
  unfold CompilationModel.compileStmtList
  unfold CompilationModel.compileStmtListWithFork
  rw [show
    CompilationModel.compileStmtWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      stmt internalFunctions =
    CompilationModel.compileStmt fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions from rfl,
    hhead]
  simpa [bind, Except.bind, Pure.pure, Except.pure,
    show
      CompilationModel.compileStmtListWithFork fields events errors dynamicSource
        internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes
        Verity.Core.Intrinsics.HardFork.cancun rest internalFunctions =
      CompilationModel.compileStmtList fields events errors dynamicSource
        internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes
        rest internalFunctions from rfl,
    htail]

theorem compileStmtListWithFork_nil_eq_ok
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      [] internalFunctions = Except.ok [] := by
  rw [compileStmtListWithFork_cancun_eq_compileStmtList
    fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes []
    internalFunctions]
  exact compileStmtList_nil_eq_ok _ _ _ _ _ _ _ _ internalFunctions

theorem compileStmtListWithFork_cons_eq_ok
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt) (rest : List Stmt)
    (internalFunctions : List FunctionSpec := [])
    (headIR tailIR : List YulStmt)
    (hhead :
      CompilationModel.compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions = Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList fields events errors dynamicSource
        internalRetNames isInternal (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest
          internalFunctions = Except.ok tailIR) :
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      (stmt :: rest) internalFunctions = Except.ok (headIR ++ tailIR) := by
  rw [compileStmtListWithFork_cancun_eq_compileStmtList
    fields events errors dynamicSource internalRetNames isInternal inScopeNames adtTypes
    (stmt :: rest) internalFunctions]
  exact compileStmtList_cons_eq_ok_with_internals
    _ _ _ _ _ _ _ _ _ _ internalFunctions _ _ hhead htail

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
          (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest = Except.ok tailIR ∧
      bodyIR = headIR ++ tailIR := by
  rw [CompilationModel.compileStmtList] at hcompile
  unfold CompilationModel.compileStmtListWithFork at hcompile
  cases hhead : CompilationModel.compileStmt
      fields events errors .calldata [] false inScopeNames adtTypes stmt with
  | error err =>
      rw [compileStmtWithFork_cancun_eq_compileStmt, hhead] at hcompile
      cases hcompile
  | ok headIR =>
      rw [compileStmtWithFork_cancun_eq_compileStmt, hhead] at hcompile
      cases htail : CompilationModel.compileStmtList
          fields events errors .calldata [] false
            (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest with
      | error err =>
          simp [compileStmtListWithFork_cancun_eq_compileStmtList, htail] at hcompile
          cases hcompile
      | ok tailIR =>
          simp [compileStmtListWithFork_cancun_eq_compileStmtList, htail] at hcompile
          injection hcompile with hbody
          subst hbody
          refine ⟨headIR, tailIR, ?_, ?_, rfl⟩
          · simpa [hhead]
          · simpa [htail]

theorem compileStmtList_cons_ok_inv_with_internals
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {adtTypes : List AdtTypeDef}
    {stmt : Stmt}
    {rest : List Stmt}
    {internalFunctions : List FunctionSpec}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmtList
        fields events errors .calldata [] false inScopeNames adtTypes (stmt :: rest) internalFunctions =
          Except.ok bodyIR) :
    ∃ headIR tailIR,
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames adtTypes
          stmt internalFunctions = Except.ok headIR ∧
      CompilationModel.compileStmtList
        fields events errors .calldata [] false (collectStmtBindNames stmt ++ inScopeNames)
          adtTypes rest internalFunctions = Except.ok tailIR ∧
      bodyIR = headIR ++ tailIR := by
  rw [CompilationModel.compileStmtList] at hcompile
  unfold CompilationModel.compileStmtListWithFork at hcompile
  cases hhead : CompilationModel.compileStmt
      fields events errors .calldata [] false inScopeNames adtTypes stmt internalFunctions with
  | error err =>
      rw [compileStmtWithFork_cancun_eq_compileStmt
        fields events errors .calldata [] false inScopeNames adtTypes stmt internalFunctions,
        hhead] at hcompile
      cases hcompile
  | ok headIR =>
      rw [compileStmtWithFork_cancun_eq_compileStmt
        fields events errors .calldata [] false inScopeNames adtTypes stmt internalFunctions,
        hhead] at hcompile
      cases htail : CompilationModel.compileStmtList
          fields events errors .calldata [] false
            (collectStmtBindNames stmt ++ inScopeNames) adtTypes rest internalFunctions with
      | error err =>
          simp [compileStmtListWithFork_cancun_eq_compileStmtList, htail] at hcompile
          cases hcompile
      | ok tailIR =>
          simp [compileStmtListWithFork_cancun_eq_compileStmtList, htail] at hcompile
          injection hcompile with hbody
          subst hbody
          refine ⟨headIR, tailIR, ?_, ?_, rfl⟩
          · simpa [hhead]
          · simpa [htail]

/-- Both sides perform the same physical `mstore`; the recomputed word views agree. -/
theorem runtimeStateMatchesIR_writePhysicalMemoryValue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (offset value : Nat) :
    runtimeStateMatchesIR fields
      { runtime with
          world := runtime.world.writePhysicalMemoryValue offset (Verity.Core.Uint256.ofNat value) }
      (state.writePhysicalMemoryValue offset value) := by
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    -, hret, hevt, hcode, hrd, hbytes⟩ := hmatch
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    ?_, hret, hevt, hcode, hrd, ?_⟩
  · rw [IRState.writePhysicalMemoryValue_storage, hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · funext o
    simp only [IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory,
      Verity.ContractState.writePhysicalMemoryValue, Verity.ContractState.writePhysicalMemoryWord,
      Verity.ContractState.installPhysicalMemory, hbytes]
  · simp only [IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory,
      Verity.ContractState.writePhysicalMemoryValue, Verity.ContractState.writePhysicalMemoryWord,
      Verity.ContractState.installPhysicalMemory, hbytes]

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
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel,
    hcd, hcds, hmem, hret, hevt, hcs⟩ := hmatch
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel,
    hcd, hcds, hmemory, hret, hevents, hcs⟩
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
          world := runtime.world.writeTransient offset value }
      { state with
          transientStorage := fun o => if o = offset then value else state.transientStorage o } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds, hmem, hret, hevt, hcs⟩ := hmatch
  refine ⟨?_, ?_, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds, hmem, hret, hevt, hcs⟩
  · -- storage: encodeStorageAt doesn't depend on transientStorage
    rw [hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · -- transientStorage
    funext o
    by_cases ho : o = offset
    · subst ho
      simp [ite_true, Verity.ContractState.transientStorage_writeTransient_same,
        Verity.Core.Uint256.ofNat]
      have hmod : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
      exact (Nat.mod_eq_of_lt (hmod ▸ hvalue)).symm
    · simp [ho]
      exact congrFun htrans o

theorem bindingsExactlyMatchIRVars_setMemory
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVars bindings
      (state.writePhysicalMemoryValue offset value) := by
  intro name
  simpa [IRState.getVar] using hexact name

theorem bindingsExactlyMatchIRVarsOnScope_setMemory
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      (state.writePhysicalMemoryValue offset value) := by
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
  · have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
    rfl
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
  · have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
    rfl
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

private theorem execIRStmt_mstore_zero_of_eval_succ
    (fuel : Nat) (state : IRState) (valueExpr : YulExpr) (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state
        (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr])) =
      .continue (state.writePhysicalMemoryValue 0 value) := by
  simp [execIRStmt, evalIRExpr, heval]

private theorem execIRStmt_return_zero_32_succ
    (fuel : Nat) (state : IRState) :
    execIRStmt (Nat.succ fuel) state
        (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
      .return (state.memory 0) state := by
  simp [execIRStmt, evalIRExpr]

private theorem execIRStmts_mstore_zero_return_32
    (extraFuel : Nat) (state : IRState) (valueExpr : YulExpr) (value : Nat)
    (heval : evalIRExpr state valueExpr = some value)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    execIRStmts (2 + extraFuel + 1) state
        [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr])
        , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
      .return value (state.writePhysicalMemoryValue 0 value) := by
  let state' : IRState := state.writePhysicalMemoryValue 0 value
  have hword : state'.memory 0 = value := by
    simp only [state', IRState.writePhysicalMemoryValue_at, Verity.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt hvalue]
  have hmstore :
      execIRStmt (Nat.succ (Nat.succ extraFuel)) state
          (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr])) =
        .continue state' := by
    simpa [state'] using execIRStmt_mstore_zero_of_eval_succ
      (Nat.succ extraFuel) state valueExpr value heval
  have hreturn :
      execIRStmt (Nat.succ extraFuel) state'
          (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
        .return value state' := by
    simpa [hword] using execIRStmt_return_zero_32_succ extraFuel state'
  have hFuel : 2 + extraFuel + 1 = Nat.succ (Nat.succ (Nat.succ extraFuel)) := by omega
  rw [hFuel]
  simp only [execIRStmts, hmstore, hreturn]
  rfl

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
  refine ⟨[ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
    rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt, List.length]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      have hlt : v < Verity.Core.Uint256.modulus := by
        have := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
        rw [heval.symm] at this; exact this
      have hexec := execIRStmts_mstore_zero_return_32 0 state valueIR v hIR hlt
      rw [hexec]
      exact ⟨⟨rfl, runtimeStateMatchesIR_writePhysicalMemoryValue hruntime 0 v⟩, hexact, hbounded⟩

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
  refine ⟨[ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
    rfl
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
          [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
          .return v (state.writePhysicalMemoryValue 0 v) := by
        exact execIRStmts_mstore_zero_return_32 extraFuel state valueIR v hIR hlt
      set runtime' : SourceSemantics.RuntimeState :=
        { runtime with world := runtime.world.writePhysicalMemoryValue 0 (Verity.Core.Uint256.ofNat v) }
      show stmtResultMatchesIRExec fields (.return v runtime') _ ∧
           stmtResultMatchesIRExecExact (.return v runtime') _
      rw [hexec]
      exact ⟨⟨rfl, runtimeStateMatchesIR_writePhysicalMemoryValue hruntime 0 v⟩, hexact, hbounded⟩

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
  refine ⟨[YulStmt.exprStmt (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork]
    rfl
  · constructor
    · have hirExec :
          execIRStmts ([YulStmt.exprStmt (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.exprStmt (YulExpr.call "stop" [])] = .stop state := by
        simp [execIRStmts]
      rw [SourceSemantics.execStmt, hirExec]
      exact hruntime
    · have hirExec :
          execIRStmts ([YulStmt.exprStmt (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.exprStmt (YulExpr.call "stop" [])] = .stop state := by
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
  refine ⟨[YulStmt.exprStmt (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork]
    rfl
  · have hirExec :
        execIRStmts
          ([YulStmt.exprStmt (YulExpr.call "stop" [])].length + extraFuel + 1)
          state
          [YulStmt.exprStmt (YulExpr.call "stop" [])] = .stop state := by
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

/-- `compileStmtList_cons_eq_ok` specialised to the core compilation context. -/
private theorem compileStmtList_core_cons_ok
    {fields : List Field} {inScopeNames : List String} {stmt : Stmt} {rest : List Stmt}
    {headIR tailIR : List YulStmt}
    (hhead : CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      stmt = Except.ok headIR)
    (htail : CompilationModel.compileStmtList fields [] [] .calldata [] false
      (collectStmtBindNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      (stmt :: rest) = Except.ok (headIR ++ tailIR) :=
  compileStmtList_cons_eq_ok _ _ _ _ _ _ _ _ _ _ _ _ hhead htail

private theorem compileStmt_letVar_eq_of_compileExpr
    {fields : List Field} {inScopeNames : List String} {name : String} {value : Expr}
    {valueIR : YulExpr}
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.letVar name value) = Except.ok [YulStmt.let_ name valueIR] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIR
  rw [hvalueIR]
  rfl

private theorem compileStmt_assignVar_eq_of_compileExpr
    {fields : List Field} {inScopeNames : List String} {name : String} {value : Expr}
    {valueIR : YulExpr}
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.assignVar name value) = Except.ok [YulStmt.assign name valueIR] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIR
  rw [hvalueIR]
  rfl

private theorem compileStmt_require_eq_of_compileRequireFailCond
    {fields : List Field} {inScopeNames : List String} {cond : Expr} {message : String}
    {failCond : YulExpr}
    (hfail : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.require cond message) =
        Except.ok [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileRequireFailCondWithInternals_nil_eq] at hfail
  rw [hfail]
  rfl

private theorem compileStmt_return_eq_of_compileExpr
    {fields : List Field} {inScopeNames : List String} {value : Expr} {valueIR : YulExpr}
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.return value) = Except.ok
        [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
        , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIR
  rw [hvalueIR]
  rfl

private theorem compileStmt_stop_eq {fields : List Field} {inScopeNames : List String} :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames [] .stop =
      Except.ok [YulStmt.exprStmt (YulExpr.call "stop" [])] := by
  rw [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork]
  rfl

private theorem compileStmt_mstore_eq_of_compileExpr
    {fields : List Field} {inScopeNames : List String} {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.mstore offset value) =
        Except.ok [YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hoffsetIR hvalueIR
  rw [hoffsetIR, hvalueIR]
  rfl

private theorem compileStmt_tstore_eq_of_compileExpr
    {fields : List Field} {inScopeNames : List String} {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.tstore offset value) =
        Except.ok [YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hoffsetIR hvalueIR
  rw [hoffsetIR, hvalueIR]
  rfl

private theorem isEmpty_eq_false_of_stmtListTerminalCore
    {scope : List String} {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    stmts.isEmpty = false := by
  cases stmts with
  | nil => exact absurd rfl (stmtListTerminalCore_ne_nil hterminal)
  | cons => rfl

private theorem compileStmt_ite_eq_of_compiled
    {fields : List Field} {inScopeNames : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt} {condIR : YulExpr} {thenIR elseIR : List YulStmt}
    (hcondIR : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthenIR : CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      thenBranch = Except.ok thenIR)
    (helseIR : CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      elseBranch = Except.ok elseIR)
    (helseNonempty : elseBranch.isEmpty = false) :
    let tempName := CompilationModel.pickFreshName
      (CompilationModel.iteCondBaseName thenBranch elseBranch)
      (inScopeNames ++ collectExprNames cond ++ collectStmtListNames thenBranch ++
        collectStmtListNames elseBranch)
    CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.ite cond thenBranch elseBranch) = Except.ok
        [YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] := by
  intro tempName
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcondIR
  rw [hcondIR]
  simp [compileStmtListWithFork_cancun_eq_compileStmtList, hthenIR, helseIR,
    helseNonempty, tempName, bind, Except.bind, Pure.pure, Except.pure]

/-- A core statement compiles, in any scope, to a nonempty IR list. -/
private theorem compileStmt_core_ok_ne_nil
    {fields : List Field} {inScopeNames : List String} {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR, CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      stmt = Except.ok bodyIR ∧ bodyIR ≠ [] := by
  cases hcore with
  | letVar hvalue =>
      obtain ⟨_, h⟩ := compileExpr_core_ok hvalue
      exact ⟨_, compileStmt_letVar_eq_of_compileExpr h, List.cons_ne_nil _ _⟩
  | assignVar hvalue =>
      obtain ⟨_, h⟩ := compileExpr_core_ok hvalue
      exact ⟨_, compileStmt_assignVar_eq_of_compileExpr h, List.cons_ne_nil _ _⟩
  | require_ hcond =>
      obtain ⟨_, h⟩ := compileRequireFailCond_core_ok hcond
      exact ⟨_, compileStmt_require_eq_of_compileRequireFailCond h, List.cons_ne_nil _ _⟩
  | return_ hvalue =>
      obtain ⟨_, h⟩ := compileExpr_core_ok hvalue
      exact ⟨_, compileStmt_return_eq_of_compileExpr h, List.cons_ne_nil _ _⟩
  | stop => exact ⟨_, compileStmt_stop_eq, List.cons_ne_nil _ _⟩
  | mstore hoffset hvalue =>
      obtain ⟨_, ho⟩ := compileExpr_core_ok hoffset
      obtain ⟨_, hv⟩ := compileExpr_core_ok hvalue
      exact ⟨_, compileStmt_mstore_eq_of_compileExpr ho hv, List.cons_ne_nil _ _⟩
  | tstore hoffset hvalue =>
      obtain ⟨_, ho⟩ := compileExpr_core_ok hoffset
      obtain ⟨_, hv⟩ := compileExpr_core_ok hvalue
      exact ⟨_, compileStmt_tstore_eq_of_compileExpr ho hv, List.cons_ne_nil _ _⟩

theorem compileStmt_core_ok_any_scope
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR,
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames [] stmt = Except.ok bodyIR :=
  let ⟨bodyIR, hbody, _⟩ := compileStmt_core_ok_ne_nil (fields := fields) hcore
  ⟨bodyIR, hbody⟩

/-! ### Scope-independence of compileStmt / compileStmtList success

`compileStmt` uses `inScopeNames` only in `ite` (for `pickFreshName` + recursive
`compileStmtList` on branches) and `forEach` (for recursive `compileStmtList` on body).
Since `pickFreshName` is total and `compileExpr` / all other helpers ignore `inScopeNames`,
compilation success is scope-independent: if it succeeds with one scope, it succeeds
with any other. -/

/-- Success of `compileStmt` on `stmt` transports from `scope1` to `scope2`. -/
private def StmtOkAnyScope (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (internalFunctions : List FunctionSpec)
    (scope1 scope2 : List String) (stmt : Stmt) : Prop :=
  (∃ ir, CompilationModel.compileStmt fields events errors .calldata [] false scope1 []
    stmt internalFunctions = Except.ok ir) →
  ∃ ir', CompilationModel.compileStmt fields events errors .calldata [] false scope2 []
    stmt internalFunctions = Except.ok ir'

/-- Success of `compileStmtList` on `stmts` transports from `scope1` to `scope2`. -/
private def StmtListOkAnyScope (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (internalFunctions : List FunctionSpec)
    (scope1 scope2 : List String) (stmts : List Stmt) : Prop :=
  (∃ ir, CompilationModel.compileStmtList fields events errors .calldata [] false scope1 []
    stmts internalFunctions = Except.ok ir) →
  ∃ ir', CompilationModel.compileStmtList fields events errors .calldata [] false scope2 []
    stmts internalFunctions = Except.ok ir'

/-- The IR block emitted for a compiled terminal `ite` whose condition is cached in `tempName`
(see `compileStmt_ite_eq_of_compiled`). -/
local notation "compiledTerminalIteIR(" tempName ", " condIR ", " thenIR ", " elseIR ")" =>
  [YulStmt.block
    [ YulStmt.let_ tempName condIR
    , YulStmt.if_ (YulExpr.ident tempName) thenIR
    , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]

private theorem stmtOkAnyScope_ite
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec} {scope1 scope2 : List String}
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hthen : StmtListOkAnyScope fields events errors internalFunctions scope1 scope2 thenBranch)
    (helse : StmtListOkAnyScope fields events errors internalFunctions scope1 scope2 elseBranch) :
    StmtOkAnyScope fields events errors internalFunctions scope1 scope2
      (.ite cond thenBranch elseBranch) := by
  rintro ⟨ir, hir⟩
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    compileStmtListWithFork_cancun_eq_compileStmtList, bind, Except.bind] at hir ⊢
  cases hcond : CompilationModel.compileExprWithInternals fields .calldata internalFunctions cond
    with
  | error e => simp [hcond] at hir
  | ok condIR =>
    cases hthen1 : CompilationModel.compileStmtList
        fields events errors .calldata [] false scope1 [] thenBranch internalFunctions with
    | error e => simp [hcond, hthen1] at hir
    | ok thenIR1 =>
      cases helse1 : CompilationModel.compileStmtList
          fields events errors .calldata [] false scope1 [] elseBranch internalFunctions with
      | error e => simp [hcond, hthen1, helse1] at hir
      | ok elseIR1 =>
        obtain ⟨thenIR2, hthen2⟩ := hthen ⟨thenIR1, hthen1⟩
        obtain ⟨elseIR2, helse2⟩ := helse ⟨elseIR1, helse1⟩
        simp only [hthen2, helse2]
        cases elseBranch <;> exact ⟨_, rfl⟩

private theorem stmtOkAnyScope_forEach
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec} {scope1 scope2 : List String}
    {varName : String} {count : Expr} {body : List Stmt}
    (hbody : StmtListOkAnyScope fields events errors internalFunctions
      (CompilationModel.forEachBodyScope scope1 varName count body)
      (CompilationModel.forEachBodyScope scope2 varName count body) body) :
    StmtOkAnyScope fields events errors internalFunctions scope1 scope2
      (.forEach varName count body) := by
  rintro ⟨ir, hir⟩
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    compileStmtListWithFork_cancun_eq_compileStmtList, bind, Except.bind] at hir ⊢
  cases hcount : CompilationModel.compileExprWithInternals fields .calldata internalFunctions
    count with
  | error e => simp [hcount] at hir
  | ok countIR =>
    cases hbody1 : CompilationModel.compileStmtList fields events errors .calldata [] false
        (CompilationModel.forEachBodyScope scope1 varName count body) [] body
        internalFunctions with
    | error e => simp [hcount, hbody1] at hir
    | ok bodyIR1 =>
      obtain ⟨bodyIR2, hbody2⟩ := hbody ⟨bodyIR1, hbody1⟩
      simp only [hbody2]
      exact ⟨_, rfl⟩

private theorem stmtOkAnyScope_forEachSetBit
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec} {scope1 scope2 : List String}
    {varName : String} {bitmap : Expr} {body : List Stmt}
    (hbody : StmtListOkAnyScope fields events errors internalFunctions
      (CompilationModel.forEachSetBitFallbackBodyScope scope1 varName bitmap body)
      (CompilationModel.forEachSetBitFallbackBodyScope scope2 varName bitmap body) body) :
    StmtOkAnyScope fields events errors internalFunctions scope1 scope2
      (.forEachSetBit varName bitmap body) := by
  rintro ⟨ir, hir⟩
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    compileStmtListWithFork_cancun_eq_compileStmtList, bind, Except.bind] at hir ⊢
  cases hbitmap : CompilationModel.compileExprWithInternals fields .calldata internalFunctions
    bitmap with
  | error e => simp [hbitmap] at hir
  | ok bitmapIR =>
    cases hbody1 : CompilationModel.compileStmtList fields events errors .calldata [] false
        (CompilationModel.forEachSetBitFallbackBodyScope scope1 varName bitmap body) [] body
        internalFunctions with
    | error e => simp [hbitmap, hbody1] at hir
    | ok bodyIR1 =>
      obtain ⟨bodyIR2, hbody2⟩ := hbody ⟨bodyIR1, hbody1⟩
      simp only [hbody2]
      exact ⟨_, rfl⟩

/-- One step of the scope-transport induction for a single statement, given transport for
every strictly smaller statement list. -/
private theorem stmtOkAnyScope_of_lt
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec} {stmt : Stmt}
    (hlist : ∀ (stmts : List Stmt) (scope1 scope2 : List String), sizeOf stmts < sizeOf stmt →
      StmtListOkAnyScope fields events errors internalFunctions scope1 scope2 stmts)
    (scope1 scope2 : List String) :
    StmtOkAnyScope fields events errors internalFunctions scope1 scope2 stmt := by
  cases stmt with
  | ite cond thenBranch elseBranch =>
      exact stmtOkAnyScope_ite (hlist _ _ _ (by simp; omega)) (hlist _ _ _ (by simp))
  | forEach varName count body => exact stmtOkAnyScope_forEach (hlist _ _ _ (by simp))
  | forEachSetBit varName bitmap body =>
      exact stmtOkAnyScope_forEachSetBit (hlist _ _ _ (by simp))
  | unsafeBlock _ body =>
      intro hok
      simpa [StmtOkAnyScope, CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        compileStmtListWithFork_cancun_eq_compileStmtList] using
        hlist body scope1 scope2 (by simp) (by
          simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
            compileStmtListWithFork_cancun_eq_compileStmtList] using hok)
  | matchAdt =>
      rintro ⟨ir, hir⟩
      simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, lookupAdtTypeDef,
        Except.bind, bind] at hir
  | _ =>
      intro hok
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hok ⊢
      exact hok

private theorem stmtListOkAnyScope_cons
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec} {scope1 scope2 : List String}
    {stmt : Stmt} {rest : List Stmt}
    (hhead : StmtOkAnyScope fields events errors internalFunctions scope1 scope2 stmt)
    (htail : StmtListOkAnyScope fields events errors internalFunctions
      (collectStmtBindNames stmt ++ scope1) (collectStmtBindNames stmt ++ scope2) rest) :
    StmtListOkAnyScope fields events errors internalFunctions scope1 scope2 (stmt :: rest) := by
  rintro ⟨ir, hir⟩
  rcases compileStmtList_cons_ok_inv_with_internals (adtTypes := []) hir with
    ⟨headIR1, tailIR1, hs1, hss1, _⟩
  obtain ⟨headIR2, hs2⟩ := hhead ⟨headIR1, hs1⟩
  obtain ⟨tailIR2, hss2⟩ := htail ⟨tailIR1, hss1⟩
  exact ⟨_, compileStmtList_cons_eq_ok_with_internals
    _ _ _ _ _ _ _ _ _ _ internalFunctions _ _ hs2 hss2⟩

private theorem compileStmt_ok_any_scope_with_surface_aux
    (n : Nat) (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec) :
    (∀ (stmt : Stmt) (scope1 scope2 : List String), sizeOf stmt < n →
      StmtOkAnyScope fields events errors internalFunctions scope1 scope2 stmt) ∧
    (∀ (stmts : List Stmt) (scope1 scope2 : List String), sizeOf stmts < n →
      StmtListOkAnyScope fields events errors internalFunctions scope1 scope2 stmts) := by
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
                    fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    refine ⟨fun stmt scope1 scope2 hlt =>
      stmtOkAnyScope_of_lt (fun stmts s1 s2 hlt' => ih.2 stmts s1 s2 (by omega)) scope1 scope2,
      fun stmts scope1 scope2 hlt => ?_⟩
    cases stmts with
    | nil => exact fun _ => ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
    | cons s ss =>
      exact stmtListOkAnyScope_cons (ih.1 s _ _ (by simp at hlt; omega))
        (ih.2 ss _ _ (by simp at hlt; omega))

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
        Except.ok ir') :=
  compileStmt_ok_any_scope_with_surface_aux n fields [] [] []

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
  (compileStmt_ok_any_scope_with_surface_aux (sizeOf stmt + 1) fields events errors []).1
    stmt scope1 scope2 (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmt_ok_any_scope_with_surface_with_internals
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec}
    {scope1 scope2 : List String}
    {stmt : Stmt}
    (hok : ∃ ir, CompilationModel.compileStmt
      fields events errors .calldata [] false scope1 [] stmt internalFunctions =
        Except.ok ir) :
    ∃ ir', CompilationModel.compileStmt
      fields events errors .calldata [] false scope2 [] stmt internalFunctions =
        Except.ok ir' :=
  (compileStmt_ok_any_scope_with_surface_aux
    (sizeOf stmt + 1) fields events errors internalFunctions).1
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
  (compileStmt_ok_any_scope_with_surface_aux (sizeOf stmts + 1) fields events errors []).2
    stmts scope1 scope2 (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmtList_ok_any_scope_with_surface_with_internals
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {internalFunctions : List FunctionSpec}
    {scope1 scope2 : List String}
    {stmts : List Stmt}
    (hok : ∃ ir, CompilationModel.compileStmtList
      fields events errors .calldata [] false scope1 [] stmts internalFunctions =
        Except.ok ir) :
    ∃ ir', CompilationModel.compileStmtList
      fields events errors .calldata [] false scope2 [] stmts internalFunctions =
        Except.ok ir' :=
  (compileStmt_ok_any_scope_with_surface_aux
    (sizeOf stmts + 1) fields events errors internalFunctions).2
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
          (collectStmtBindNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    CompilationModel.compileStmtList
      fields events errors .calldata [] false inScopeNames [] (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  exact compileStmtList_cons_eq_ok _ _ _ _ _ _ _ _ _ _ _ _ hhead htail

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
          (collectStmtBindNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  exact compileStmtList_cons_eq_ok _ _ _ _ _ _ _ _ _ _ _ _ hhead htail

/-- A successful compile of an `ite` compiles its condition and both branches. -/
private theorem compileStmt_ite_ok_components
    {fields : List Field} {inScopeNames : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt} {bodyIR : List YulStmt}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.ite cond thenBranch elseBranch) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] elseBranch = Except.ok elseIR := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork at hcompile
  rw [← CompilationModel.compileExprWithInternals_nil_eq]
  simp only [compileStmtListWithFork_cancun_eq_compileStmtList] at hcompile
  cases hcond : CompilationModel.compileExprWithInternals fields .calldata [] cond with
  | error err => simp [hcond] at hcompile; cases hcompile
  | ok condIR =>
    cases hthen : CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] thenBranch with
    | error err => simp [hcond, hthen] at hcompile; cases hcompile
    | ok thenIR =>
      cases helse : CompilationModel.compileStmtList
          fields [] [] .calldata [] false inScopeNames [] elseBranch with
      | error err => simp [hcond, hthen, helse] at hcompile; cases hcompile
      | ok elseIR => exact ⟨condIR, thenIR, elseIR, rfl, rfl, rfl⟩

theorem compileStmt_terminal_ite_ok_inv
    {fields : List Field} {inScopeNames : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt} {bodyIR : List YulStmt}
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
        CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR = compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) := by
  obtain ⟨condIR, thenIR, elseIR, hcond, hthen, helse⟩ := compileStmt_ite_ok_components hcompile
  refine ⟨condIR, thenIR, elseIR, _, hcond, hthen, helse, rfl, ?_⟩
  rw [compileStmt_ite_eq_of_compiled hcond hthen helse helseNonempty] at hcompile
  exact (Except.ok.inj hcompile).symm

theorem compileStmtList_terminal_ite_ok_inv
    {fields : List Field} {inScopeNames : List String} {cond : Expr}
    {thenBranch elseBranch rest : List Stmt} {bodyIR : List YulStmt}
    (helseNonempty : elseBranch.isEmpty = false)
    (hcompile : CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      (.ite cond thenBranch elseBranch :: rest) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR tailIR tempName,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] elseBranch = Except.ok elseIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtBindNames (.ite cond thenBranch elseBranch) ++ inScopeNames) [] rest =
          Except.ok tailIR ∧
      tempName =
        CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR = compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR := by
  rcases compileStmtList_cons_ok_inv hcompile with ⟨headIR, tailIR, hhead, htail, hbody⟩
  rcases compileStmt_terminal_ite_ok_inv helseNonempty hhead with
    ⟨condIR, thenIR, elseIR, tempName, hcond, hthen, helse, htemp, hheadIR⟩
  exact ⟨condIR, thenIR, elseIR, tailIR, tempName, hcond, hthen, helse, htail, htemp,
    hheadIR ▸ hbody⟩

/-- Prepending a statement that compiles in every scope preserves compile success. -/
private theorem compileStmtList_cons_ok_of_head_ok
    {fields : List Field} {inScopeNames : List String} {stmt : Stmt} {rest : List Stmt}
    (hhead : ∃ headIR, CompilationModel.compileStmt
      fields [] [] .calldata [] false inScopeNames [] stmt = Except.ok headIR)
    (htail : ∃ tailIR, CompilationModel.compileStmtList fields [] [] .calldata [] false
      (collectStmtBindNames stmt ++ inScopeNames) [] rest = Except.ok tailIR) :
    ∃ bodyIR, CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] (stmt :: rest) = Except.ok bodyIR :=
  let ⟨_, hh⟩ := hhead
  let ⟨_, ht⟩ := htail
  ⟨_, compileStmtList_core_cons_ok hh ht⟩

theorem compileStmtList_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hcore : StmtListCompileCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hcore generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | letVar _ _ _ ih | assignVar _ _ _ ih | require_ _ _ _ ih | return_ _ _ _ ih | stop _ ih
  | mstore _ _ _ _ _ ih | tstore _ _ _ _ _ ih =>
      exact compileStmtList_cons_ok_of_head_ok
        (compileStmt_core_ok_any_scope (by constructor <;> assumption)) ih

/-- An `ite` whose condition is core and whose branches compile, compiles in the same scope. -/
private theorem compileStmt_terminal_ite_core_ok
    {fields : List Field} {scope inScopeNames : List String} {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : ExprCompileCore cond)
    (helse : StmtListTerminalCore scope elseBranch)
    (hthenIR : ∃ thenIR, CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] thenBranch = Except.ok thenIR)
    (helseIR : ∃ elseIR, CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] elseBranch = Except.ok elseIR) :
    ∃ headIR, CompilationModel.compileStmt fields [] [] .calldata [] false inScopeNames []
      (.ite cond thenBranch elseBranch) = Except.ok headIR :=
  let ⟨_, hc⟩ := compileExpr_core_ok (fields := fields) hcond
  let ⟨_, ht⟩ := hthenIR
  let ⟨_, he⟩ := helseIR
  ⟨_, compileStmt_ite_eq_of_compiled hc ht he (isEmpty_eq_false_of_stmtListTerminalCore helse)⟩

theorem compileStmtList_terminal_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hterminal generalizing inScopeNames with
  | letVar _ _ _ ih | assignVar _ _ _ ih | require_ _ _ _ ih | mstore _ _ _ _ _ ih
  | tstore _ _ _ _ _ ih =>
      exact compileStmtList_cons_ok_of_head_ok
        (compileStmt_core_ok_any_scope (by constructor <;> assumption)) ih
  | return_ _ _ hrest | stop hrest =>
      exact compileStmtList_cons_ok_of_head_ok
        (compileStmt_core_ok_any_scope (by constructor <;> assumption))
        (compileStmtList_core_ok hrest)
  | ite hcond _ _ helse hrest ihThen ihElse =>
      exact compileStmtList_cons_ok_of_head_ok
        (compileStmt_terminal_ite_core_ok hcond helse ihThen ihElse)
        (compileStmtList_core_ok hrest)

/-- A list headed by a core statement compiles to a nonempty IR list. -/
private theorem compileStmtList_cons_core_ne_nil
    {fields : List Field} {inScopeNames : List String} {stmt : Stmt} {rest : List Stmt}
    {bodyIR : List YulStmt}
    (hcore : StmtCompileCore stmt)
    (hcompile : CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames [] (stmt :: rest) = Except.ok bodyIR) :
    bodyIR ≠ [] := by
  rcases compileStmtList_cons_ok_inv hcompile with ⟨headIR, tailIR, hhead, _, rfl⟩
  obtain ⟨headIR', hhead', hne⟩ :=
    compileStmt_core_ok_ne_nil (fields := fields) (inScopeNames := inScopeNames) hcore
  rw [hhead'] at hhead
  cases hhead
  simp [hne]

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
  cases hterminal with
  | ite _ _ _ helse =>
      rcases compileStmtList_terminal_ite_ok_inv (isEmpty_eq_false_of_stmtListTerminalCore helse)
        hcompile with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp
  | _ => exact compileStmtList_cons_core_ne_nil (by constructor <;> assumption) hcompile

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

private theorem execIRStmts_two_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state mid : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt)
    (hstmt1 : execIRStmt (rest.length + extraFuel + 2) state stmt1 = .continue mid) :
    execIRStmts (rest.length + extraFuel + 3) state (stmt1 :: stmt2 :: rest) =
      execIRStmts (rest.length + extraFuel + 2) mid (stmt2 :: rest) := by
  simp [execIRStmts, hstmt1]

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

/-- A non-`continue` head result is the result of the whole statement list. -/
private theorem execIRStmts_cons_of_execIRStmt_noncontinue_anyFuel
    (fuel : Nat) (state : IRState) (stmt : YulStmt) (rest : List YulStmt)
    {result : IRExecResult} (hstmt : execIRStmt fuel state stmt = result)
    (hresult : ∀ next, result ≠ .continue next) :
    execIRStmts (fuel + 1) state (stmt :: rest) = result := by
  subst hstmt
  cases h : execIRStmt fuel state stmt with
  | «continue» next => exact absurd h (hresult next)
  | «return» value next =>
      exact execIRStmts_cons_of_execIRStmt_return_anyFuel fuel state next stmt rest value h
  | stop next => exact execIRStmts_cons_of_execIRStmt_stop_anyFuel fuel state next stmt rest h
  | revert next =>
      exact execIRStmts_cons_of_execIRStmt_revert_anyFuel fuel state next stmt rest h

/-- A block whose body ends in a non-`continue` result yields that result. -/
private theorem execIRStmt_block_of_execIRStmts_noncontinue_nonzeroFuel
    (fuel : Nat) (state : IRState) (body : List YulStmt) {result : IRExecResult}
    (hfuel : fuel ≠ 0) (hbody : execIRStmts (fuel - 1) state body = result)
    (hresult : ∀ next, result ≠ .continue next) :
    execIRStmt fuel state (YulStmt.block body) = result := by
  subst hbody
  cases h : execIRStmts (fuel - 1) state body with
  | «continue» next => exact absurd h (hresult next)
  | «return» value next =>
      exact execIRStmt_block_of_execIRStmts_return_nonzeroFuel fuel state next body value hfuel h
  | stop next => exact execIRStmt_block_of_execIRStmts_stop_nonzeroFuel fuel state next body hfuel h
  | revert next =>
      exact execIRStmt_block_of_execIRStmts_revert_nonzeroFuel fuel state next body hfuel h

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
      (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue (state.writePhysicalMemoryValue (offset % Compiler.Constants.evmModulus) value) := by
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
      (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue (state.writePhysicalMemoryValue (offset % Compiler.Constants.evmModulus) value) := by
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
      (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
      .return (state.memory offset) state := by
  simp [execIRStmt, evalIRExpr]

private theorem execIRStmt_return32_of_memory_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (hfuel : fuel ≠ 0) :
    execIRStmt fuel state
      (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
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
    execIRStmt fuel state (YulStmt.exprStmt (YulExpr.call "stop" [])) = .stop state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_stop_succ fuel state

private inductive RevertPrefixStmt : YulStmt → Prop where
  | mstore_lit {offset value : Nat} :
      RevertPrefixStmt (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.lit value]))
  | mstore_hex {offset value : Nat} :
      RevertPrefixStmt (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex value]))

private theorem execIRStmt_revertPrefix_continue
    (fuel : Nat) (state : IRState) {stmt : YulStmt}
    (hstmt : RevertPrefixStmt stmt) :
    ∃ next, execIRStmt (Nat.succ fuel) state stmt = .continue next := by
  cases hstmt with
  | mstore_lit =>
      rename_i offset value
      let next := state.writePhysicalMemoryValue (offset % Compiler.Constants.evmModulus) value
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]
  | mstore_hex =>
      rename_i offset value
      let next := state.writePhysicalMemoryValue (offset % Compiler.Constants.evmModulus) value
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]

private theorem execIRStmts_revertPrefix_then_revert
    (fuel : Nat) (state : IRState)
    (prefixStmts : List YulStmt)
    (offset size : Nat)
    (hprefix : ∀ stmt ∈ prefixStmts, RevertPrefixStmt stmt) :
    ∃ next,
      execIRStmts fuel state
        (prefixStmts ++ [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit offset, YulExpr.lit size])]) =
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
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (CompilationModel.chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := CompilationModel.wordFromBytes chunk
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
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

/-- Exact-bindings analogue of `exists_eval_compileExpr_core_of_scope`. -/
private theorem exists_eval_compileExpr_core_of_exact
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {value : Expr} {valueIR : YulExpr}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ v, evalIRExpr state valueIR = some v ∧
      SourceSemantics.evalExpr fields runtime value = some v ∧
      v < Compiler.Constants.evmModulus := by
  have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
  have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp only [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    rw [← heval] at hlt
    exact ⟨v, rfl, heval.symm, by simpa using hlt⟩

private theorem execStmtList_letVar_cons_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {name : String}
    {value : Expr} {rest : List Stmt} {valueNat : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.letVar name value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        rest := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc]

/-- Closes an exact-fuel list step whose head continues in both semantics. -/
private theorem stmtResultMatches_cons_continue_extraFuel
    {fields : List Field} {src : SourceSemantics.StmtResult}
    {runtime' : SourceSemantics.RuntimeState} {rest : List Stmt} {state state' : IRState}
    {stmt : YulStmt} {tailIR : List YulStmt} {extraFuel : Nat}
    (hsrc : src = SourceSemantics.execStmtList fields runtime' rest)
    (hstmt : execIRStmt (tailIR.length + extraFuel + 1) state stmt = .continue state')
    (htailSem : stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime' rest)
      (execIRStmts (tailIR.length + extraFuel + 1) state' tailIR))
    (htailExact : stmtResultMatchesIRExecExact
      (SourceSemantics.execStmtList fields runtime' rest)
      (execIRStmts (tailIR.length + extraFuel + 1) state' tailIR)) :
    let irExec := execIRStmts (([stmt] ++ tailIR).length + extraFuel + 1) state ([stmt] ++ tailIR)
    stmtResultMatchesIRExec fields src irExec ∧ stmtResultMatchesIRExecExact src irExec := by
  have hirExec := execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state' stmt
    tailIR hstmt
  have hlen : ([stmt] ++ tailIR).length + extraFuel + 1 = tailIR.length + extraFuel + 2 := by
    simp; omega
  rw [hlen, List.singleton_append, hirExec, hsrc]
  exact ⟨htailSem, htailExact⟩

private theorem stmtResultMatches_return_cons_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {value : Expr} {rest : List Stmt} {valueIR : YulExpr} {tailIR : List YulStmt}
    {extraFuel v : Nat}
    (hIR : evalIRExpr state valueIR = some v)
    (hsrc : SourceSemantics.evalExpr fields runtime value = some v)
    (hlt : v < Compiler.Constants.evmModulus)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    let src := SourceSemantics.execStmtList fields runtime (.return value :: rest)
    let irExec := execIRStmts
      (([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
        , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR).length + extraFuel + 1) state
      ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
        , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR)
    stmtResultMatchesIRExec fields src irExec ∧ stmtResultMatchesIRExecExact src irExec := by
  have hirExec := execIRStmts_two_of_continue_then_return_extraFuel extraFuel state
    (state.writePhysicalMemoryValue 0 v) (state.writePhysicalMemoryValue 0 v)
    (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
    (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) tailIR v
    (by simp [execIRStmt, evalIRExpr, hIR]) (by simp [execIRStmt, evalIRExpr]; exact hlt)
  have hlen : ∀ a b : YulStmt,
      ([a, b] ++ tailIR).length + extraFuel + 1 = tailIR.length + extraFuel + 3 := by
    intro a b; simp; omega
  rw [hlen]
  simp only [List.cons_append, List.nil_append, hirExec, SourceSemantics.execStmtList,
    SourceSemantics.execStmt, hsrc]
  exact ⟨⟨rfl, runtimeStateMatchesIR_writePhysicalMemoryValue hruntime 0 v⟩,
    bindingsExactlyMatchIRVars_setMemory hexact 0 v, hbounded⟩

private theorem execStmtList_assignVar_cons_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {name : String}
    {value : Expr} {rest : List Stmt} {valueNat : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.assignVar name value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        rest := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc]

private theorem execStmtList_require_cons_eq_of_ne_zero
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {cond : Expr}
    {message : String} {rest : List Stmt} {condVal : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hne : condVal ≠ 0) :
    SourceSemantics.execStmtList fields runtime (.require cond message :: rest) =
      SourceSemantics.execStmtList fields runtime rest := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc]
  simp [hne]

private theorem execStmtList_mstore_cons_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {offset value : Expr}
    {rest : List Stmt} {offsetNat valueNat : Nat}
    (hoffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hvalue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.mstore offset value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with world := runtime.world.writePhysicalMemoryValue offsetNat valueNat }
        rest := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hoffset, hvalue]

private theorem execStmtList_tstore_cons_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {offset value : Expr}
    {rest : List Stmt} {offsetNat valueNat : Nat}
    (hoffset : SourceSemantics.evalExpr fields runtime offset = some offsetNat)
    (hvalue : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    SourceSemantics.execStmtList fields runtime (.tstore offset value :: rest) =
      SourceSemantics.execStmtList fields
        { runtime with
          world := runtime.world.writeTransient (offsetNat % Compiler.Constants.evmModulus)
            valueNat }
        rest := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hoffset, hvalue]
  simp [SourceSemantics.wordNormalize_eq_mod]

private theorem bindingsExactlyMatchIRVars_setTransientStorage
    {bindings : List (String × Nat)} {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) (key value : Nat) :
    bindingsExactlyMatchIRVars bindings
      { state with transientStorage := fun o =>
          if o = key then value else state.transientStorage o } := by
  intro name
  simpa [IRState.getVar] using hexact name

private theorem length_singleton_append_add_one (stmt : YulStmt) (tailIR : List YulStmt)
    (extraFuel : Nat) :
    ([stmt] ++ tailIR).length + extraFuel + 1 = tailIR.length + extraFuel + 2 := by
  simp
  omega

private theorem stmtResultMatches_require_fail_cons_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {cond : Expr} {message : String} {rest : List Stmt} {failCond : YulExpr}
    {tailIR : List YulStmt} {extraFuel : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime cond = some 0)
    (hfail : evalIRExpr state failCond = some 1) :
    let src := SourceSemantics.execStmtList fields runtime (.require cond message :: rest)
    let irExec := execIRStmts
      (([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR).length +
        extraFuel + 1) state
      ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)
    stmtResultMatchesIRExec fields src irExec ∧ stmtResultMatchesIRExecExact src irExec := by
  rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length + extraFuel)
      (state := state) message with ⟨revState, hrev⟩
  have hirExec := execIRStmts_cons_of_execIRStmt_revert_extraFuel extraFuel state revState
    (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
    (by simp [execIRStmt, hfail, hrev])
  rw [length_singleton_append_add_one, List.singleton_append, hirExec]
  simp [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc, stmtResultMatchesIRExec,
    stmtResultMatchesIRExecExact]

private theorem stmtResultMatches_require_cons_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {cond : Expr} {message : String} {rest : List Stmt} {failCond : YulExpr}
    {tailIR : List YulStmt} {extraFuel condVal : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hfail : evalIRExpr state failCond =
      some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)))
    (htailSem : stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime rest)
      (execIRStmts (tailIR.length + extraFuel + 1) state tailIR))
    (htailExact : stmtResultMatchesIRExecExact (SourceSemantics.execStmtList fields runtime rest)
      (execIRStmts (tailIR.length + extraFuel + 1) state tailIR)) :
    let src := SourceSemantics.execStmtList fields runtime (.require cond message :: rest)
    let irExec := execIRStmts
      (([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR).length +
        extraFuel + 1) state
      ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)
    stmtResultMatchesIRExec fields src irExec ∧ stmtResultMatchesIRExecExact src irExec := by
  by_cases hzero : condVal = 0
  · subst hzero
    exact stmtResultMatches_require_fail_cons_extraFuel hsrc
      (by simpa [hsrc, SourceSemantics.boolWord] using hfail)
  · have hfail0 : evalIRExpr state failCond = some 0 := by
      simpa [hsrc, hzero, SourceSemantics.boolWord] using hfail
    exact stmtResultMatches_cons_continue_extraFuel
      (execStmtList_require_cons_eq_of_ne_zero hsrc hzero)
      (by simp [execIRStmt, hfail0]) htailSem htailExact

private theorem stmtResultMatches_stop_cons_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {rest : List Stmt} {tailIR : List YulStmt} {extraFuel : Nat}
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    let src := SourceSemantics.execStmtList fields runtime (.stop :: rest)
    let irExec := execIRStmts
      (([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR).length + extraFuel + 1) state
      ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR)
    stmtResultMatchesIRExec fields src irExec ∧ stmtResultMatchesIRExecExact src irExec := by
  have hirExec := execIRStmts_cons_of_execIRStmt_stop_extraFuel extraFuel state state
    (YulStmt.exprStmt (YulExpr.call "stop" [])) tailIR (by simp [execIRStmt])
  rw [length_singleton_append_add_one, List.singleton_append, hirExec]
  simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  exact ⟨hruntime, hexact, hbounded⟩

/-- Induction motive of `exec_compileStmtList_core_extraFuel`. -/
private def CoreListExecMatches (fields : List Field) (extraFuel : Nat) (scope : List String)
    (stmts : List Stmt) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (inScopeNames : List String),
    scopeNamesPresent scope runtime.bindings →
    bindingsExactlyMatchIRVars runtime.bindings state →
    bindingsBounded runtime.bindings →
    runtimeStateMatchesIR fields runtime state →
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec

private theorem coreListExecMatches_nil {fields : List Field} {extraFuel : Nat}
    {scope : List String} : CoreListExecMatches fields extraFuel scope [] := by
  intro runtime state inScopeNames _ hexact hbounded hruntime
  refine ⟨[], by
    simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
      Pure.pure, Except.pure], ?_⟩
  constructor
  · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
  · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
      And.intro hexact hbounded

private theorem coreListExecMatches_letVar
    {fields : List Field} {extraFuel : Nat} {scope : List String} {name : String}
    {value : Expr} {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (ih : CoreListExecMatches fields extraFuel (name :: scope) rest) :
    CoreListExecMatches fields extraFuel scope (.letVar name value :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_exact hvalue hvalueIR hexact
    hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rcases ih { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
      (state.setVar name v) (collectStmtBindNames (.letVar name value) ++ inScopeNames)
      (scopeNamesPresent_cons_bindValue hscope)
      (bindingsExactlyMatchIRVars_setVar_bindValue hexact name v)
      (bindingsBounded_bindValue hbounded name v hlt)
      (runtimeStateMatchesIR_setVar_bindValue hruntime name v) with
    ⟨tailIR, htailCompile, htailSem, htailExact⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_letVar_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_extraFuel (execStmtList_letVar_cons_eq hsrc)
    (by simp [execIRStmt, hIR]) htailSem htailExact

private theorem coreListExecMatches_assignVar
    {fields : List Field} {extraFuel : Nat} {scope : List String} {name : String}
    {value : Expr} {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (ih : CoreListExecMatches fields extraFuel scope rest) :
    CoreListExecMatches fields extraFuel scope (.assignVar name value :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_exact hvalue hvalueIR hexact
    hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rcases ih { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
      (state.setVar name v) (collectStmtBindNames (.assignVar name value) ++ inScopeNames)
      (fun other hmem =>
        scopeNamesPresent_cons_bindValue hscope other (List.mem_cons_of_mem name hmem))
      (bindingsExactlyMatchIRVars_setVar_bindValue hexact name v)
      (bindingsBounded_bindValue hbounded name v hlt)
      (runtimeStateMatchesIR_setVar_bindValue hruntime name v) with
    ⟨tailIR, htailCompile, htailSem, htailExact⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_assignVar_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_extraFuel (execStmtList_assignVar_cons_eq hsrc)
    (by simp [execIRStmt, hIR]) htailSem htailExact

private theorem coreListExecMatches_require
    {fields : List Field} {extraFuel : Nat} {scope : List String} {cond : Expr}
    {message : String} {rest : List Stmt}
    (hcond : ExprCompileCore cond) (hinScope : exprBoundNamesInScope cond scope)
    (ih : CoreListExecMatches fields extraFuel scope rest) :
    CoreListExecMatches fields extraFuel scope (.require cond message :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  have hpresent := exprBoundNamesPresent_of_scope hscope hinScope
  rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
  obtain ⟨condVal, -, hCondSrc, -⟩ :=
    exists_eval_compileExpr_core_of_exact hcond hcondIR hexact hbounded hpresent hruntime
  rcases eval_compileRequireFailCond_core_onExpr hcond
      (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime with
    ⟨failCond, hfailCompile, hfailEval⟩
  rcases ih runtime state (collectStmtBindNames (.require cond message) ++ inScopeNames)
      hscope hexact hbounded hruntime with
    ⟨tailIR, htailCompile, htailSem, htailExact⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_require_eq_of_compileRequireFailCond hfailCompile) htailCompile, ?_⟩
  exact stmtResultMatches_require_cons_extraFuel hCondSrc hfailEval htailSem htailExact

private theorem coreListExecMatches_return
    {fields : List Field} {extraFuel : Nat} {scope : List String} {value : Expr}
    {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (hrest : StmtListCompileCore scope rest) :
    CoreListExecMatches fields extraFuel scope (.return value :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_exact hvalue hvalueIR hexact
    hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rcases compileStmtList_core_ok (fields := fields)
      (inScopeNames := collectStmtBindNames (.return value) ++ inScopeNames) hrest with
    ⟨tailIR, htailCompile⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_return_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_return_cons_extraFuel hIR hsrc hlt hexact hbounded hruntime

private theorem coreListExecMatches_stop
    {fields : List Field} {extraFuel : Nat} {scope : List String} {rest : List Stmt}
    (hrest : StmtListCompileCore scope rest) :
    CoreListExecMatches fields extraFuel scope (.stop :: rest) := by
  intro runtime state inScopeNames _ hexact hbounded hruntime
  rcases compileStmtList_core_ok (fields := fields)
      (inScopeNames := collectStmtBindNames (.stop) ++ inScopeNames) hrest with
    ⟨tailIR, htailCompile⟩
  exact ⟨_, compileStmtList_core_cons_ok compileStmt_stop_eq htailCompile,
    stmtResultMatches_stop_cons_extraFuel hexact hbounded hruntime⟩

private theorem coreListExecMatches_mstore
    {fields : List Field} {extraFuel : Nat} {scope : List String} {offset value : Expr}
    {rest : List Stmt}
    (hoffset : ExprCompileCore offset) (hinScopeOffset : exprBoundNamesInScope offset scope)
    (hvalue : ExprCompileCore value) (hinScopeValue : exprBoundNamesInScope value scope)
    (ih : CoreListExecMatches fields extraFuel scope rest) :
    CoreListExecMatches fields extraFuel scope (.mstore offset value :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨o, hIROffset, hoffSrc, hoffLt⟩ := exists_eval_compileExpr_core_of_exact hoffset
    hoffsetIR hexact hbounded (exprBoundNamesPresent_of_scope hscope hinScopeOffset) hruntime
  obtain ⟨v, hIRValue, hvalSrc, -⟩ := exists_eval_compileExpr_core_of_exact hvalue
    hvalueIR hexact hbounded (exprBoundNamesPresent_of_scope hscope hinScopeValue) hruntime
  rcases ih { runtime with world := runtime.world.writePhysicalMemoryValue o v }
      (state.writePhysicalMemoryValue o v)
      (collectStmtBindNames (.mstore offset value) ++ inScopeNames)
      hscope (bindingsExactlyMatchIRVars_setMemory hexact o v) hbounded
      (runtimeStateMatchesIR_writePhysicalMemoryValue hruntime o v) with
    ⟨tailIR, htailCompile, htailSem, htailExact⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_mstore_eq_of_compileExpr hoffsetIR hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_extraFuel (execStmtList_mstore_cons_eq hoffSrc hvalSrc)
    (by simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, Nat.mod_eq_of_lt hoffLt])
    htailSem htailExact

private theorem coreListExecMatches_tstore
    {fields : List Field} {extraFuel : Nat} {scope : List String} {offset value : Expr}
    {rest : List Stmt}
    (hoffset : ExprCompileCore offset) (hinScopeOffset : exprBoundNamesInScope offset scope)
    (hvalue : ExprCompileCore value) (hinScopeValue : exprBoundNamesInScope value scope)
    (ih : CoreListExecMatches fields extraFuel scope rest) :
    CoreListExecMatches fields extraFuel scope (.tstore offset value :: rest) := by
  intro runtime state inScopeNames hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨o, hIROffset, hoffSrc, -⟩ := exists_eval_compileExpr_core_of_exact hoffset
    hoffsetIR hexact hbounded (exprBoundNamesPresent_of_scope hscope hinScopeOffset) hruntime
  obtain ⟨v, hIRValue, hvalSrc, hvalLt⟩ := exists_eval_compileExpr_core_of_exact hvalue
    hvalueIR hexact hbounded (exprBoundNamesPresent_of_scope hscope hinScopeValue) hruntime
  rcases ih
      { runtime with world := runtime.world.writeTransient (o % Compiler.Constants.evmModulus) v }
      { state with transientStorage := fun k =>
          if k = o % Compiler.Constants.evmModulus then v else state.transientStorage k }
      (collectStmtBindNames (.tstore offset value) ++ inScopeNames)
      hscope (bindingsExactlyMatchIRVars_setTransientStorage hexact _ v) hbounded
      (runtimeStateMatchesIR_setTransientStorage hruntime _ v hvalLt) with
    ⟨tailIR, htailCompile, htailSem, htailExact⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_tstore_eq_of_compileExpr hoffsetIR hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_extraFuel (execStmtList_tstore_cons_eq hoffSrc hvalSrc)
    (by simp [execIRStmt, evalIRExprs, hIROffset, hIRValue]) htailSem htailExact

theorem exec_compileStmtList_core_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope inScopeNames : List String} {stmts : List Stmt}
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
  have key : CoreListExecMatches fields extraFuel scope stmts := by
    clear hscope
    induction hcore with
    | nil => exact coreListExecMatches_nil
    | letVar hv hs _ ih => exact coreListExecMatches_letVar hv hs ih
    | assignVar hv hs _ ih => exact coreListExecMatches_assignVar hv hs ih
    | require_ hc hs _ ih => exact coreListExecMatches_require hc hs ih
    | return_ hv hs hrest => exact coreListExecMatches_return hv hs hrest
    | stop hrest => exact coreListExecMatches_stop hrest
    | mstore ho hso hv hsv _ ih => exact coreListExecMatches_mstore ho hso hv hsv ih
    | tstore ho hso hv hsv _ ih => exact coreListExecMatches_tstore ho hso hv hsv ih
  exact key runtime state inScopeNames hscope hexact hbounded hruntime

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
  exact exec_compileStmtList_core_extraFuel 0 hcore hscope hexact hbounded hruntime

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
  rw [execIRStmt_if_true_of_eval_nonzeroFuel _ _ _ _ _
      (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      (by simp [evalIRExpr]) hcondNonzero,
    compiled_terminal_ite_body_thenBranch_execFuel_eq, Nat.sub_sub]

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
  rw [execIRStmt_if_true_of_eval_nonzeroFuel _ _ _ _ 1
      (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      (evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero)
      (by decide),
    compiled_terminal_ite_body_elseBranch_execFuel_eq, Nat.sub_sub]

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
  rw [execIRStmt_if_true_of_eval_nonzeroFuel _ _ _ _ 1
      (compiled_terminal_ite_body_elseIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      (evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero)
      (by decide),
    compiled_terminal_ite_body_elseBranch_tailExecFuel_eq, Nat.sub_sub]

/-- Executing a compiled terminal `ite` reduces to executing its two guarded `if`s from the
state that caches the condition. -/
private theorem execIRStmts_compiled_terminal_ite_of_ifs
    (extraFuel : Nat) (state : IRState) (tempName : String) (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) (condValue : Nat) (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue)
    (hifs : execIRStmts
      (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) + extraFuel - 2)
      (state.setVar tempName condValue)
      [ YulStmt.if_ (YulExpr.ident tempName) thenIR
      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) + extraFuel + 1)
      state (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) = irExec := by
  have hge := (compiled_terminal_ite_body_size_ge_branchExecFuel
    tempName condIR thenIR elseIR tailIR).1
  have hne := compiled_terminal_ite_body_blockStmtFuel_ne_zero
    extraFuel tempName condIR thenIR elseIR tailIR
  have hlet := execIRStmt_compiled_terminal_ite_let
    extraFuel state tempName condIR thenIR elseIR tailIR condValue hcond
  generalize sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) =
    size at hge hne hlet hifs ⊢
  refine execIRStmts_cons_of_execIRStmt_noncontinue_anyFuel _ _ _ _
    (execIRStmt_block_of_execIRStmts_noncontinue_nonzeroFuel _ _ _ hne ?_ hirNoContinue)
    hirNoContinue
  rw [show size + extraFuel - 1 = size + extraFuel - 2 + 1 by omega,
    execIRStmts_cons_of_execIRStmt_continue_anyFuel _ _ _ _ _ hlet]
  exact hifs

private theorem execIRStmts_compiled_terminal_ite_then_of_irExec
    (extraFuel : Nat) (state : IRState) (tempName : String) (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) (condValue : Nat) (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue) (hcondNonzero : condValue ≠ 0)
    (hthenExec : execIRStmts (sizeOf thenIR +
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) -
          (sizeOf thenIR + 5) + extraFuel) + 1)
      (state.setVar tempName condValue) thenIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) + extraFuel + 1)
      state (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) = irExec := by
  refine execIRStmts_compiled_terminal_ite_of_ifs extraFuel state tempName condIR thenIR elseIR
    tailIR condValue irExec hcond ?_ hirNoContinue
  have hge := (compiled_terminal_ite_body_size_ge_branchExecFuel
    tempName condIR thenIR elseIR tailIR).1
  have hthen := (execIRStmt_compiled_terminal_ite_then_branch_entry
    extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondNonzero).trans hthenExec
  generalize sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) =
    size at hge hthen ⊢
  rw [show size + extraFuel - 2 = size + extraFuel - 3 + 1 by omega]
  exact execIRStmts_cons_of_execIRStmt_noncontinue_anyFuel _ _ _ _ hthen hirNoContinue

private theorem execIRStmts_compiled_terminal_ite_else_of_irExec
    (extraFuel : Nat) (state : IRState) (tempName : String) (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) (condValue : Nat) (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue) (hcondZero : condValue = 0)
    (helseExec : execIRStmts (sizeOf elseIR +
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) -
          (sizeOf elseIR + 5) + extraFuel))
      (state.setVar tempName condValue) elseIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) + extraFuel + 1)
      state (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) = irExec := by
  refine execIRStmts_compiled_terminal_ite_of_ifs extraFuel state tempName condIR thenIR elseIR
    tailIR condValue irExec hcond ?_ hirNoContinue
  obtain ⟨hgeThen, hgeElse⟩ := compiled_terminal_ite_body_size_ge_branchExecFuel
    tempName condIR thenIR elseIR tailIR
  have hthen := execIRStmt_compiled_terminal_ite_thenIf_false
    extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero
  have helse := (execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel
    extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero).trans helseExec
  generalize sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) =
    size at hgeThen hgeElse hthen helse ⊢
  rw [show size + extraFuel - 2 = size + extraFuel - 3 + 1 by omega,
    execIRStmts_cons_of_execIRStmt_continue_anyFuel _ _ _ _ _ hthen,
    show size + extraFuel - 3 = size + extraFuel - 4 + 1 by omega]
  exact execIRStmts_cons_of_execIRStmt_noncontinue_anyFuel _ _ _ _ helse hirNoContinue

/-- A terminal `ite` whose branches never fall through never falls through. -/
private theorem execStmtList_ite_cons_not_continue
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    (hthen : ∀ next, SourceSemantics.execStmtList fields runtime thenBranch ≠ .continue next)
    (helse : ∀ next, SourceSemantics.execStmtList fields runtime elseBranch ≠ .continue next) :
    ∀ next, SourceSemantics.execStmtList fields runtime
      (.ite cond thenBranch elseBranch :: rest) ≠ .continue next := by
  intro next
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  cases heval : SourceSemantics.evalExpr fields runtime cond with
  | none => simp
  | some resolved =>
      simp only [heval]
      by_cases hne : resolved != 0
      · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
        cases hexec : SourceSemantics.execStmtList fields runtime thenBranch with
        | «continue» next' => exact absurd hexec (hthen next')
        | stop _ | «return» _ _ | revert => simp [hexec]
      · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
        cases hexec : SourceSemantics.execStmtList fields runtime elseBranch with
        | «continue» next' => exact absurd hexec (helse next')
        | stop _ | «return» _ _ | revert => simp [hexec]

theorem execStmtList_terminal_core_not_continue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∀ next, SourceSemantics.execStmtList fields runtime stmts ≠ .continue next := by
  induction hterminal generalizing runtime with
  | ite _ _ _ _ _ ihThen ihElse => exact execStmtList_ite_cons_not_continue ihThen ihElse
  | require_ hcond hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases heval : SourceSemantics.evalExpr fields runtime _ with
      | none => simp
      | some resolved =>
          simp only [heval]
          by_cases hne : resolved != 0 <;> simp_all
  | return_ =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp
  | stop => simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  | letVar _ _ _ ih | assignVar _ _ _ ih | mstore _ _ _ _ _ ih | tstore _ _ _ _ _ ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      repeat' (cases SourceSemantics.evalExpr fields runtime _ <;> simp_all)

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
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt}
    {extraFuel : Nat} {tempName : String} {condIR : YulExpr} {thenIR elseIR tailIR : List YulStmt}
    {condValue sourceCondValue : Nat} {irExec : IRExecResult}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hmatch : stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime thenBranch) irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondTrue : sourceCondValue != 0)
    (hcond : evalIRExpr state condIR = some condValue) (hcondNonzero : condValue ≠ 0)
    (hthenExec : execIRStmts (sizeOf thenIR +
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) -
          (sizeOf thenIR + 5) + extraFuel) + 1)
      (state.setVar tempName condValue) thenIR = irExec) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) +
          extraFuel + 1)
        state (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR)) := by
  rw [execStmtList_terminal_core_ite_then_eq hthen hcondEval hcondTrue,
    execIRStmts_compiled_terminal_ite_then_of_irExec extraFuel state tempName condIR thenIR
      elseIR tailIR condValue irExec hcond hcondNonzero hthenExec
      (stmtResultMatchesIRExec_ir_not_continue_of_terminal_core hthen hmatch)]
  exact hmatch

theorem stmtResultMatchesIRExec_compiled_terminal_ite_else
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt}
    {extraFuel : Nat} {tempName : String} {condIR : YulExpr} {thenIR elseIR tailIR : List YulStmt}
    {condValue sourceCondValue : Nat} {irExec : IRExecResult}
    (helse : StmtListTerminalCore scope elseBranch)
    (hmatch : stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime elseBranch) irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondFalse : (sourceCondValue != 0) = false)
    (hcond : evalIRExpr state condIR = some condValue) (hcondZero : condValue = 0)
    (helseExec : execIRStmts (sizeOf elseIR +
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) -
          (sizeOf elseIR + 5) + extraFuel))
      (state.setVar tempName condValue) elseIR = irExec) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts
        (sizeOf (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR) +
          extraFuel + 1)
        state (compiledTerminalIteIR(tempName, condIR, thenIR, elseIR) ++ tailIR)) := by
  rw [execStmtList_terminal_core_ite_else_eq helse hcondEval hcondFalse,
    execIRStmts_compiled_terminal_ite_else_of_irExec extraFuel state tempName condIR thenIR
      elseIR tailIR condValue irExec hcond hcondZero helseExec
      (stmtResultMatchesIRExec_ir_not_continue_of_terminal_core helse hmatch)]
  exact hmatch

/-- A compiled core expression evaluates in IR to its source value, which is
bounded by the EVM modulus. -/
private theorem exists_eval_compileExpr_core_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {value : Expr} {valueIR : YulExpr}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ v, evalIRExpr state valueIR = some v ∧
      SourceSemantics.evalExpr fields runtime value = some v ∧
      v < Compiler.Constants.evmModulus := by
  have heval := eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  have hlt := evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp only [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    rw [← heval] at hlt
    exact ⟨v, rfl, heval.symm, by simpa using hlt⟩

/-- `exists_eval_compileExpr_core_of_scope` specialised to a known source value. -/
private theorem evalIRExpr_compileExpr_core_of_scope_of_eval
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {value : Expr} {valueIR : YulExpr} {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat) :
    evalIRExpr state valueIR = some valueNat ∧ valueNat < Compiler.Constants.evmModulus := by
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_scope hcore hvalueIR hexact
    hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  obtain rfl : v = valueNat := Option.some.inj (hsrc.symm.trans hValueEval)
  exact ⟨hIR, hlt⟩

/-- The compiled `return` prefix `mstore(0, v); return(0, 32)` halts with `v`
under whole-list fuel. -/
private theorem execIRStmts_mstore_return32_append_wholeFuel
    {state : IRState} {valueIR : YulExpr} {tailIR : List YulStmt} {extraFuel v : Nat}
    (hIR : evalIRExpr state valueIR = some v)
    (hlt : v < Compiler.Constants.evmModulus) :
    execIRStmts
        (sizeOf
          ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
            tailIR) + extraFuel + 1) state
        ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR) =
      .return v (state.writePhysicalMemoryValue 0 v) := by
  have hlen := yulStmtList_length_le_sizeOf
    ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
     , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR)
  have hlen2 :
      2 ≤ ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
            tailIR).length := by
    simp
  refine execIRStmts_two_append_of_continue_then_return_wholeFuel extraFuel state
    (state.writePhysicalMemoryValue 0 v) _ _ _ tailIR v ?_ ?_
  · simpa using execIRStmt_mstore_of_eval_nonzeroFuel _ state 0 valueIR v (by omega) hIR
  · simpa [Nat.mod_eq_of_lt hlt] using
      execIRStmt_return32_of_memory_nonzeroFuel _ (state.writePhysicalMemoryValue 0 v) 0
        (by omega)

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
    let state' := state.writePhysicalMemoryValue 0 retVal
    ∃ valueIR,
      CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
      execIRStmts
        (sizeOf
            ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel + 1)
        state
        ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR) =
        .return retVal state' := by
  rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_scope hcore hvalueIR hexact
    hinScope hbounded hpresent hruntime
  rw [hsrc]
  exact ⟨valueIR, hvalueIR, execIRStmts_mstore_return32_append_wholeFuel hIR hlt⟩

theorem execIRStmts_compiled_stop_core_append_wholeFuel
    {state : IRState}
    {tailIR : List YulStmt}
    {extraFuel : Nat} :
    execIRStmts
      (sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) =
      .stop state := by
  have hstopFuelNeZero :
      sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) + extraFuel ≠ 0 := by
    have hprefixLen :
        1 ≤ ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR).length := by
      simp
    have hlen :
        ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR).length ≤
          sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) := by
      exact yulStmtList_length_le_sizeOf _
    omega
  have hstop :
      execIRStmt
          (sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
          state
          (YulStmt.exprStmt (YulExpr.call "stop" [])) =
        .stop state := by
    exact execIRStmt_stop_nonzeroFuel
      (fuel := sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
      (state := state)
      hstopFuelNeZero
  exact execIRStmts_singleton_append_of_execIRStmt_stop_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.exprStmt (YulExpr.call "stop" []))
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

/-- Binding a bounded value re-establishes the scoped exact-state invariants. -/
private theorem setVar_bindValue_invariants_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {name : String} {valueNat : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hlt : valueNat < Compiler.Constants.evmModulus) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    runtimeStateMatchesIR fields runtime' state' ∧
      bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
      bindingsBounded runtime'.bindings ∧
      scopeNamesPresent (name :: scope) runtime'.bindings :=
  ⟨runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat,
    bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact,
    bindingsBounded_bindValue hbounded name valueNat hlt,
    scopeNamesPresent_cons_bindValue hscope⟩

/-- Shared `let`/`assign` head step under whole-list fuel. -/
private theorem execIRStmts_setVar_append_wholeFuel_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {name : String} {stmt : YulStmt} {tailIR : List YulStmt}
    {extraFuel valueNat : Nat}
    (hstep : ∀ fuel, fuel ≠ 0 →
      execIRStmt fuel state stmt = .continue (state.setVar name valueNat))
    (hlt : valueNat < Compiler.Constants.evmModulus)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    execIRStmts (sizeOf ([stmt] ++ tailIR) + extraFuel + 1) state ([stmt] ++ tailIR) =
        execIRStmts (sizeOf ([stmt] ++ tailIR) + extraFuel) state' tailIR ∧
      runtimeStateMatchesIR fields runtime' state' ∧
      bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
      bindingsBounded runtime'.bindings ∧
      scopeNamesPresent (name :: scope) runtime'.bindings :=
  ⟨execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel _ _ _ _ _
      (hstep _ (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)),
    setVar_bindValue_invariants_of_scope hexact hscope hbounded hruntime hlt⟩

/-- Shared `let`/`assign` head step, handing the tail its own extra fuel. -/
private theorem execIRStmts_setVar_append_tailExtraFuel_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {name : String} {stmt : YulStmt} {tailIR : List YulStmt}
    {extraFuel valueNat : Nat}
    (hstep : ∀ fuel, fuel ≠ 0 →
      execIRStmt fuel state stmt = .continue (state.setVar name valueNat))
    (hlt : valueNat < Compiler.Constants.evmModulus)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    {irExec : IRExecResult}
    (htail :
      execIRStmts
        (sizeOf tailIR + (sizeOf ([stmt] ++ tailIR) - (sizeOf tailIR + 1) + extraFuel) + 1)
        (state.setVar name valueNat) tailIR = irExec) :
    let runtime' :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' := state.setVar name valueNat
    execIRStmts (sizeOf ([stmt] ++ tailIR) + extraFuel + 1) state ([stmt] ++ tailIR) = irExec ∧
      runtimeStateMatchesIR fields runtime' state' ∧
      bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
      bindingsBounded runtime'.bindings ∧
      scopeNamesPresent (name :: scope) runtime'.bindings :=
  ⟨execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel _ _ _ _ _ _
      (hstep _ (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)) htail,
    setVar_bindValue_invariants_of_scope hexact hscope hbounded hruntime hlt⟩

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
  obtain ⟨hIR, hlt⟩ := evalIRExpr_compileExpr_core_of_scope_of_eval hcore hvalueIR hexact
    hinScope hscope hbounded hruntime hValueEval
  exact ⟨valueIR, hvalueIR, execIRStmts_setVar_append_wholeFuel_of_scope
    (fun fuel hfuel =>
      execIRStmt_let_of_eval_nonzeroFuel fuel state name valueIR valueNat hfuel hIR)
    hlt hexact hscope hbounded hruntime⟩

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
  obtain ⟨hIR, hlt⟩ := evalIRExpr_compileExpr_core_of_scope_of_eval hcore hvalueIR hexact
    hinScope hscope hbounded hruntime hValueEval
  exact execIRStmts_setVar_append_tailExtraFuel_of_scope
    (fun fuel hfuel =>
      execIRStmt_let_of_eval_nonzeroFuel fuel state name valueIR valueNat hfuel hIR)
    hlt hexact hscope hbounded hruntime htail

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
  obtain ⟨hIR, hlt⟩ := evalIRExpr_compileExpr_core_of_scope_of_eval hcore hvalueIR hexact
    hinScope hscope hbounded hruntime hValueEval
  exact ⟨valueIR, hvalueIR, execIRStmts_setVar_append_wholeFuel_of_scope
    (fun fuel hfuel =>
      execIRStmt_assign_of_eval_nonzeroFuel fuel state name valueIR valueNat hfuel hIR)
    hlt hexact hscope hbounded hruntime⟩

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
  obtain ⟨hIR, hlt⟩ := evalIRExpr_compileExpr_core_of_scope_of_eval hcore hvalueIR hexact
    hinScope hscope hbounded hruntime hValueEval
  exact execIRStmts_setVar_append_tailExtraFuel_of_scope
    (fun fuel hfuel =>
      execIRStmt_assign_of_eval_nonzeroFuel fuel state name valueIR valueNat hfuel hIR)
    hlt hexact hscope hbounded hruntime htail

/-- A passing `require` condition makes its compiled fail condition evaluate to `0`. -/
private theorem evalIRExpr_requireFailCond_eq_zero_of_scope
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope : List String} {cond : Expr} {failCond : YulExpr} {condValue : Nat}
    (hcore : ExprCompileCore cond)
    (hfailCompile :
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondNeZero : condValue ≠ 0) :
    evalIRExpr state failCond = some 0 := by
  rcases eval_compileRequireFailCond_core_of_scope hcore hexact hinScope hbounded
      (exprBoundNamesPresent_of_scope hscope hinScope) hruntime with
    ⟨failCond', hfailCompile', hfailEval⟩
  rw [hfailCompile] at hfailCompile'
  obtain rfl := Except.ok.inj hfailCompile'
  have hdecideFalse :
      decide (SourceSemantics.evalExpr fields runtime cond = some 0) = false := by
    simp [hcondEval, hcondNeZero]
  simpa [SourceSemantics.boolWord, hdecideFalse] using hfailEval

/-- A compiled `require` guard whose fail condition is `1` reverts the whole list. -/
private theorem execIRStmts_if_revertWithMessage_append_wholeFuel
    {state : IRState} {failCond : YulExpr} {message : String} {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hfail : evalIRExpr state failCond = some 1) :
    ∃ revState,
      execIRStmts
          (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) +
            extraFuel + 1) state
          ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) =
        .revert revState := by
  rcases execIRStmts_revertWithMessage_revert (state := state)
      (fuel := sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++
        tailIR) + extraFuel - 1) message with ⟨revState, hrev⟩
  refine ⟨revState, execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel _ _ _ _ _ ?_⟩
  rw [execIRStmt_if_true_of_eval_nonzeroFuel _ _ _ _ _
    (sizeOf_singleton_append_extraFuel_ne_zero _ _ _) hfail (by decide)]
  exact hrev

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
  rcases eval_compileRequireFailCond_core_of_scope hcore hexact hinScope hbounded
      (exprBoundNamesPresent_of_scope hscope hinScope) hruntime with ⟨failCond, hfailCompile, -⟩
  refine ⟨failCond, hfailCompile, ?_⟩
  exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel _ _ _ _ _
    (execIRStmt_if_false_of_eval_nonzeroFuel _ _ _ _ _
      (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
      (evalIRExpr_requireFailCond_eq_zero_of_scope hcore hfailCompile hexact hinScope hscope
        hbounded hruntime hcondEval hcondNeZero) rfl)

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
  exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel _ _ _ _ _ _
    (execIRStmt_if_false_of_eval_nonzeroFuel _ _ _ _ _
      (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
      (evalIRExpr_requireFailCond_eq_zero_of_scope hcore hfailCompile hexact hinScope hscope
        hbounded hruntime hcondEval hcondNeZero) rfl)
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
  rcases eval_compileRequireFailCond_core_of_scope hcore hexact hinScope hbounded
      (exprBoundNamesPresent_of_scope hscope hinScope) hruntime with
    ⟨failCond, hfailCompile, hfailEval⟩
  have hfailEval' : evalIRExpr state failCond = some 1 := by
    simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
  rcases execIRStmts_if_revertWithMessage_append_wholeFuel (message := message)
      (tailIR := tailIR) (extraFuel := extraFuel) hfailEval' with ⟨revState, hrev⟩
  exact ⟨failCond, revState, hfailCompile, hrev⟩

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
  rcases execIRStmts_compiled_let_core_tailExtraFuel_of_scope (name := name) (tailIR := tailIR)
      (extraFuel := extraFuel) hcore hvalueIR hexact hinScope hscope hbounded hruntime
      hValueEval rfl with ⟨hwhole, -⟩
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
  rcases execIRStmts_compiled_assign_core_tailExtraFuel_of_scope (name := name) (tailIR := tailIR)
      (extraFuel := extraFuel) hcore hvalueIR hexact hinScope hscope hbounded hruntime
      hValueEval rfl with ⟨hwhole, -⟩
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
  have hwhole := execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
    (message := message) (tailIR := tailIR) (extraFuel := extraFuel)
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
            ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel + 1)
        state
        ([ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR)) := by
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_scope hcore hvalueIR hexact
    hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rw [execIRStmts_mstore_return32_append_wholeFuel hIR hlt]
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc]
  exact ⟨rfl, runtimeStateMatchesIR_writePhysicalMemoryValue hruntime 0 v⟩

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
        (sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.exprStmt (YulExpr.call "stop" [])] ++ tailIR)) := by
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

theorem scopeNamesIncluded_collectStmtBindNames_tail
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope (collectStmtBindNames stmt ++ inScopeNames) := by
  exact scopeNamesIncluded_append_right (left := collectStmtBindNames stmt) hincluded

theorem scopeNamesIncluded_collectStmtBindNames_letVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded (name :: scope)
      (collectStmtBindNames (.letVar name value) ++ inScopeNames) := by
  intro other hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · simp [collectStmtBindNames]
  · simp [collectStmtBindNames, hincluded other hmem]

theorem scopeNamesIncluded_collectStmtBindNames_assignVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope
      (collectStmtBindNames (.assignVar name value) ++ inScopeNames) := by
  simpa [collectStmtBindNames] using hincluded

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
    CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
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
        (CompilationModel.pickFreshName (CompilationModel.iteCondBaseName thenBranch elseBranch)
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))
        value) := by
  apply bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact
  exact compiled_terminal_ite_temp_not_mem_scope
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) hincluded

/-- Closes a whole-fuel list step whose head continues in both semantics. -/
private theorem stmtResultMatches_cons_continue_sizeOf
    {fields : List Field} {src : SourceSemantics.StmtResult}
    {runtime' : SourceSemantics.RuntimeState} {rest : List Stmt} {state state' : IRState}
    {stmt : YulStmt} {tailIR : List YulStmt} {extraFuel : Nat}
    (hsrc : src = SourceSemantics.execStmtList fields runtime' rest)
    (hstmt : ∀ fuel, fuel ≠ 0 → execIRStmt fuel state stmt = .continue state')
    (htailSem : stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime' rest)
      (execIRStmts (sizeOf tailIR + (extraFuel + sizeOf stmt) + 1) state' tailIR)) :
    stmtResultMatchesIRExec fields src
      (execIRStmts (sizeOf ([stmt] ++ tailIR) + extraFuel + 1) state ([stmt] ++ tailIR)) := by
  rw [execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel extraFuel state state' stmt
    tailIR (hstmt _ (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)), hsrc]
  convert htailSem using 2
  simp
  omega

private theorem execIRStmt_mstore_of_evals_nonzeroFuel
    {fuel : Nat} {state : IRState} {offsetIR valueIR : YulExpr} {offsetNat valueNat : Nat}
    (hfuel : fuel ≠ 0)
    (hoffset : evalIRExpr state offsetIR = some offsetNat)
    (hvalue : evalIRExpr state valueIR = some valueNat)
    (hlt : offsetNat < Compiler.Constants.evmModulus) :
    execIRStmt fuel state (YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])) =
      .continue (state.writePhysicalMemoryValue offsetNat valueNat) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfuel
  simp [execIRStmt, evalIRExprs, hoffset, hvalue, Nat.mod_eq_of_lt hlt]

private theorem execIRStmt_tstore_of_evals_nonzeroFuel
    {fuel : Nat} {state : IRState} {offsetIR valueIR : YulExpr} {offsetNat valueNat : Nat}
    (hfuel : fuel ≠ 0)
    (hoffset : evalIRExpr state offsetIR = some offsetNat)
    (hvalue : evalIRExpr state valueIR = some valueNat) :
    execIRStmt fuel state (YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])) =
      .continue { state with transientStorage := fun k =>
        if k = offsetNat % Compiler.Constants.evmModulus then valueNat
        else state.transientStorage k } := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfuel
  simp [execIRStmt, evalIRExprs, hoffset, hvalue]

private theorem bindingsExactlyMatchIRVarsOnScope_setTransientStorage
    {scope : List String} {bindings : List (String × Nat)} {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state) (key value : Nat) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with transientStorage := fun o =>
          if o = key then value else state.transientStorage o } := by
  intro name hname
  simpa [IRState.getVar] using hexact name hname

private theorem stmtResultMatches_require_cons_sizeOf
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {cond : Expr} {message : String} {rest : List Stmt} {failCond : YulExpr}
    {tailIR : List YulStmt} {extraFuel condVal : Nat}
    (hsrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hfail : evalIRExpr state failCond =
      some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)))
    (htailSem : stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime rest)
      (execIRStmts (sizeOf tailIR + (extraFuel +
        sizeOf (YulStmt.if_ failCond (CompilationModel.revertWithMessage message))) + 1)
        state tailIR)) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.require cond message :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++
          tailIR) + extraFuel + 1) state
        ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)) := by
  by_cases hzero : condVal = 0
  · subst hzero
    rcases execIRStmts_if_revertWithMessage_append_wholeFuel (message := message)
        (tailIR := tailIR) (extraFuel := extraFuel)
        (by simpa [hsrc, SourceSemantics.boolWord] using hfail) with ⟨revState, hrev⟩
    rw [hrev]
    simp [SourceSemantics.execStmtList, SourceSemantics.execStmt, hsrc, stmtResultMatchesIRExec]
  · have hfail0 : evalIRExpr state failCond = some 0 := by
      simpa [hsrc, hzero, SourceSemantics.boolWord] using hfail
    exact stmtResultMatches_cons_continue_sizeOf
      (execStmtList_require_cons_eq_of_ne_zero hsrc hzero)
      (fun fuel hfuel => execIRStmt_if_false_of_eval_nonzeroFuel fuel state failCond _ 0 hfuel
        hfail0 rfl) htailSem

private theorem sizeOf_terminal_ite_else_fuel_eq
    (tempName : String) (condIR : YulExpr) (thenIR elseIR tailIR : List YulStmt)
    (extraFuel : Nat) :
    sizeOf elseIR + (extraFuel + sizeOf (YulStmt.let_ tempName condIR) +
        sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
        sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) + sizeOf tailIR + 1) + 1 =
      sizeOf elseIR +
        (sizeOf ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++
            tailIR) - (sizeOf elseIR + 5) + extraFuel) := by
  simp only [List.singleton_append, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
    YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec, YulStmt.let_.sizeOf_spec,
    YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
  omega

private theorem sizeOf_terminal_ite_then_fuel_eq
    (tempName : String) (condIR : YulExpr) (thenIR elseIR tailIR : List YulStmt)
    (extraFuel : Nat) :
    sizeOf thenIR + (extraFuel + sizeOf (YulStmt.let_ tempName condIR) +
        sizeOf (YulExpr.ident tempName) +
        sizeOf (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) +
        sizeOf tailIR + 2) + 1 =
      sizeOf thenIR +
        (sizeOf ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++
            tailIR) - (sizeOf thenIR + 5) + extraFuel) + 1 := by
  simp only [List.singleton_append, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
    YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec, YulStmt.let_.sizeOf_spec,
    YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
  omega

private theorem stmtResultMatches_terminal_ite_else_of_branch
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope inScopeNames : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt}
    {extraFuel condVal : Nat} {tempName : String} {condIR : YulExpr}
    {thenIR elseIR tailIR : List YulStmt}
    (helse : StmtListTerminalCore scope elseBranch)
    (helseIR : CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      elseBranch = Except.ok elseIR)
    (hbranch : ∀ k, ∃ bodyIR, CompilationModel.compileStmtList fields [] [] .calldata [] false
        inScopeNames [] elseBranch = Except.ok bodyIR ∧
      stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime elseBranch)
        (execIRStmts (sizeOf bodyIR + k + 1) (state.setVar tempName condVal) bodyIR))
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hCondIRVal : evalIRExpr state condIR = some condVal)
    (hcondZero : condVal = 0) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts (sizeOf ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR) +
        extraFuel + 1) state
        ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR)) := by
  rcases hbranch (extraFuel + sizeOf (YulStmt.let_ tempName condIR) +
      sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
      sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) + sizeOf tailIR + 1) with
    ⟨elseIR', helseIR', helseSem⟩
  rw [helseIR] at helseIR'
  obtain rfl := Except.ok.inj helseIR'
  rw [sizeOf_terminal_ite_else_fuel_eq] at helseSem
  exact stmtResultMatchesIRExec_compiled_terminal_ite_else (scope := scope) (rest := rest)
    (tempName := tempName) (condIR := condIR) (thenIR := thenIR) (tailIR := tailIR)
    helse helseSem hCondSrc (by simp [hcondZero]) hCondIRVal hcondZero rfl

private theorem stmtResultMatches_terminal_ite_then_of_branch
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope inScopeNames : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt}
    {extraFuel condVal : Nat} {tempName : String} {condIR : YulExpr}
    {thenIR elseIR tailIR : List YulStmt}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hthenIR : CompilationModel.compileStmtList fields [] [] .calldata [] false inScopeNames []
      thenBranch = Except.ok thenIR)
    (hbranch : ∀ k, ∃ bodyIR, CompilationModel.compileStmtList fields [] [] .calldata [] false
        inScopeNames [] thenBranch = Except.ok bodyIR ∧
      stmtResultMatchesIRExec fields (SourceSemantics.execStmtList fields runtime thenBranch)
        (execIRStmts (sizeOf bodyIR + k + 1) (state.setVar tempName condVal) bodyIR))
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hCondIRVal : evalIRExpr state condIR = some condVal)
    (hcondNonzero : condVal ≠ 0) :
    stmtResultMatchesIRExec fields
      (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
      (execIRStmts (sizeOf ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR) +
        extraFuel + 1) state
        ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR)) := by
  rcases hbranch (extraFuel + sizeOf (YulStmt.let_ tempName condIR) +
      sizeOf (YulExpr.ident tempName) +
      sizeOf (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) +
      sizeOf tailIR + 2) with
    ⟨thenIR', hthenIR', hthenSem⟩
  rw [hthenIR] at hthenIR'
  obtain rfl := Except.ok.inj hthenIR'
  rw [sizeOf_terminal_ite_then_fuel_eq] at hthenSem
  exact stmtResultMatchesIRExec_compiled_terminal_ite_then (scope := scope) (rest := rest)
    (tempName := tempName) (condIR := condIR) (elseIR := elseIR) (tailIR := tailIR)
    hthen hthenSem hCondSrc (by simp [hcondNonzero]) hCondIRVal hcondNonzero rfl

/-- Induction motive of `exec_compileStmtList_terminal_core_sizeOf_extraFuel`. -/
private def TerminalListExecMatches (fields : List Field) (scope : List String)
    (stmts : List Stmt) : Prop :=
  ∀ (extraFuel : Nat) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (inScopeNames : List String),
    scopeNamesIncluded scope inScopeNames →
    scopeNamesPresent scope runtime.bindings →
    bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    bindingsBounded runtime.bindings →
    runtimeStateMatchesIR fields runtime state →
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec

private theorem terminalListExecMatches_letVar
    {fields : List Field} {scope : List String} {name : String} {value : Expr}
    {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (ih : TerminalListExecMatches fields (name :: scope) rest) :
    TerminalListExecMatches fields scope (.letVar name value :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_scope hvalue hvalueIR hexact
    hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  obtain ⟨hruntime', hexact', hbounded', hscope'⟩ :=
    setVar_bindValue_invariants_of_scope (name := name) hexact hscope hbounded hruntime hlt
  rcases ih (extraFuel + sizeOf (YulStmt.let_ name valueIR))
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
      (state.setVar name v) (collectStmtBindNames (.letVar name value) ++ inScopeNames)
      (scopeNamesIncluded_collectStmtBindNames_letVar hincluded)
      hscope' hexact' hbounded' hruntime' with
    ⟨tailIR, htailCompile, htailSem⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_letVar_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_sizeOf (execStmtList_letVar_cons_eq hsrc)
    (fun fuel hfuel => execIRStmt_let_of_eval_nonzeroFuel fuel state name valueIR v hfuel hIR)
    htailSem

private theorem terminalListExecMatches_assignVar
    {fields : List Field} {scope : List String} {name : String} {value : Expr}
    {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (ih : TerminalListExecMatches fields scope rest) :
    TerminalListExecMatches fields scope (.assignVar name value :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨v, hIR, hsrc, hlt⟩ := exists_eval_compileExpr_core_of_scope hvalue hvalueIR hexact
    hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  obtain ⟨hruntime', hexact', hbounded', hscope'⟩ :=
    setVar_bindValue_invariants_of_scope (name := name) hexact hscope hbounded hruntime hlt
  rcases ih (extraFuel + sizeOf (YulStmt.assign name valueIR))
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v }
      (state.setVar name v) (collectStmtBindNames (.assignVar name value) ++ inScopeNames)
      (scopeNamesIncluded_collectStmtBindNames_assignVar hincluded)
      (fun other hmem => hscope' other (List.mem_cons_of_mem name hmem))
      (fun other hmem => hexact' other (List.mem_cons_of_mem name hmem))
      hbounded' hruntime' with
    ⟨tailIR, htailCompile, htailSem⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_assignVar_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_sizeOf (execStmtList_assignVar_cons_eq hsrc)
    (fun fuel hfuel => execIRStmt_assign_of_eval_nonzeroFuel fuel state name valueIR v hfuel hIR)
    htailSem

private theorem terminalListExecMatches_require
    {fields : List Field} {scope : List String} {cond : Expr} {message : String}
    {rest : List Stmt}
    (hcond : ExprCompileCore cond) (hinScope : exprBoundNamesInScope cond scope)
    (ih : TerminalListExecMatches fields scope rest) :
    TerminalListExecMatches fields scope (.require cond message :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  have hpresent := exprBoundNamesPresent_of_scope hscope hinScope
  rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
  obtain ⟨condVal, -, hCondSrc, -⟩ := exists_eval_compileExpr_core_of_scope hcond hcondIR
    hexact hinScope hbounded hpresent hruntime
  rcases eval_compileRequireFailCond_core_of_scope hcond hexact hinScope hbounded hpresent
      hruntime with ⟨failCond, hfailCompile, hfailEval⟩
  rcases ih (extraFuel + sizeOf (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)))
      runtime state (collectStmtBindNames (.require cond message) ++ inScopeNames)
      (scopeNamesIncluded_collectStmtBindNames_tail hincluded)
      hscope hexact hbounded hruntime with
    ⟨tailIR, htailCompile, htailSem⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_require_eq_of_compileRequireFailCond hfailCompile) htailCompile, ?_⟩
  exact stmtResultMatches_require_cons_sizeOf hCondSrc hfailEval htailSem

private theorem terminalListExecMatches_return
    {fields : List Field} {scope : List String} {value : Expr} {rest : List Stmt}
    (hvalue : ExprCompileCore value) (hinScope : exprBoundNamesInScope value scope)
    (hrest : StmtListCompileCore scope rest) :
    TerminalListExecMatches fields scope (.return value :: rest) := by
  intro extraFuel runtime state inScopeNames _ hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  rcases compileStmtList_core_ok (fields := fields)
      (inScopeNames := collectStmtBindNames (.return value) ++ inScopeNames) hrest with
    ⟨tailIR, htailCompile⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_return_eq_of_compileExpr hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
    hvalue hvalueIR hexact hinScope hscope hbounded hruntime

private theorem terminalListExecMatches_stop
    {fields : List Field} {scope : List String} {rest : List Stmt}
    (hrest : StmtListCompileCore scope rest) :
    TerminalListExecMatches fields scope (.stop :: rest) := by
  intro extraFuel runtime state inScopeNames _ _ _ _ hruntime
  rcases compileStmtList_core_ok (fields := fields)
      (inScopeNames := collectStmtBindNames (.stop) ++ inScopeNames) hrest with
    ⟨tailIR, htailCompile⟩
  exact ⟨_, compileStmtList_core_cons_ok compileStmt_stop_eq htailCompile,
    stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel hruntime⟩

private theorem terminalListExecMatches_mstore
    {fields : List Field} {scope : List String} {offset value : Expr} {rest : List Stmt}
    (hoffset : ExprCompileCore offset) (hinScopeOffset : exprBoundNamesInScope offset scope)
    (hvalue : ExprCompileCore value) (hinScopeValue : exprBoundNamesInScope value scope)
    (ih : TerminalListExecMatches fields scope rest) :
    TerminalListExecMatches fields scope (.mstore offset value :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨o, hIROffset, hoffSrc, hoffLt⟩ := exists_eval_compileExpr_core_of_scope hoffset
    hoffsetIR hexact hinScopeOffset hbounded
    (exprBoundNamesPresent_of_scope hscope hinScopeOffset) hruntime
  obtain ⟨v, hIRValue, hvalSrc, -⟩ := exists_eval_compileExpr_core_of_scope hvalue
    hvalueIR hexact hinScopeValue hbounded
    (exprBoundNamesPresent_of_scope hscope hinScopeValue) hruntime
  rcases ih (extraFuel + sizeOf (YulStmt.exprStmt (YulExpr.call "mstore" [offsetIR, valueIR])))
      { runtime with world := runtime.world.writePhysicalMemoryValue o v }
      (state.writePhysicalMemoryValue o v)
      (collectStmtBindNames (.mstore offset value) ++ inScopeNames)
      (scopeNamesIncluded_collectStmtBindNames_tail hincluded) hscope
      (bindingsExactlyMatchIRVarsOnScope_setMemory hexact o v) hbounded
      (runtimeStateMatchesIR_writePhysicalMemoryValue hruntime o v) with
    ⟨tailIR, htailCompile, htailSem⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_mstore_eq_of_compileExpr hoffsetIR hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_sizeOf (execStmtList_mstore_cons_eq hoffSrc hvalSrc)
    (fun _ hfuel => execIRStmt_mstore_of_evals_nonzeroFuel hfuel hIROffset hIRValue hoffLt)
    htailSem

private theorem terminalListExecMatches_tstore
    {fields : List Field} {scope : List String} {offset value : Expr} {rest : List Stmt}
    (hoffset : ExprCompileCore offset) (hinScopeOffset : exprBoundNamesInScope offset scope)
    (hvalue : ExprCompileCore value) (hinScopeValue : exprBoundNamesInScope value scope)
    (ih : TerminalListExecMatches fields scope rest) :
    TerminalListExecMatches fields scope (.tstore offset value :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  rcases compileExpr_core_ok hoffset with ⟨offsetIR, hoffsetIR⟩
  rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
  obtain ⟨o, hIROffset, hoffSrc, -⟩ := exists_eval_compileExpr_core_of_scope hoffset
    hoffsetIR hexact hinScopeOffset hbounded
    (exprBoundNamesPresent_of_scope hscope hinScopeOffset) hruntime
  obtain ⟨v, hIRValue, hvalSrc, hvalLt⟩ := exists_eval_compileExpr_core_of_scope hvalue
    hvalueIR hexact hinScopeValue hbounded
    (exprBoundNamesPresent_of_scope hscope hinScopeValue) hruntime
  rcases ih (extraFuel + sizeOf (YulStmt.exprStmt (YulExpr.call "tstore" [offsetIR, valueIR])))
      { runtime with world := runtime.world.writeTransient (o % Compiler.Constants.evmModulus) v } _
      (collectStmtBindNames (.tstore offset value) ++ inScopeNames)
      (scopeNamesIncluded_collectStmtBindNames_tail hincluded) hscope
      (bindingsExactlyMatchIRVarsOnScope_setTransientStorage hexact
        (o % Compiler.Constants.evmModulus) v) hbounded
      (runtimeStateMatchesIR_setTransientStorage hruntime _ v hvalLt) with
    ⟨tailIR, htailCompile, htailSem⟩
  refine ⟨_, compileStmtList_core_cons_ok
    (compileStmt_tstore_eq_of_compileExpr hoffsetIR hvalueIR) htailCompile, ?_⟩
  exact stmtResultMatches_cons_continue_sizeOf (execStmtList_tstore_cons_eq hoffSrc hvalSrc)
    (fun _ hfuel => execIRStmt_tstore_of_evals_nonzeroFuel hfuel hIROffset hIRValue)
    htailSem

private theorem terminalListExecMatches_ite
    {fields : List Field} {scope : List String} {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    (hcond : ExprCompileCore cond) (hinScope : exprBoundNamesInScope cond scope)
    (hthen : StmtListTerminalCore scope thenBranch) (helse : StmtListTerminalCore scope elseBranch)
    (hrest : StmtListCompileCore scope rest)
    (ihThen : TerminalListExecMatches fields scope thenBranch)
    (ihElse : TerminalListExecMatches fields scope elseBranch) :
    TerminalListExecMatches fields scope (.ite cond thenBranch elseBranch :: rest) := by
  intro extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime
  obtain ⟨bodyIR, hbody⟩ := compileStmtList_terminal_core_ok (fields := fields)
    (inScopeNames := inScopeNames) (.ite hcond hinScope hthen helse hrest)
  refine ⟨bodyIR, hbody, ?_⟩
  obtain ⟨condIR, thenIR, elseIR, -, -, hcondIR, hthenIR, helseIR, -, rfl, rfl⟩ :=
    compileStmtList_terminal_ite_ok_inv (isEmpty_eq_false_of_stmtListTerminalCore helse) hbody
  obtain ⟨condVal, hCondIRVal, hCondSrc, -⟩ := exists_eval_compileExpr_core_of_scope hcond
    hcondIR hexact hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  have hexact' := bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) (value := condVal)
    hexact hincluded
  by_cases hcondZero : condVal = 0
  · exact stmtResultMatches_terminal_ite_else_of_branch helse helseIR
      (fun k => ihElse k _ _ _ hincluded hscope hexact' hbounded hruntime)
      hCondSrc hCondIRVal hcondZero
  · exact stmtResultMatches_terminal_ite_then_of_branch hthen hthenIR
      (fun k => ihThen k _ _ _ hincluded hscope hexact' hbounded hruntime)
      hCondSrc hCondIRVal hcondZero

theorem exec_compileStmtList_terminal_core_sizeOf_extraFuel
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {scope inScopeNames : List String} {stmts : List Stmt}
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
  have key : TerminalListExecMatches fields scope stmts := by
    clear hincluded hscope hexact
    induction hterminal with
    | letVar hv hs _ ih => exact terminalListExecMatches_letVar hv hs ih
    | assignVar hv hs _ ih => exact terminalListExecMatches_assignVar hv hs ih
    | require_ hc hs _ ih => exact terminalListExecMatches_require hc hs ih
    | return_ hv hs hrest => exact terminalListExecMatches_return hv hs hrest
    | stop hrest => exact terminalListExecMatches_stop hrest
    | mstore ho hso hv hsv _ ih => exact terminalListExecMatches_mstore ho hso hv hsv ih
    | tstore ho hso hv hsv _ ih => exact terminalListExecMatches_tstore ho hso hv hsv ih
    | ite hc hs ht he hr iht ihe => exact terminalListExecMatches_ite hc hs ht he hr iht ihe
  exact key extraFuel runtime state inScopeNames hincluded hscope hexact hbounded hruntime

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
