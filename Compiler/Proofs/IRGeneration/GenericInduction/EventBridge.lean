import Compiler.Proofs.IRGeneration.GenericInduction.Storage

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Event emission semantic bridge

Proves that the compiled scalar `.emit` block (free-pointer scratch, signature
stores, `keccak256` topic0, unindexed head stores, `logN`) matches the source
event semantics, discharging `EventHeadStepSemanticBridgeCatalog.bridge`.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-! ## Fuel arithmetic helpers -/

private theorem length_le_sizeOf (stmts : List YulStmt) :
    stmts.length ≤ sizeOf stmts := by
  induction stmts with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.cons.sizeOf_spec]
      omega

private theorem eventSingletonBlock_sizeOf_slack (body : List YulStmt) :
    sizeOf [YulStmt.block body] - [YulStmt.block body].length = sizeOf body + 2 := by
  simp [YulStmt.block.sizeOf_spec]
  omega

private theorem eventExecIRStmts_single_block_of_continue
    (fuel : Nat)
    (state next : IRState)
    (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts (fuel + 2) state [YulStmt.block body] = .continue next := by
  have hblock :
      execIRStmt (fuel + 1) state (YulStmt.block body) = .continue next := by
    simpa [execIRStmt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbody
  simpa [execIRStmts, hblock]

/-! ## Source expression-list evaluation -/

private theorem eventEvalExprList_eq_mapM
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (exprs : List Expr) :
    SourceSemantics.evalExprList fields state exprs =
      exprs.mapM (SourceSemantics.evalExpr fields state) := by
  induction exprs with
  | nil => rfl
  | cons expr rest ih =>
      simp [SourceSemantics.evalExprList, ih]

private theorem eventExprList_all_helperSurfaceClosed_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
  induction exprs with
  | nil =>
      simp
  | cons expr rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hsurface
      have hhead :=
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1
      simp only [List.all_cons, BEq.rfl, Bool.and_eq_true]
      exact ⟨by simpa [hhead], ih hsurface.2⟩

private theorem eventEvalExprListWithHelpers_eq_evalExprList_of_contractSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : SourceSemantics.RuntimeState)
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    SourceSemantics.evalExprListWithHelpers spec fields fuel state exprs =
      SourceSemantics.evalExprList fields state exprs := by
  rw [SourceSemantics.evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed]
  · exact (eventEvalExprList_eq_mapM fields state exprs).symm
  · exact eventExprList_all_helperSurfaceClosed_of_contractSurfaceClosed hsurface

private theorem eventEvalExprList_values_lt
    {fields : List Field} {scope : List String}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {args : List Expr} {values : List Nat}
    (hcore : ∀ expr ∈ args, FunctionBody.ExprCompileCore expr)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
      scope runtime.bindings state)
    (hinScope : ∀ expr ∈ args, FunctionBody.exprBoundNamesInScope expr scope)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (heval : SourceSemantics.evalExprList fields runtime args = some values) :
    ∀ value ∈ values, value < Compiler.Constants.evmModulus := by
  induction args generalizing values with
  | nil =>
      simp [SourceSemantics.evalExprList] at heval
      subst values
      simp
  | cons expr rest ih =>
      cases hhead : SourceSemantics.evalExpr fields runtime expr with
      | none =>
          simp [SourceSemantics.evalExprList, hhead] at heval
      | some headValue =>
          cases htail : SourceSemantics.evalExprList fields runtime rest with
          | none =>
              simp [SourceSemantics.evalExprList, hhead, htail] at heval
          | some tailValues =>
              simp [SourceSemantics.evalExprList, hhead, htail] at heval
              subst values
              simp only [List.mem_cons, forall_eq_or_imp]
              constructor
              · have hsrcLt := FunctionBody.evalExpr_lt_evmModulus_core_onExpr
                  (hcore expr (by simp))
                  (FunctionBody.bindingsExactlyMatchIRVarsOnScope_implies_onExpr
                    hexact (hinScope expr (by simp)))
                  hbounded
                  (FunctionBody.exprBoundNamesPresent_of_scope hscope
                    (hinScope expr (by simp)))
                  hruntime
                simpa [hhead] using hsrcLt
              · exact ih
                  (by intro e he; exact hcore e (by simp [he]))
                  (by intro e he; exact hinScope e (by simp [he]))
                  htail

private theorem eventExprList_compile_core_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr := by
  intro expr hmem
  have hnotTrue :
      ¬ exprTouchesUnsupportedContractSurface expr = true :=
    (List.any_eq_false.mp hsurface) expr hmem
  have hclosed : exprTouchesUnsupportedContractSurface expr = false := by
    cases h : exprTouchesUnsupportedContractSurface expr <;> simp [h] at hnotTrue ⊢
  exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hclosed

private theorem eventEncodeEvents_snoc
    (events : List Verity.Event) (event : Verity.Event) :
    SourceSemantics.encodeEvents (events ++ [event]) =
      SourceSemantics.encodeEvents events ++ [SourceSemantics.encodeEvent event] := by
  simp [SourceSemantics.encodeEvents]

/-! ## Final-state-tracking statement continuation

`StmtsContinueFrom` (IRInterpreter.lean) only yields an existential final
state. The event bridge needs the exact final state, so we track it. -/

private def StmtsContinueFromTo (state : IRState) :
    List YulStmt → IRState → Prop
  | [], final => state = final
  | stmt :: rest, final =>
      ∃ state',
        (∀ extraFuel, execIRStmt (extraFuel + 1) state stmt = .continue state') ∧
        StmtsContinueFromTo state' rest final

private theorem execIRStmts_of_StmtsContinueFromTo
    {state final : IRState}
    {stmts : List YulStmt}
    (h : StmtsContinueFromTo state stmts final)
    (extraFuel : Nat) :
    execIRStmts (stmts.length + extraFuel + 1) state stmts = .continue final := by
  induction stmts generalizing state with
  | nil =>
      have hfinal : state = final := h
      subst hfinal
      simp [execIRStmts]
  | cons stmt rest ih =>
      obtain ⟨state', hstep, htail⟩ := h
      have hlen : (stmt :: rest).length + extraFuel + 1 =
          (rest.length + extraFuel + 1) + 1 := by
        simp [List.length_cons]
        omega
      rw [hlen]
      simp only [execIRStmts, hstep (rest.length + extraFuel)]
      exact ih htail

private theorem StmtsContinueFromTo_append
    {state mid final : IRState}
    {front back : List YulStmt}
    (hfront : StmtsContinueFromTo state front mid)
    (hback : StmtsContinueFromTo mid back final) :
    StmtsContinueFromTo state (front ++ back) final := by
  induction front generalizing state with
  | nil =>
      have hmid : state = mid := hfront
      subst hmid
      simpa using hback
  | cons stmt rest ih =>
      obtain ⟨state', hstep, htail⟩ := hfront
      exact ⟨state', hstep, ih htail⟩

/-! ## Atomic argument IR shapes

Compiling an atomic event argument yields a literal, a scope identifier, or a
zero-argument context builtin. These shapes evaluate independently of block
scratch bindings and memory writes. -/

private def AtomicArgIR (scope : List String) (exprIR : YulExpr) : Prop :=
  (∃ n, exprIR = YulExpr.lit n) ∨
  (∃ name, exprIR = YulExpr.ident name ∧ name ∈ scope) ∨
  (∃ func, exprIR = YulExpr.call func [])

private theorem compileExpr_atomic_shape
    {fields : List Field}
    {scope : List String}
    {expr : Expr}
    {exprIR : YulExpr}
    (hatomic : exprEventArgAtomic expr = true)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    AtomicArgIR scope exprIR := by
  cases expr <;> simp [exprEventArgAtomic] at hatomic
  case literal n =>
      refine Or.inl ⟨n % CompilationModel.uint256Modulus, ?_⟩
      simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
  case param name =>
      refine Or.inr (Or.inl ⟨name, ?_, ?_⟩)
      · simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
      · exact hinScope name (by simp [FunctionBody.exprBoundNames])
  case localVar name =>
      refine Or.inr (Or.inl ⟨name, ?_, ?_⟩)
      · simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
      · exact hinScope name (by simp [FunctionBody.exprBoundNames])
  case caller =>
      exact Or.inr (Or.inr ⟨"caller", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case contractAddress =>
      exact Or.inr (Or.inr ⟨"address", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case txOrigin =>
      exact Or.inr (Or.inr ⟨"origin", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case msgValue =>
      exact Or.inr (Or.inr ⟨"callvalue", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockTimestamp =>
      exact Or.inr (Or.inr ⟨"timestamp", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockNumber =>
      exact Or.inr (Or.inr ⟨"number", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case chainid =>
      exact Or.inr (Or.inr ⟨"chainid", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blobbasefee =>
      exact Or.inr (Or.inr ⟨"blobbasefee", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case calldatasize =>
      exact Or.inr (Or.inr ⟨"calldatasize", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)

private theorem eventExprCompileCore_of_exprEventArgAtomic
    {expr : Expr}
    (hatomic : exprEventArgAtomic expr = true) :
    FunctionBody.ExprCompileCore expr := by
  cases expr <;> simp [exprEventArgAtomic] at hatomic <;> constructor

private theorem eventCompileExprList_atomic_shapes
    {fields : List Field} {scope : List String}
    {args : List Expr} {argExprs : List YulExpr}
    (hatomic : args.all exprEventArgAtomic = true)
    (hinScope : ∀ arg ∈ args, FunctionBody.exprBoundNamesInScope arg scope)
    (hcompile :
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs) :
    List.Forall₂ (fun argExpr _ => AtomicArgIR scope argExpr) argExprs args := by
  induction args generalizing argExprs with
  | nil =>
      simp [CompilationModel.compileExprList] at hcompile
      injection hcompile with hargs
      subst hargs
      exact .nil
  | cons arg rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hatomic
      have hheadScope := hinScope arg (by simp)
      have htailScope :
          ∀ tailArg ∈ rest, FunctionBody.exprBoundNamesInScope tailArg scope := by
        intro tailArg hmem
        exact hinScope tailArg (by simp [hmem])
      have hcore : FunctionBody.ExprCompileCore arg :=
        eventExprCompileCore_of_exprEventArgAtomic hatomic.1
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
        ⟨argIR, hargIR⟩
      have htailCore :
          ∀ tailArg ∈ rest, FunctionBody.ExprCompileCore tailArg := by
        intro tailArg hmem
        exact eventExprCompileCore_of_exprEventArgAtomic
          ((List.all_eq_true.mp hatomic.2) tailArg hmem)
      rcases compileExprList_core_ok (fields := fields) htailCore with
        ⟨restIRs, hrestIRs⟩
      rw [CompilationModel.compileExprList, hargIR, hrestIRs] at hcompile
      injection hcompile with hcompiledTail
      subst hcompiledTail
      exact .cons
        (compileExpr_atomic_shape hatomic.1 hheadScope hargIR)
        (ih hatomic.2 htailScope hrestIRs)

/-! ## Stability of atomic argument IR under scratch effects -/

private theorem evalIRCall_nil_setVar
    (state : IRState) (name : String) (value : Nat) (func : String) :
    evalIRCall (state.setVar name value) func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs, IRState.setVar]

private theorem evalIRCall_nil_memory
    (state : IRState) (mem : Nat → Nat) (func : String) :
    evalIRCall { state with memory := mem } func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs]

private theorem evalIRExpr_atomic_setVar
    {scope : List String}
    {exprIR : YulExpr}
    (hshape : AtomicArgIR scope exprIR)
    {name : String}
    (hname : name ∉ scope)
    (state : IRState)
    (value : Nat) :
    evalIRExpr (state.setVar name value) exprIR = evalIRExpr state exprIR := by
  rcases hshape with ⟨n, rfl⟩ | ⟨varName, rfl, hmem⟩ | ⟨func, rfl⟩
  · simp [evalIRExpr]
  · have hne : varName ≠ name := fun h => hname (h ▸ hmem)
    simp only [evalIRExpr]
    exact FunctionBody.getVar_setVar_ne state name varName value hne
  · simp only [evalIRExpr]
    exact evalIRCall_nil_setVar state name value func

private theorem evalIRExpr_atomic_memory
    {scope : List String}
    {exprIR : YulExpr}
    (hshape : AtomicArgIR scope exprIR)
    (state : IRState)
    (mem : Nat → Nat) :
    evalIRExpr { state with memory := mem } exprIR = evalIRExpr state exprIR := by
  rcases hshape with ⟨n, rfl⟩ | ⟨varName, rfl, hmem⟩ | ⟨func, rfl⟩
  · simp [evalIRExpr]
  · simp [evalIRExpr, IRState.getVar]
  · simp only [evalIRExpr]
    exact evalIRCall_nil_memory state mem func

private theorem eventForall₂_eval_atomic_setVar
    {scope : List String} {state : IRState}
    {exprIRs : List YulExpr} {values : List Nat}
    (hshapes : List.Forall₂ (fun exprIR _ => AtomicArgIR scope exprIR)
      exprIRs values)
    (hevals : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value)
      exprIRs values)
    {name : String} (hname : name ∉ scope) (newValue : Nat) :
    List.Forall₂
      (fun exprIR argValue =>
        evalIRExpr (state.setVar name newValue) exprIR = some argValue)
      exprIRs values := by
  induction hshapes with
  | nil => cases hevals; exact .nil
  | cons hshape hshapeTail ih =>
      cases hevals with
      | cons heval hevalTail =>
          exact .cons
            (by
              rw [evalIRExpr_atomic_setVar hshape hname state newValue]
              exact heval)
            (ih hevalTail)

private theorem eventForall₂_eval_atomic_memory
    {scope : List String} {state : IRState}
    {exprIRs : List YulExpr} {values : List Nat}
    (hshapes : List.Forall₂ (fun exprIR _ => AtomicArgIR scope exprIR)
      exprIRs values)
    (hevals : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value)
      exprIRs values)
    (mem : Nat → Nat) :
    List.Forall₂
      (fun exprIR value => evalIRExpr { state with memory := mem } exprIR = some value)
      exprIRs values := by
  induction hshapes with
  | nil => cases hevals; exact .nil
  | cons hshape hshapeTail ih =>
      cases hevals with
      | cons heval hevalTail =>
          exact .cons
            (by
              rw [evalIRExpr_atomic_memory hshape state mem]
              exact heval)
            (ih hevalTail)

private theorem eventForall₂_eval_atomic_setVar_of_args
    {scope : List String} {state : IRState}
    {exprIRs : List YulExpr} {args : List Expr} {values : List Nat}
    (hshapes : List.Forall₂ (fun exprIR _ => AtomicArgIR scope exprIR)
      exprIRs args)
    (hevals : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value)
      exprIRs values)
    {name : String} (hname : name ∉ scope) (newValue : Nat) :
    List.Forall₂
      (fun exprIR argValue =>
        evalIRExpr (state.setVar name newValue) exprIR = some argValue)
      exprIRs values := by
  induction hshapes generalizing values with
  | nil =>
      cases hevals
      exact .nil
  | cons hshape hshapeTail ih =>
      cases hevals with
      | cons heval hevalTail =>
          exact .cons
            (by
              rw [evalIRExpr_atomic_setVar hshape hname state newValue]
              exact heval)
            (ih hevalTail)

private theorem eventForall₂_eval_atomic_memory_of_args
    {scope : List String} {state : IRState}
    {exprIRs : List YulExpr} {args : List Expr} {values : List Nat}
    (hshapes : List.Forall₂ (fun exprIR _ => AtomicArgIR scope exprIR)
      exprIRs args)
    (hevals : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value)
      exprIRs values)
    (mem : Nat → Nat) :
    List.Forall₂
      (fun exprIR value => evalIRExpr { state with memory := mem } exprIR = some value)
      exprIRs values := by
  induction hshapes generalizing values with
  | nil =>
      cases hevals
      exact .nil
  | cons hshape hshapeTail ih =>
      cases hevals with
      | cons heval hevalTail =>
          exact .cons
            (by
              rw [evalIRExpr_atomic_memory hshape state mem]
              exact heval)
            (ih hevalTail)

/-! ## Per-statement step lemmas -/

private theorem eventExecIRStmt_let_step
    {state : IRState} {valueIR : YulExpr} {value : Nat}
    (name : String)
    (heval : evalIRExpr state valueIR = some value)
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.let_ name valueIR) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem eventExecIRStmt_mstore_step
    {state : IRState} {offsetExpr valExpr : YulExpr} {offset val : Nat}
    (hoff : evalIRExpr state offsetExpr = some offset)
    (hval : evalIRExpr state valExpr = some val)
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state
        (YulStmt.expr (YulExpr.call "mstore" [offsetExpr, valExpr])) =
      .continue { state with
        memory := fun o => if o = offset then val else state.memory o } := by
  simp [execIRStmt, hoff, hval]

private theorem eventExecIRStmt_log1_step
    {state : IRState} {args : List YulExpr} {offset size topic0 : Nat}
    (heval : evalIRExprs state args = some [offset, size, topic0])
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.expr (YulExpr.call "log1" args)) =
      .continue (state.appendYulLog offset size [topic0]) := by
  simp [execIRStmt, isYulLogName, heval]

private theorem eventExecIRStmt_log2_step
    {state : IRState} {args : List YulExpr} {offset size topic0 topic1 : Nat}
    (heval : evalIRExprs state args = some [offset, size, topic0, topic1])
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.expr (YulExpr.call "log2" args)) =
      .continue (state.appendYulLog offset size [topic0, topic1]) := by
  simp [execIRStmt, isYulLogName, heval]

private theorem eventExecIRStmt_log3_step
    {state : IRState} {args : List YulExpr} {offset size topic0 topic1 topic2 : Nat}
    (heval : evalIRExprs state args = some [offset, size, topic0, topic1, topic2])
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.expr (YulExpr.call "log3" args)) =
      .continue (state.appendYulLog offset size [topic0, topic1, topic2]) := by
  simp [execIRStmt, isYulLogName, heval]

private theorem eventExecIRStmt_log4_step
    {state : IRState} {args : List YulExpr}
    {offset size topic0 topic1 topic2 topic3 : Nat}
    (heval : evalIRExprs state args =
      some [offset, size, topic0, topic1, topic2, topic3])
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.expr (YulExpr.call "log4" args)) =
      .continue (state.appendYulLog offset size
        [topic0, topic1, topic2, topic3]) := by
  simp [execIRStmt, isYulLogName, heval]

/-! ## Event signature scratch stores -/

private theorem eventIRState_set_memory_eq_self
    (state : IRState) {mem : Nat → Nat}
    (hmem : ∀ offset, mem offset = state.memory offset) :
    { state with memory := mem } = state := by
  cases state
  simp only
  congr
  funext offset
  exact hmem offset

private def eventSignatureStoreStmtsFromWords :
    List Nat → Nat → List YulStmt
  | [], _ => []
  | word :: rest, startIdx =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [
        YulExpr.ident "__evt_ptr",
        YulExpr.lit (startIdx * 32)
      ],
      YulExpr.hex word
    ]) :: eventSignatureStoreStmtsFromWords rest (startIdx + 1)

private def eventSignatureStoreStmtsFromChunks
    (chunks : List (List UInt8)) (startIdx : Nat) : List YulStmt :=
  (chunks.zipIdx startIdx).map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [
        YulExpr.ident "__evt_ptr",
        YulExpr.lit (idx * 32)
      ],
      YulExpr.hex (wordFromBytes chunk)
    ])

private theorem eventEvalIRExpr_evtPtr_add
    {state : IRState} {ptr idx : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr) :
    evalIRExpr state
        (YulExpr.call "add" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (idx * 32)
        ]) =
      some ((ptr + idx * 32) % Compiler.Constants.evmModulus) := by
  exact FunctionBody.evalIRExpr_add_of_eval
    (state := state)
    (lhs := YulExpr.ident "__evt_ptr")
    (rhs := YulExpr.lit (idx * 32))
    (a := ptr)
    (b := idx * 32)
    (by simpa [evalIRExpr] using hptr)
    (by simp [evalIRExpr])

private theorem eventSignatureStoreStmtsFromWords_cons
    (word : Nat) (words : List Nat) (startIdx : Nat) :
    eventSignatureStoreStmtsFromWords (word :: words) startIdx =
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (startIdx * 32)
        ],
        YulExpr.hex word
      ]) :: eventSignatureStoreStmtsFromWords words (startIdx + 1) := by
  rfl

private theorem eventSignatureStoreStmtsFromChunks_eq_words
    (chunks : List (List UInt8)) (startIdx : Nat) :
    eventSignatureStoreStmtsFromChunks chunks startIdx =
      eventSignatureStoreStmtsFromWords (chunks.map wordFromBytes) startIdx := by
  induction chunks generalizing startIdx with
  | nil =>
      simp [eventSignatureStoreStmtsFromChunks, eventSignatureStoreStmtsFromWords]
  | cons chunk rest ih =>
      simp [eventSignatureStoreStmtsFromChunks, eventSignatureStoreStmtsFromWords]
      exact ih (startIdx + 1)

private theorem eventSignatureScratchStore_memoryRel
    {state : IRState} {srcMemory : Nat → Verity.Core.Uint256}
    {ptr startIdx word : Nat}
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hword : word < Compiler.Constants.evmModulus) :
    ∀ offset,
      (if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
        then word else state.memory offset) =
      ((fun offset =>
        if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus then
          (word : Verity.Core.Uint256)
        else
          srcMemory offset) offset).val := by
  intro offset
  by_cases hkey :
      offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
  · simp [hkey, Nat.mod_eq_of_lt hword]
  · simp [hkey, hmem offset]

private theorem eventSignatureScratchStores_continue {state : IRState}
    {srcMemory : Nat → Verity.Core.Uint256} {ptr startIdx : Nat} {words : List Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hbounded : ∀ word ∈ words, word < Compiler.Constants.evmModulus) :
    StmtsContinueFromTo state (eventSignatureStoreStmtsFromWords words startIdx)
      { state with memory := fun offset =>
          (SourceSemantics.writeEventSignatureScratchFrom words ptr startIdx
            srcMemory offset).val } := by
  induction words generalizing state srcMemory startIdx with
  | nil =>
      simpa [eventSignatureStoreStmtsFromWords,
        SourceSemantics.writeEventSignatureScratchFrom] using
        (eventIRState_set_memory_eq_self state
          (by intro offset; exact (hmem offset).symm)).symm
  | cons word rest ih =>
      rw [eventSignatureStoreStmtsFromWords_cons]
      have hoff := eventEvalIRExpr_evtPtr_add (state := state) (ptr := ptr) (idx := startIdx) hptr
      have hval : evalIRExpr state (YulExpr.hex word) = some word := by simp [evalIRExpr]
      refine ⟨{ state with memory :=
        fun o => if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
          then word else state.memory o }, ?_, ?_⟩
      · intro extraFuel
        simpa using eventExecIRStmt_mstore_step hoff hval extraFuel
      · have hptr' :
            ({ state with memory :=
              fun o => if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
                then word else state.memory o }).getVar "__evt_ptr" = some ptr := by
          simpa [IRState.getVar] using hptr
        let nextSrcMemory : Nat → Verity.Core.Uint256 := fun offset =>
          if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus then
            (word : Verity.Core.Uint256)
          else srcMemory offset
        have hmem' := eventSignatureScratchStore_memoryRel
          (state := state) (srcMemory := srcMemory) (ptr := ptr)
          (startIdx := startIdx) (word := word) hmem (hbounded word (by simp))
        have hbounded' : ∀ w ∈ rest, w < Compiler.Constants.evmModulus := by
          intro w hw
          exact hbounded w (by simp [hw])
        simpa [SourceSemantics.writeEventSignatureScratchFrom, nextSrcMemory]
          using ih (state := { state with memory := (fun o =>
            if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
            then word else state.memory o) }) (srcMemory := nextSrcMemory)
            (startIdx := startIdx + 1) hptr' hmem' hbounded'

private theorem eventSignatureTopic_of_memorySliceWords_eq
    {eventDef : EventDef} {memory : Nat → Nat} {ptr : Nat}
    (hslice :
      memorySliceWords memory ptr (bytesFromString (eventSignature eventDef)).length =
        memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
          (bytesFromString (eventSignature eventDef)).length) :
    abstractKeccakMemorySlice memory ptr
        (bytesFromString (eventSignature eventDef)).length =
      SourceSemantics.eventSignatureTopic eventDef := by
  simp [abstractKeccakMemorySlice, SourceSemantics.eventSignatureTopic, hslice]

private theorem eventEvalIRExpr_topic0
    {state : IRState} {eventDef : EventDef} {ptr : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hslice :
      memorySliceWords state.memory ptr (bytesFromString (eventSignature eventDef)).length =
        memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
          (bytesFromString (eventSignature eventDef)).length) :
    evalIRExpr state
        (YulExpr.call "keccak256" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (bytesFromString (eventSignature eventDef)).length
        ]) =
      some (SourceSemantics.eventSignatureTopic eventDef) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hptr,
    eventSignatureTopic_of_memorySliceWords_eq hslice]

/-! ## Word normalization bridge

The compiled `normalizeEventWord` masking matches the source-side
`normalizeEventValue` on every proof-supported scalar parameter type. -/

private theorem eventEvalIRExpr_normalizeEventWord_uint8
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.uint8 exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.uint8 value) := by
  have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    SourceSemantics.uint8Modulus, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, h255]

private theorem eventEvalIRExpr_normalizeEventWord_uint16
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.uint16 exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.uint16 value) := by
  have h65535 : (65535 : Nat) % Compiler.Constants.evmModulus = 65535 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, h65535]

private theorem eventEvalIRExpr_normalizeEventWord_address
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.address exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.address value) := by
  have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
      Compiler.Constants.addressMask :=
    Nat.mod_eq_of_lt
      (by norm_num [Compiler.Constants.addressMask, Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, hmask]

private theorem eventEvalIRExpr_normalizeEventWord_bool
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.bool exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.bool value) := by
  have hone : (1 : Nat) % Compiler.Constants.evmModulus = 1 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  by_cases hzero : value % Compiler.Constants.evmModulus = 0 <;>
    simp [normalizeEventWord, CompilationModel.yulToBool,
      SourceSemantics.normalizeEventValue, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      heval, hzero, hone]

private theorem eventEvalIRExpr_normalizeEventWord :
    ∀ (ty : ParamType) {state : IRState} {exprIR : YulExpr} {value : Nat},
      eventParamScalarProofSupported ty = true →
      evalIRExpr state exprIR = some value →
      value < Compiler.Constants.evmModulus →
      evalIRExpr state (normalizeEventWord ty exprIR) =
        some (SourceSemantics.normalizeEventValue ty value)
  | .uint256, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .int256, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .bytes32, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .uint8, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_uint8 heval
  | .uint16, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_uint16 heval
  | .address, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_address heval
  | .bool, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_bool heval
  | .newtypeOf _ baseType, _, _, _, hsupport, heval, hlt => by
      have hbase : eventParamScalarProofSupported baseType = true := by
        simpa [eventParamScalarProofSupported, eventParamScalarCompileSupported]
          using hsupport
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue]
        using eventEvalIRExpr_normalizeEventWord baseType hbase heval hlt
  | .string, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .tuple _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .array _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .fixedArray _ _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .bytes, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .adt _ _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport

/-! ## Unindexed scalar scratch stores -/

private theorem eventNormalizeEventValue_lt_evmModulus :
    ∀ (ty : ParamType) (value : Nat),
      eventParamScalarProofSupported ty = true →
      value < Compiler.Constants.evmModulus →
      SourceSemantics.normalizeEventValue ty value < Compiler.Constants.evmModulus
  | .uint256, value, _, hlt => by
      simpa [SourceSemantics.normalizeEventValue,
        SourceSemantics.wordNormalize, Nat.mod_eq_of_lt hlt]
  | .int256, value, _, hlt => by
      simpa [SourceSemantics.normalizeEventValue,
        SourceSemantics.wordNormalize, Nat.mod_eq_of_lt hlt]
  | .bytes32, value, _, hlt => by
      simpa [SourceSemantics.normalizeEventValue,
        SourceSemantics.wordNormalize, Nat.mod_eq_of_lt hlt]
  | .uint8, value, _, _ => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .uint16, value, _, _ => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .address, value, _, _ => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .bool, value, _, _ => by
      by_cases hzero :
          value % Compiler.Constants.evmModulus = 0 <;>
        simp [SourceSemantics.normalizeEventValue, hzero,
          SourceSemantics.wordNormalize, Compiler.Constants.evmModulus]
  | .newtypeOf _ baseType, value, hsupport, hlt => by
      have hbase : eventParamScalarProofSupported baseType = true := by
        simpa [eventParamScalarProofSupported, eventParamScalarCompileSupported]
          using hsupport
      simpa [SourceSemantics.normalizeEventValue]
        using eventNormalizeEventValue_lt_evmModulus baseType value hbase hlt
  | .string, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .tuple _, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .array _, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .fixedArray _ _, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .bytes, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .adt _ _, _, hsupport, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport

private theorem eventNormalizeEventValue_lt_evmModulus_any :
    ∀ (ty : ParamType) (value : Nat),
      SourceSemantics.normalizeEventValue ty value < Compiler.Constants.evmModulus
  | .uint256, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .int256, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .bytes32, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .uint8, value => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .uint16, value => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .address, value => by
      exact Nat.lt_of_le_of_lt Nat.and_le_left
        (FunctionBody.wordNormalize_lt_evmModulus value)
  | .bool, value => by
      by_cases hzero :
          value % Compiler.Constants.evmModulus = 0 <;>
        simp [SourceSemantics.normalizeEventValue, hzero,
          SourceSemantics.wordNormalize, Compiler.Constants.evmModulus]
  | .newtypeOf _ baseType, value => by
      simpa [SourceSemantics.normalizeEventValue]
        using eventNormalizeEventValue_lt_evmModulus_any baseType value
  | .string, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .tuple _, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .array _, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .fixedArray _ _, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .bytes, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value
  | .adt _ _, value => by
      exact FunctionBody.wordNormalize_lt_evmModulus value

private theorem eventUnindexedScratchStore_memoryRel
    {state : IRState} {srcMemory : Nat → Verity.Core.Uint256}
    {ptr wordIdx value : Nat} {ty : ParamType}
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hbounded :
      SourceSemantics.normalizeEventValue ty value < Compiler.Constants.evmModulus) :
    ∀ offset,
      (if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
        SourceSemantics.normalizeEventValue ty value
      else
        state.memory offset) =
      ((fun offset =>
        if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
          (SourceSemantics.normalizeEventValue ty value : Verity.Core.Uint256)
        else
          srcMemory offset) offset).val := by
  intro offset
  by_cases hkey :
      offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus
  · simp [hkey, Nat.mod_eq_of_lt hbounded]
  · simp [hkey, hmem offset]

private theorem eventUnindexedStore_one_continue
    {state : IRState} {srcMemory : Nat → Verity.Core.Uint256}
    {ptr wordIdx value : Nat} {ty : ParamType} {argExpr : YulExpr}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (heval : evalIRExpr state argExpr = some value)
    (hsupport : eventParamScalarProofSupported ty = true)
    (hvalueLt : value < Compiler.Constants.evmModulus)
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val) :
    StmtsContinueFromTo state
      [YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (wordIdx * 32)],
        normalizeEventWord ty argExpr
      ])]
      { state with memory := fun offset =>
          (if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
            (SourceSemantics.normalizeEventValue ty value : Verity.Core.Uint256)
          else
            srcMemory offset).val } := by
  have hoff := eventEvalIRExpr_evtPtr_add
    (state := state) (ptr := ptr) (idx := wordIdx) hptr
  have hval := eventEvalIRExpr_normalizeEventWord ty hsupport heval hvalueLt
  refine ⟨{ state with memory := fun offset =>
      if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
        SourceSemantics.normalizeEventValue ty value
      else state.memory offset }, ?_, ?_⟩
  · intro extraFuel
    simpa using eventExecIRStmt_mstore_step hoff hval extraFuel
  · have hnormLt :
        SourceSemantics.normalizeEventValue ty value < Compiler.Constants.evmModulus := by
      exact eventNormalizeEventValue_lt_evmModulus ty value hsupport hvalueLt
    exact (eventIRState_set_memory_eq_self _ (by
      intro offset
      exact (eventUnindexedScratchStore_memoryRel
        (state := state) (srcMemory := srcMemory) (ptr := ptr)
        (wordIdx := wordIdx) (value := value) (ty := ty)
        hmem hnormLt offset).symm)).symm

private def EventUnindexedEntryOk (scope : List String) (state : IRState) :
    (EventParam × Expr × YulExpr) → Nat → Prop
  | (param, _, argExpr), value =>
      evalIRExpr state argExpr = some value ∧
      eventParamScalarProofSupported param.ty = true ∧
      value < Compiler.Constants.evmModulus ∧
      AtomicArgIR scope argExpr ∧
      eventHeadWordSize param.ty = 32 ∧
      (param.kind == EventParamKind.unindexed) = true

private theorem eventUnindexedEntryOk_memory
    {scope : List String} {state : IRState} {mem : Nat → Nat}
    {entry : EventParam × Expr × YulExpr} {value : Nat}
    (hok : EventUnindexedEntryOk scope state entry value) :
    EventUnindexedEntryOk scope { state with memory := mem } entry value := by
  rcases entry with ⟨param, srcExpr, argExpr⟩
  rcases hok with ⟨heval, hsupport, hlt, hshape, hsize, hkind⟩
  exact ⟨by simpa using (evalIRExpr_atomic_memory hshape state mem).trans heval,
    hsupport, hlt, hshape, hsize, hkind⟩

private theorem eventUnindexedEntriesOk_memory
    {scope : List String} {state : IRState} {mem : Nat → Nat}
    {entries : List (EventParam × Expr × YulExpr)} {values : List Nat}
    (hrel : List.Forall₂ (EventUnindexedEntryOk scope state) entries values) :
    List.Forall₂ (EventUnindexedEntryOk scope { state with memory := mem })
      entries values := by
  induction hrel with
  | nil => exact .nil
  | cons hok htail ih =>
      exact .cons (eventUnindexedEntryOk_memory hok) ih

private def eventUnindexedNextMemory
    (srcMemory : Nat → Verity.Core.Uint256)
    (ptr wordIdx : Nat) (ty : ParamType) (value : Nat) :
    Nat → Verity.Core.Uint256 :=
  fun offset =>
    if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
      (SourceSemantics.normalizeEventValue ty value : Verity.Core.Uint256)
    else srcMemory offset

private theorem eventUnindexedStores_cons_continue
    {scope : List String} {state : IRState}
    {srcMemory srcMemory' : Nat → Verity.Core.Uint256}
    {ptr wordIdx value : Nat} {param : EventParam} {srcExpr : Expr}
    {argExpr : YulExpr} {rest : List (EventParam × Expr × YulExpr)} {values : List Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hok : EventUnindexedEntryOk scope state (param, srcExpr, argExpr) value)
    (hwriteTail : SourceSemantics.writeUnindexedEventScratchFrom
        (rest.map (fun entry => entry.1)) values ptr (wordIdx + 1)
        (eventUnindexedNextMemory srcMemory ptr wordIdx param.ty value) = some srcMemory')
    (htailContinue : StmtsContinueFromTo { state with memory := fun offset =>
          ((eventUnindexedNextMemory srcMemory ptr wordIdx param.ty value)
            offset).val }
        (scalarEventUnindexedStoresFrom rest ((wordIdx + 1) * 32))
        { state with memory := fun offset => (srcMemory' offset).val }) :
    SourceSemantics.writeUnindexedEventScratchFrom
        (((param, srcExpr, argExpr) :: rest).map (fun entry => entry.1))
        (value :: values) ptr wordIdx srcMemory = some srcMemory' ∧
      StmtsContinueFromTo state
        (scalarEventUnindexedStoresFrom ((param, srcExpr, argExpr) :: rest)
          (wordIdx * 32))
        { state with memory := fun offset => (srcMemory' offset).val } := by
  rcases hok with ⟨heval, hsupport, hlt, hshape, hsize, hkind⟩
  constructor
  · simp [SourceSemantics.writeUnindexedEventScratchFrom, hkind]
    simpa [eventUnindexedNextMemory] using hwriteTail
  · have hstmt :
        scalarEventUnindexedStoresFrom ((param, srcExpr, argExpr) :: rest)
            (wordIdx * 32) =
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [
              YulExpr.ident "__evt_ptr", YulExpr.lit (wordIdx * 32)],
            normalizeEventWord param.ty argExpr]) ::
          scalarEventUnindexedStoresFrom rest ((wordIdx + 1) * 32) := by
      have hoff : wordIdx * 32 + eventHeadWordSize param.ty =
          (wordIdx + 1) * 32 := by
        rw [hsize]
        omega
      simp [scalarEventUnindexedStoresFrom, hoff]
    rw [hstmt]
    exact StmtsContinueFromTo_append
      (eventUnindexedStore_one_continue
        (state := state) (srcMemory := srcMemory) (ptr := ptr)
        (wordIdx := wordIdx) (value := value)
        (ty := param.ty) (argExpr := argExpr)
        hptr heval hsupport hlt hmem)
      htailContinue

private theorem eventUnindexedStores_continue
    {scope : List String} {state : IRState}
    {srcMemory : Nat → Verity.Core.Uint256} {ptr wordIdx : Nat}
    {entries : List (EventParam × Expr × YulExpr)} {values : List Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hrel : List.Forall₂ (EventUnindexedEntryOk scope state) entries values) :
    ∃ srcMemory',
      SourceSemantics.writeUnindexedEventScratchFrom
        (entries.map (fun entry => entry.1)) values ptr wordIdx srcMemory =
          some srcMemory' ∧
      StmtsContinueFromTo state
        (scalarEventUnindexedStoresFrom entries (wordIdx * 32))
        { state with memory := fun offset => (srcMemory' offset).val } := by
  induction entries generalizing values state srcMemory wordIdx with
  | nil =>
      cases values with
      | nil =>
          refine ⟨srcMemory, ?_, ?_⟩
          · simp [SourceSemantics.writeUnindexedEventScratchFrom]
          · simpa [scalarEventUnindexedStoresFrom] using
              (eventIRState_set_memory_eq_self state
                (by intro offset; exact (hmem offset).symm)).symm
      | cons value values => cases hrel
  | cons entry rest ih =>
      cases values with
      | nil => cases hrel
      | cons value values =>
          cases hrel with
          | cons hok htail =>
          rcases entry with ⟨param, srcExpr, argExpr⟩
          let nextSrcMemory :=
            eventUnindexedNextMemory srcMemory ptr wordIdx param.ty value
          rcases ih (state := { state with memory := fun offset =>
              (nextSrcMemory offset).val })
            (srcMemory := nextSrcMemory)
            (wordIdx := wordIdx + 1) (values := values)
            (by simpa [IRState.getVar] using hptr)
            (by intro offset; rfl)
            (eventUnindexedEntriesOk_memory htail) with
            ⟨srcMemory', hwriteTail, htailContinue⟩
          · have hcons := eventUnindexedStores_cons_continue
              (state := state) (srcMemory := srcMemory)
              (srcMemory' := srcMemory') (ptr := ptr) (wordIdx := wordIdx) (value := value)
              (param := param) (srcExpr := srcExpr) (argExpr := argExpr) (rest := rest) (values := values)
              hptr hmem hok (by simpa [nextSrcMemory] using hwriteTail)
              (by simpa [nextSrcMemory] using htailContinue)
            exact ⟨srcMemory', hcons.1, hcons.2⟩

private def eventValuesForKind :
    EventParamKind → List EventParam → List Nat → List Nat
  | _, [], _ => []
  | _, _ :: _, [] => []
  | kind, param :: params, value :: values =>
      if param.kind == kind then
        value :: eventValuesForKind kind params values
      else
        eventValuesForKind kind params values

private theorem eventValuesForKind_unindexed_cons_true
    {param : EventParam} {params : List EventParam}
    {value : Nat} {values : List Nat}
    (hkind : (param.kind == EventParamKind.unindexed) = true) :
    eventValuesForKind EventParamKind.unindexed
        (param :: params) (value :: values) =
      value :: eventValuesForKind EventParamKind.unindexed params values := by
  simp [eventValuesForKind, hkind]

private theorem eventValuesForKind_unindexed_cons_false
    {param : EventParam} {params : List EventParam}
    {value : Nat} {values : List Nat}
    (hkind : (param.kind == EventParamKind.unindexed) = false) :
    eventValuesForKind EventParamKind.unindexed
        (param :: params) (value :: values) =
      eventValuesForKind EventParamKind.unindexed params values := by
  simp [eventValuesForKind, hkind]

private theorem eventWriteUnindexed_filter_unindexed
    {params : List EventParam} {values : List Nat}
    {ptr wordIdx : Nat} {memory : Nat → Verity.Core.Uint256}
    (hlen : values.length = params.length) :
    SourceSemantics.writeUnindexedEventScratchFrom
        (params.filter (fun param => param.kind == EventParamKind.unindexed))
        (eventValuesForKind EventParamKind.unindexed params values)
        ptr wordIdx memory =
      SourceSemantics.writeUnindexedEventScratchFrom
        params values ptr wordIdx memory := by
  induction params generalizing values wordIdx memory with
  | nil =>
      cases values <;> simp [eventValuesForKind] at hlen ⊢
  | cons param params ih =>
      cases values with
      | nil => simp at hlen
      | cons value values =>
          have htail : values.length = params.length := by
            simpa using Nat.succ.inj hlen
          by_cases hkind : (param.kind == EventParamKind.unindexed) = true
          · simp [SourceSemantics.writeUnindexedEventScratchFrom, hkind,
              eventValuesForKind_unindexed_cons_true hkind, ih htail]
          · have hkindFalse :
                (param.kind == EventParamKind.unindexed) = false := by
              cases h : param.kind == EventParamKind.unindexed <;>
                simp [h] at hkind ⊢
            simp [SourceSemantics.writeUnindexedEventScratchFrom, hkindFalse,
              eventValuesForKind_unindexed_cons_false hkindFalse, ih htail]

private def eventEncodedValuesForKind :
    EventParamKind → List EventParam → List Nat → List Nat
  | _, [], _ => []
  | _, _ :: _, [] => []
  | kind, param :: params, value :: values =>
      if param.kind == kind then
        SourceSemantics.normalizeEventValue param.ty value ::
          eventEncodedValuesForKind kind params values
      else
        eventEncodedValuesForKind kind params values

private theorem eventKind_unindexed_true_of_not_indexed
    {kind : EventParamKind}
    (hindexed : ¬(kind == EventParamKind.indexed) = true) :
    (kind == EventParamKind.unindexed) = true := by
  cases kind
  · exact False.elim (hindexed rfl)
  · rfl

private theorem eventKind_indexed_false_of_unindexed_true
    {kind : EventParamKind}
    (hunindexed : (kind == EventParamKind.unindexed) = true) :
    (kind == EventParamKind.indexed) = false := by
  cases kind
  · cases hunindexed
  · rfl

private theorem eventKind_unindexed_false_of_indexed_true
    {kind : EventParamKind}
    (hindexed : (kind == EventParamKind.indexed) = true) :
    (kind == EventParamKind.unindexed) = false := by
  cases kind
  · rfl
  · cases hindexed

private theorem eventSplitEventArgsByParams_unindexed_encoded
    {params : List EventParam} {values : List Nat}
    {args indexedArgs : List Verity.Core.Uint256}
    (hsplit : SourceSemantics.splitEventArgsByParams params values =
      some (args, indexedArgs)) :
    args.map (fun value => value.val) =
        eventEncodedValuesForKind EventParamKind.unindexed params values := by
  induction params generalizing values args indexedArgs with
  | nil =>
      cases values with
      | nil =>
          simp [SourceSemantics.splitEventArgsByParams,
            eventEncodedValuesForKind] at hsplit
          rcases hsplit with ⟨hargs, _⟩
          subst args
          rfl
      | cons value values =>
          simp [SourceSemantics.splitEventArgsByParams] at hsplit
  | cons param params ih =>
      cases values with
      | nil =>
          simp [SourceSemantics.splitEventArgsByParams] at hsplit
      | cons value values =>
          simp only [SourceSemantics.splitEventArgsByParams] at hsplit
          cases htail :
              SourceSemantics.splitEventArgsByParams params values with
          | none => simp [htail] at hsplit
          | some pair =>
              rcases pair with ⟨tailArgs, tailIndexed⟩
              have htailEnc := ih htail
              by_cases hindexed : (param.kind == EventParamKind.indexed) = true
              · simp [htail, hindexed] at hsplit
                rcases hsplit with ⟨hargs, _⟩
                subst args
                have hunindexedFalse :
                    (param.kind == EventParamKind.unindexed) = false := by
                  exact eventKind_unindexed_false_of_indexed_true hindexed
                simp [eventEncodedValuesForKind, hindexed, hunindexedFalse, htailEnc]
              · have hunindexed := eventKind_unindexed_true_of_not_indexed hindexed
                have hindexedFalse :
                    (param.kind == EventParamKind.indexed) = false := by
                  exact eventKind_indexed_false_of_unindexed_true hunindexed
                simp [htail, hindexedFalse] at hsplit
                rcases hsplit with ⟨hargs, _⟩
                subst args
                have hnorm := eventNormalizeEventValue_lt_evmModulus_any
                  param.ty value
                simp [eventEncodedValuesForKind, hunindexed, htailEnc,
                  Nat.mod_eq_of_lt hnorm]

private theorem eventSplitEventArgsByParams_indexed_encoded
    {params : List EventParam} {values : List Nat}
    {args indexedArgs : List Verity.Core.Uint256}
    (hsplit :
      SourceSemantics.splitEventArgsByParams params values =
        some (args, indexedArgs)) :
    indexedArgs.map (fun value => value.val) =
        eventEncodedValuesForKind EventParamKind.indexed params values := by
  induction params generalizing values args indexedArgs with
  | nil =>
      cases values with
      | nil =>
          simp [SourceSemantics.splitEventArgsByParams,
            eventEncodedValuesForKind] at hsplit
          rcases hsplit with ⟨_, hindexedArgs⟩
          subst indexedArgs
          rfl
      | cons value values =>
          simp [SourceSemantics.splitEventArgsByParams] at hsplit
  | cons param params ih =>
      cases values with
      | nil => simp [SourceSemantics.splitEventArgsByParams] at hsplit
      | cons value values =>
          simp only [SourceSemantics.splitEventArgsByParams] at hsplit
          cases htail : SourceSemantics.splitEventArgsByParams params values with
          | none => simp [htail] at hsplit
          | some pair =>
              rcases pair with ⟨tailArgs, tailIndexed⟩
              have htailEnc := ih htail
              by_cases hindexed : (param.kind == EventParamKind.indexed) = true
              · simp [htail, hindexed] at hsplit
                rcases hsplit with ⟨_, hindexedArgs⟩
                subst indexedArgs
                have hnorm := eventNormalizeEventValue_lt_evmModulus_any
                  param.ty value
                simp [eventEncodedValuesForKind, hindexed, htailEnc,
                  Nat.mod_eq_of_lt hnorm]
              · have hunindexed := eventKind_unindexed_true_of_not_indexed hindexed
                have hindexedFalse :=
                  eventKind_indexed_false_of_unindexed_true hunindexed
                simp [htail, hindexedFalse] at hsplit
                rcases hsplit with ⟨_, hindexedArgs⟩
                subst indexedArgs
                simp [eventEncodedValuesForKind, hindexedFalse, htailEnc]

private theorem eventSplitEventArgsByParams_encoded
    {params : List EventParam} {values : List Nat}
    {args indexedArgs : List Verity.Core.Uint256}
    (hsplit :
      SourceSemantics.splitEventArgsByParams params values =
        some (args, indexedArgs)) :
    args.map (fun value => value.val) =
        eventEncodedValuesForKind EventParamKind.unindexed params values ∧
      indexedArgs.map (fun value => value.val) =
        eventEncodedValuesForKind EventParamKind.indexed params values := by
  exact ⟨eventSplitEventArgsByParams_unindexed_encoded hsplit,
    eventSplitEventArgsByParams_indexed_encoded hsplit⟩

private theorem eventKeccakFold_lt_evmModulus (words : List Nat) (acc : Nat) :
    words.foldl
        (fun acc word =>
          (acc * 16777619 + word) % Compiler.Constants.evmModulus)
        (acc % Compiler.Constants.evmModulus) <
      Compiler.Constants.evmModulus := by
  induction words generalizing acc with
  | nil =>
      exact Nat.mod_lt acc (by norm_num [Compiler.Constants.evmModulus])
  | cons word rest ih =>
      change rest.foldl
          (fun acc word =>
            (acc * 16777619 + word) % Compiler.Constants.evmModulus)
          (((acc % Compiler.Constants.evmModulus) * 16777619 + word) %
            Compiler.Constants.evmModulus) <
        Compiler.Constants.evmModulus
      exact ih ((acc % Compiler.Constants.evmModulus) * 16777619 + word)

private theorem eventSignatureTopic_lt_evmModulus (eventDef : EventDef) :
    SourceSemantics.eventSignatureTopic eventDef <
      Compiler.Constants.evmModulus := by
  simpa [SourceSemantics.eventSignatureTopic, abstractKeccakMemorySlice] using
    eventKeccakFold_lt_evmModulus
      (memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
        (bytesFromString (eventSignature eventDef)).length)
      (bytesFromString (eventSignature eventDef)).length

private theorem eventFromResolvedArgs?_encoded
    {events : List EventDef} {eventName : String} {values : List Nat}
    {eventDef : EventDef} {event : Verity.Event}
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hevent :
      SourceSemantics.eventFromResolvedArgs? events eventName values = some event) :
    SourceSemantics.encodeEvent event =
      SourceSemantics.eventSignatureTopic eventDef ::
        eventEncodedValuesForKind EventParamKind.indexed eventDef.params values ++
        eventEncodedValuesForKind EventParamKind.unindexed eventDef.params values := by
  simp only [SourceSemantics.eventFromResolvedArgs?, hfind] at hevent
  cases hsplit :
      SourceSemantics.splitEventArgsByParams eventDef.params values with
  | none => simp [hsplit] at hevent
  | some pair =>
      rcases pair with ⟨args, indexedArgs⟩
      simp [hsplit] at hevent
      cases hevent
      have henc := eventSplitEventArgsByParams_encoded hsplit
      have htopic := eventSignatureTopic_lt_evmModulus eventDef
      simp [SourceSemantics.encodeEvent, henc, List.map_append,
        Nat.mod_eq_of_lt htopic]

private def EventIndexedEntryOk (scope : List String) (state : IRState) :
    (EventParam × Expr × YulExpr) → Nat → Prop
  | (param, _, argExpr), value =>
      evalIRExpr state argExpr = some value ∧
      eventParamScalarProofSupported param.ty = true ∧
      value < Compiler.Constants.evmModulus ∧
      AtomicArgIR scope argExpr ∧
      (param.kind == EventParamKind.indexed) = true

private theorem eventIndexedTopicParts_eval
    {scope : List String} {state : IRState}
    {entries : List (EventParam × Expr × YulExpr)} {values : List Nat}
    (hrel : List.Forall₂ (EventIndexedEntryOk scope state) entries values) :
    evalIRExprs state ((scalarEventIndexedTopicParts entries).map (fun part => part.2)) =
      some (entries.zip values |>.map (fun (entry, value) =>
        SourceSemantics.normalizeEventValue entry.1.ty value)) := by
  induction hrel with
  | nil =>
      simp [scalarEventIndexedTopicParts, evalIRExprs]
  | cons hok htail ih =>
      rcases hok with ⟨heval, hsupport, hlt, _hshape, _hkind⟩
      have hnorm := eventEvalIRExpr_normalizeEventWord _ hsupport heval hlt
      have htailEval := by
        simpa [scalarEventIndexedTopicParts] using ih
      simp [evalIRExprs, scalarEventIndexedTopicParts, hnorm, htailEval]

private theorem eventIndexedTopicParts_eval_values
    {scope : List String} {state : IRState}
    {entries : List (EventParam × Expr × YulExpr)} {values : List Nat}
    (hrel : List.Forall₂ (EventIndexedEntryOk scope state) entries values) :
    evalIRExprs state ((scalarEventIndexedTopicParts entries).map (fun part => part.2)) =
      some (eventEncodedValuesForKind EventParamKind.indexed
        (entries.map (fun entry => entry.1)) values) := by
  induction hrel with
  | nil =>
      simp [scalarEventIndexedTopicParts, eventEncodedValuesForKind, evalIRExprs]
  | cons hok htail ih =>
      rcases hok with ⟨heval, hsupport, hlt, _hshape, hkind⟩
      have hnorm := eventEvalIRExpr_normalizeEventWord _ hsupport heval hlt
      have htailEval := by
        simpa [scalarEventIndexedTopicParts] using ih
      simp [evalIRExprs, scalarEventIndexedTopicParts, eventEncodedValuesForKind,
        hkind, hnorm, htailEval]

/-! ## Log data readback -/

private theorem eventScratchKey_injective_of_lt
    {ptr i j : Nat}
    (hi : i < eventScratchSizeLimit)
    (hj : j < eventScratchSizeLimit)
    (hkey :
      (ptr + i * 32) % Compiler.Constants.evmModulus =
        (ptr + j * 32) % Compiler.Constants.evmModulus) :
    i = j := by
  have hmodeqPtr :
      ptr + i * 32 ≡ ptr + j * 32 [MOD Compiler.Constants.evmModulus] := hkey
  have hmodeqMul :
      i * 32 ≡ j * 32 [MOD Compiler.Constants.evmModulus] :=
    Nat.ModEq.add_left_cancel' ptr hmodeqPtr
  have hmodeq :
      i ≡ j [MOD Compiler.Constants.evmModulus / Nat.gcd Compiler.Constants.evmModulus 32] :=
    Nat.ModEq.cancel_right_div_gcd
      (by norm_num [Compiler.Constants.evmModulus]) hmodeqMul
  have hdiv :
      Compiler.Constants.evmModulus / Nat.gcd Compiler.Constants.evmModulus 32 =
        2 ^ 251 := by
    native_decide
  have hi' : i < Compiler.Constants.evmModulus / Nat.gcd Compiler.Constants.evmModulus 32 := by
    rw [hdiv]
    exact lt_of_lt_of_le hi (by norm_num [eventScratchSizeLimit])
  have hj' : j < Compiler.Constants.evmModulus / Nat.gcd Compiler.Constants.evmModulus 32 := by
    rw [hdiv]
    exact lt_of_lt_of_le hj (by norm_num [eventScratchSizeLimit])
  exact Nat.ModEq.eq_of_lt_of_lt hmodeq hi' hj'

private theorem eventWriteSignatureScratch_preserve_before :
    ∀ {words : List Nat} {ptr idx baseIdx : Nat}
      {memory : Nat → Verity.Core.Uint256},
      idx + words.length ≤ eventScratchSizeLimit →
      baseIdx < idx →
      baseIdx < eventScratchSizeLimit →
      SourceSemantics.writeEventSignatureScratchFrom words ptr idx memory
          ((ptr + baseIdx * 32) % Compiler.Constants.evmModulus) =
        memory ((ptr + baseIdx * 32) % Compiler.Constants.evmModulus)
  | [], _, _, _, _, _, _, _ => by
      simp [SourceSemantics.writeEventSignatureScratchFrom]
  | word :: words, ptr, idx, baseIdx, memory, hlimit, hbefore, hbaseLimit => by
      have htail := eventWriteSignatureScratch_preserve_before
        (words := words) (ptr := ptr) (idx := idx + 1) (baseIdx := baseIdx)
        (memory := fun offset =>
          if offset = (ptr + idx * 32) % Compiler.Constants.evmModulus then
            (word : Verity.Core.Uint256)
          else memory offset)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlimit)
        (by omega) hbaseLimit
      have hne :
          (ptr + baseIdx * 32) % Compiler.Constants.evmModulus ≠
            (ptr + idx * 32) % Compiler.Constants.evmModulus := by
        intro hkey
        have hidx : idx < eventScratchSizeLimit := by
          exact lt_of_lt_of_le (by simp : idx < idx + (word :: words).length) hlimit
        have heq := eventScratchKey_injective_of_lt hbaseLimit hidx hkey
        omega
      simpa [SourceSemantics.writeEventSignatureScratchFrom, hne] using htail

private theorem eventWriteSignatureScratch_read_head
    {word : Nat} {words : List Nat} {ptr idx : Nat}
    {memory : Nat → Verity.Core.Uint256}
    (hlimit : idx + (word :: words).length ≤ eventScratchSizeLimit) :
    SourceSemantics.writeEventSignatureScratchFrom (word :: words) ptr idx memory
        ((ptr + idx * 32) % Compiler.Constants.evmModulus) =
      (word : Verity.Core.Uint256) := by
  have hpres := eventWriteSignatureScratch_preserve_before
    (words := words) (ptr := ptr) (idx := idx + 1) (baseIdx := idx)
    (memory := fun offset =>
      if offset = (ptr + idx * 32) % Compiler.Constants.evmModulus then
        (word : Verity.Core.Uint256)
      else memory offset)
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlimit)
    (by omega)
    (lt_of_lt_of_le (by simp : idx < idx + (word :: words).length) hlimit)
  simpa [SourceSemantics.writeEventSignatureScratchFrom, hpres]

private theorem eventWriteSignatureScratch_read_getElem :
    ∀ {words : List Nat} {ptr idx : Nat} {memory : Nat → Verity.Core.Uint256},
      idx + words.length ≤ eventScratchSizeLimit →
      ∀ i (hi : i < words.length),
        SourceSemantics.writeEventSignatureScratchFrom words ptr idx memory
            ((ptr + (idx + i) * 32) % Compiler.Constants.evmModulus) =
          (words[i] : Verity.Core.Uint256)
  | word :: words, ptr, idx, memory, hlimit, i, hi => by
      cases i with
      | zero =>
          simpa using eventWriteSignatureScratch_read_head
            (word := word) (words := words) (ptr := ptr) (idx := idx)
            (memory := memory) hlimit
      | succ i =>
          have htail := eventWriteSignatureScratch_read_getElem
            (words := words) (ptr := ptr) (idx := idx + 1)
            (memory := fun offset =>
              if offset = (ptr + idx * 32) % Compiler.Constants.evmModulus then
                (word : Verity.Core.Uint256)
              else memory offset)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlimit)
            i (by simpa using hi)
          simpa [SourceSemantics.writeEventSignatureScratchFrom, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using htail
  | [], _, _, _, _, i, hi => by
      simp at hi

private theorem eventChunkBytes32_length (bs : List UInt8) :
    (chunkBytes32 bs).length = byteWordCount bs.length := by
  rw [chunkBytes32]
  cases bs with
  | nil =>
      simp [byteWordCount]
  | cons b rest =>
      simp
      have hrec := eventChunkBytes32_length (rest.drop 31)
      rw [hrec]
      simp [byteWordCount, List.length_drop]
      omega
termination_by bs.length

private theorem eventByteWordCount_le_self (n : Nat) :
    byteWordCount n ≤ n := by
  cases n with
  | zero =>
      simp [byteWordCount]
  | succ n =>
      simp [byteWordCount]
      omega

private theorem eventSignatureWords_length
    (sigBytes : List UInt8) :
    ((chunkBytes32 sigBytes).map wordFromBytes).length =
      byteWordCount sigBytes.length := by
  simp [eventChunkBytes32_length]

private theorem eventSignatureWords_length_le_scratch
    {events : List EventDef} {eventName : String} {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length ≤
      eventScratchSizeLimit := by
  have hbounded := eventDefScratchBounded_of_eventEmissionProofSupported
    hsupport hfind
  unfold eventDefScratchBounded at hbounded
  simp [Bool.and_eq_true] at hbounded
  rw [eventSignatureWords_length]
  exact le_trans (eventByteWordCount_le_self _) hbounded.1

private theorem eventChunkBytes32_mem_length_le :
    ∀ {bs chunk : List UInt8}, chunk ∈ chunkBytes32 bs → chunk.length ≤ 32
  | [], chunk, hmem => by
      unfold chunkBytes32 at hmem
      simp at hmem
  | b :: rest, chunk, hmem => by
      unfold chunkBytes32 at hmem
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst chunk
        exact List.length_take_le 32 (b :: rest)
      · exact eventChunkBytes32_mem_length_le (bs := (b :: rest).drop 32) htail
termination_by bs => bs.length
decreasing_by
  simp_wf
  omega

private theorem eventFoldBytes_bound (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc <
      (acc + 1) * 256 ^ bs.length := by
  induction bs generalizing acc with
  | nil =>
      simp
  | cons b rest ih =>
      have hb : b.toNat < 256 := by exact UInt8.toNat_lt b
      have hstep : acc * 256 + b.toNat + 1 ≤ (acc + 1) * 256 := by omega
      have hmul := Nat.mul_le_mul_right (256 ^ rest.length) hstep
      have hrest := ih (acc * 256 + b.toNat)
      simp [List.foldl_cons, List.length_cons]
      exact lt_of_lt_of_le hrest (by simpa [Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm, pow_succ] using hmul)

private theorem eventWordFromBytes_lt_evmModulus_of_length_le
    {bs : List UInt8} (hlen : bs.length ≤ 32) :
    wordFromBytes bs < Compiler.Constants.evmModulus := by
  have hbound := eventFoldBytes_bound
    (bs ++ List.replicate (32 - bs.length) (0 : UInt8)) 0
  have hlenPadded :
      (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).length = 32 := by
    simp [hlen]
  rw [hlenPadded] at hbound
  simpa [wordFromBytes, Compiler.Constants.evmModulus] using hbound

private theorem eventSignatureWords_bounded (eventDef : EventDef) :
    ∀ word ∈
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes),
      word < Compiler.Constants.evmModulus := by
  intro word hmem
  rcases List.mem_map.mp hmem with ⟨chunk, hchunk, rfl⟩
  exact eventWordFromBytes_lt_evmModulus_of_length_le
    (eventChunkBytes32_mem_length_le hchunk)

private theorem eventSignatureMemory_read_getElem
    {eventDef : EventDef} {i : Nat}
    (hi : i <
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length)
    (hlimit :
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length ≤
        eventScratchSizeLimit) :
    SourceSemantics.eventSignatureMemory eventDef
        ((0 + i * 32) % Compiler.Constants.evmModulus) =
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)[i] := by
  have hiLimit : i < eventScratchSizeLimit := lt_of_lt_of_le hi hlimit
  have hltMod : i * 32 < Compiler.Constants.evmModulus := by
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hiLimit (by norm_num))
      (by norm_num [eventScratchSizeLimit, Compiler.Constants.evmModulus])
  have hmod : (0 + i * 32) % Compiler.Constants.evmModulus = i * 32 := by
    simpa using Nat.mod_eq_of_lt hltMod
  have hmod' : i * 32 % Compiler.Constants.evmModulus = i * 32 := by
    simpa using Nat.mod_eq_of_lt hltMod
  have halign : (i * 32) % 32 = 0 := by simp [Nat.mul_comm]
  have hdiv : (i * 32) / 32 = i := by simp [Nat.mul_comm]
  have hichunk : i < (chunkBytes32 (bytesFromString (eventSignature eventDef))).length := by
    simpa using hi
  have hget :
      ((chunkBytes32 (bytesFromString (eventSignature eventDef)))[i]?) =
        some ((chunkBytes32 (bytesFromString (eventSignature eventDef)))[i]) := by
    simpa using List.getElem?_eq_getElem hichunk
  simp [SourceSemantics.eventSignatureMemory, hmod, hmod', halign, hdiv, hget]

private theorem eventSignatureScratch_read_getElem_val
    {eventDef : EventDef} {ptr i : Nat}
    {srcMemory : Nat → Verity.Core.Uint256}
    (hi : i <
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length)
    (hlimit :
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length ≤
        eventScratchSizeLimit) :
    (SourceSemantics.writeEventSignatureScratchFrom
        ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)
        ptr 0 srcMemory ((ptr + i * 32) % Compiler.Constants.evmModulus)).val =
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)[i] := by
  have hwrite := eventWriteSignatureScratch_read_getElem
    (words := (chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)
    (ptr := ptr) (idx := 0) (memory := srcMemory) (by simpa using hlimit) i hi
  have hwordLt :
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)[i] <
        Compiler.Constants.evmModulus :=
    eventSignatureWords_bounded eventDef _
      (List.get_mem _ ⟨i, hi⟩)
  have hiChunk :
      i < (chunkBytes32 (bytesFromString (eventSignature eventDef))).length := by
    simpa using hi
  have hwordLt' :
      wordFromBytes ((chunkBytes32 (bytesFromString (eventSignature eventDef)))[i]'hiChunk) <
        Compiler.Constants.evmModulus := by
    simpa using hwordLt
  simpa [Nat.zero_add, Nat.mod_eq_of_lt hwordLt'] using
    (congrArg Verity.Core.Uint256.val hwrite)

private theorem eventSignatureScratch_memorySliceWords_eq
    {eventDef : EventDef} {ptr : Nat} {srcMemory : Nat → Verity.Core.Uint256}
    (hlimit :
      ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length ≤
        eventScratchSizeLimit) :
    memorySliceWords
        (fun offset =>
          (SourceSemantics.writeEventSignatureScratchFrom
            ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)
            ptr 0 srcMemory offset).val)
        ptr (bytesFromString (eventSignature eventDef)).length =
      memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
        (bytesFromString (eventSignature eventDef)).length := by
  apply List.ext_getElem
  · simp [memorySliceWords]
  · intro i hleft hright
    have hiWords :
        i < ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes).length := by
      simpa [memorySliceWords, List.length_map, eventChunkBytes32_length] using hright
    have hwrite := eventSignatureScratch_read_getElem_val
      (eventDef := eventDef) (ptr := ptr) (srcMemory := srcMemory)
      hiWords hlimit
    have hsrc := eventSignatureMemory_read_getElem
      (eventDef := eventDef) (i := i) hiWords hlimit
    simpa [memorySliceWords] using
      (calc
        (SourceSemantics.writeEventSignatureScratchFrom
            ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)
            ptr 0 srcMemory ((ptr + i * 32) % Compiler.Constants.evmModulus)).val =
          ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)[i] := hwrite
        _ = SourceSemantics.eventSignatureMemory eventDef ((0 + i * 32) % Compiler.Constants.evmModulus) :=
          hsrc.symm)

private theorem eventYulLogDataWords_eq_of_getElem
    {memory : Nat → Nat} {ptr : Nat} :
    ∀ {values : List Nat},
      (∀ i (hi : i < values.length),
        memory ((ptr + i * 32) % Compiler.Constants.evmModulus) =
          values[i]) →
      yulLogDataWords memory ptr (32 * values.length) = values
  | values, hread => by
      apply List.ext_getElem
      · simp [yulLogDataWords]
      · intro i hleft hright
        simpa [yulLogDataWords] using hread i hright

private theorem eventWriteUnindexedScratch_preserve_before :
    ∀ {params : List EventParam} {values : List Nat}
      {ptr wordIdx baseIdx : Nat}
      {memory memory' : Nat → Verity.Core.Uint256},
      SourceSemantics.writeUnindexedEventScratchFrom
          params values ptr wordIdx memory = some memory' →
      (∀ param ∈ params, (param.kind == EventParamKind.unindexed) = true) →
      wordIdx + params.length ≤ eventScratchSizeLimit →
      baseIdx < wordIdx →
      baseIdx < eventScratchSizeLimit →
      memory' ((ptr + baseIdx * 32) % Compiler.Constants.evmModulus) =
        memory ((ptr + baseIdx * 32) % Compiler.Constants.evmModulus)
  | [], [], _, _, _, _, _, hwrite, _, _, _, _ => by
      simp [SourceSemantics.writeUnindexedEventScratchFrom] at hwrite
      cases hwrite
      rfl
  | param :: params, value :: values, ptr, wordIdx, baseIdx, memory, memory',
      hwrite, hall, hlimit, hbefore, hbaseLimit => by
      have hkind : (param.kind == EventParamKind.unindexed) = true := hall param (by simp)
      simp [SourceSemantics.writeUnindexedEventScratchFrom, hkind] at hwrite
      have hpres := eventWriteUnindexedScratch_preserve_before
        (params := params) (values := values) (ptr := ptr)
        (wordIdx := wordIdx + 1) (baseIdx := baseIdx)
        (memory := fun offset =>
          if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
            (SourceSemantics.normalizeEventValue param.ty value : Verity.Core.Uint256)
          else memory offset)
        (memory' := memory') hwrite (by intro p hp; exact hall p (by simp [hp]))
        (by have hlimit' : wordIdx + (params.length + 1) ≤ eventScratchSizeLimit := by
              simpa using hlimit
            omega)
        (by omega) hbaseLimit
      have hne :
          (ptr + baseIdx * 32) % Compiler.Constants.evmModulus ≠
            (ptr + wordIdx * 32) % Compiler.Constants.evmModulus := by
        intro hkey
        have heq := eventScratchKey_injective_of_lt hbaseLimit
          (by have hlimit' : wordIdx + (params.length + 1) ≤ eventScratchSizeLimit := by
                simpa using hlimit
              omega)
          hkey
        omega
      rw [hpres]
      simp [hne]
  | [], _ :: _, _, _, _, _, _, hwrite, _, _, _, _ => by
      simp [SourceSemantics.writeUnindexedEventScratchFrom] at hwrite
  | _ :: _, [], _, _, _, _, _, hwrite, _, _, _, _ => by
      simp [SourceSemantics.writeUnindexedEventScratchFrom] at hwrite

private theorem eventWriteUnindexedScratch_read_head
    {param : EventParam} {params : List EventParam} {value : Nat}
    {values : List Nat} {ptr wordIdx : Nat}
    {memory memory' : Nat → Verity.Core.Uint256}
    (hwrite : SourceSemantics.writeUnindexedEventScratchFrom
        (param :: params) (value :: values) ptr wordIdx memory = some memory')
    (hall : ∀ p ∈ param :: params,
      (p.kind == EventParamKind.unindexed) = true)
    (hlimit : wordIdx + (param :: params).length ≤ eventScratchSizeLimit) :
    (memory' ((ptr + wordIdx * 32) % Compiler.Constants.evmModulus)).val =
      SourceSemantics.normalizeEventValue param.ty value := by
  have hkind : (param.kind == EventParamKind.unindexed) = true := hall param (by simp)
  simp [SourceSemantics.writeUnindexedEventScratchFrom, hkind] at hwrite
  have hpres := eventWriteUnindexedScratch_preserve_before
    (params := params) (values := values) (ptr := ptr)
    (wordIdx := wordIdx + 1) (baseIdx := wordIdx)
    (memory := fun offset =>
      if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
        (SourceSemantics.normalizeEventValue param.ty value : Verity.Core.Uint256)
      else memory offset)
    (memory' := memory') hwrite (by intro p hp; exact hall p (by simp [hp]))
    (by have hlimit' : wordIdx + (params.length + 1) ≤ eventScratchSizeLimit := by
          simpa using hlimit
        omega)
    (by omega)
    (lt_of_lt_of_le (by omega : wordIdx < wordIdx + (params.length + 1))
      (by simpa using hlimit))
  have hnorm := eventNormalizeEventValue_lt_evmModulus_any param.ty value
  simpa [hpres, Nat.mod_eq_of_lt hnorm]

private theorem eventWriteUnindexedScratch_read_getElem :
    ∀ {params : List EventParam} {values : List Nat}
      {ptr wordIdx : Nat} {memory memory' : Nat → Verity.Core.Uint256},
      SourceSemantics.writeUnindexedEventScratchFrom
          params values ptr wordIdx memory = some memory' →
      (∀ param ∈ params, (param.kind == EventParamKind.unindexed) = true) →
      values.length = params.length →
      wordIdx + params.length ≤ eventScratchSizeLimit →
      ∀ i (hi : i < values.length) (hpi : i < params.length),
        (memory' ((ptr + (wordIdx + i) * 32) %
          Compiler.Constants.evmModulus)).val =
          SourceSemantics.normalizeEventValue (params[i]'hpi).ty values[i]
  | param :: params, value :: values, ptr, wordIdx, memory, memory',
      hwrite, hall, hlen, hlimit, i, hi, hpi => by
      have hkind : (param.kind == EventParamKind.unindexed) = true := hall param (by simp)
      simp [SourceSemantics.writeUnindexedEventScratchFrom, hkind] at hwrite
      cases i with
      | zero =>
          simpa using eventWriteUnindexedScratch_read_head
            (param := param) (params := params) (value := value)
            (values := values) (ptr := ptr) (wordIdx := wordIdx)
            (memory := memory) (memory' := memory') (by
              simpa [SourceSemantics.writeUnindexedEventScratchFrom, hkind] using hwrite)
            hall hlimit
      | succ i =>
          have htailLen : values.length = params.length := by
            simpa using Nat.succ.inj hlen
          have htailLimit : wordIdx + 1 + params.length ≤ eventScratchSizeLimit := by
            have hlimit' : wordIdx + (params.length + 1) ≤ eventScratchSizeLimit := by
              simpa using hlimit
            omega
          have htail := eventWriteUnindexedScratch_read_getElem
            (params := params) (values := values) (ptr := ptr)
            (wordIdx := wordIdx + 1) (memory' := memory') hwrite
            (by intro p hp; exact hall p (by simp [hp])) htailLen htailLimit i
            (by simpa using hi) (by simpa using hpi)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  | [], [], _, _, _, _, hwrite, _, _, _, i, hi, _ => by
      simp at hi
  | [], _ :: _, _, _, _, _, hwrite, _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, [], _, _, _, _, hwrite, _, hlen, _, _, hi, _ => by
      simp at hi

private theorem eventEncodedValuesForKind_unindexed_all_length :
    ∀ {params : List EventParam} {values : List Nat},
      (∀ param ∈ params, (param.kind == EventParamKind.unindexed) = true) →
      values.length = params.length →
      (eventEncodedValuesForKind EventParamKind.unindexed params values).length =
        values.length
  | [], [], _, _ => by
      simp [eventEncodedValuesForKind]
  | param :: params, value :: values, hall, hlen => by
      have hkind : (param.kind == EventParamKind.unindexed) = true := hall param (by simp)
      have htail := eventEncodedValuesForKind_unindexed_all_length
        (params := params) (values := values)
        (by intro p hp; exact hall p (by simp [hp]))
        (by simpa using Nat.succ.inj hlen)
      simp [eventEncodedValuesForKind, hkind, htail]
  | [], _ :: _, _, hlen => by
      simp at hlen
  | _ :: _, [], _, hlen => by
      simp at hlen

private theorem eventEncodedValuesForKind_unindexed_all_getElem :
    ∀ {params : List EventParam} {values : List Nat},
      (hall : ∀ param ∈ params,
        (param.kind == EventParamKind.unindexed) = true) →
      (hlen : values.length = params.length) →
      ∀ i (hi : i < values.length) (hpi : i < params.length)
        (hei : i <
          (eventEncodedValuesForKind EventParamKind.unindexed params values).length),
        (eventEncodedValuesForKind EventParamKind.unindexed params values)[i]'hei =
          SourceSemantics.normalizeEventValue (params[i]'hpi).ty values[i]
  | param :: params, value :: values, hall, hlen, i, hi, hpi, hei => by
      have hkind : (param.kind == EventParamKind.unindexed) = true := hall param (by simp)
      cases i with
      | zero =>
          simp [eventEncodedValuesForKind, hkind]
      | succ i =>
          have htail := eventEncodedValuesForKind_unindexed_all_getElem
            (params := params) (values := values)
            (by intro p hp; exact hall p (by simp [hp]))
            (by simpa using Nat.succ.inj hlen) i
            (by simpa using hi) (by simpa using hpi)
            (by simpa [eventEncodedValuesForKind, hkind] using hei)
          simpa [eventEncodedValuesForKind, hkind] using htail
  | [], [], _, _, i, hi, _, _ => by
      simp at hi
  | [], _ :: _, _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, [], _, _, _, hi, _, _ => by
      simp at hi

private theorem eventYulLogDataWords_of_writeUnindexedScratch
    {params : List EventParam} {values : List Nat}
    {ptr : Nat} {memory memory' : Nat → Verity.Core.Uint256}
    (hwrite : SourceSemantics.writeUnindexedEventScratchFrom
        params values ptr 0 memory = some memory')
    (hall : ∀ param ∈ params,
      (param.kind == EventParamKind.unindexed) = true)
    (hlen : values.length = params.length)
    (hlimit : params.length ≤ eventScratchSizeLimit) :
    yulLogDataWords (fun offset => (memory' offset).val) ptr
        (32 * values.length) =
      eventEncodedValuesForKind EventParamKind.unindexed params values := by
  have hencLen := eventEncodedValuesForKind_unindexed_all_length
    (params := params) (values := values) hall hlen
  have hread :
      ∀ i (hi : i <
          (eventEncodedValuesForKind EventParamKind.unindexed params values).length),
        (memory' ((ptr + i * 32) % Compiler.Constants.evmModulus)).val =
          (eventEncodedValuesForKind EventParamKind.unindexed params values)[i] := by
    intro i hi
    have hiv : i < values.length := by simpa [hencLen] using hi
    have hip : i < params.length := by omega
    have hmem := eventWriteUnindexedScratch_read_getElem
      (params := params) (values := values) (ptr := ptr) (wordIdx := 0)
      (memory := memory) (memory' := memory') hwrite hall hlen (by simpa using hlimit)
      i hiv hip
    have henc := eventEncodedValuesForKind_unindexed_all_getElem
      (params := params) (values := values) hall hlen i hiv hip hi
    simpa [henc] using hmem
  have hyul := eventYulLogDataWords_eq_of_getElem
    (memory := fun offset => (memory' offset).val) (ptr := ptr)
    (values := eventEncodedValuesForKind EventParamKind.unindexed params values) hread
  simpa [hencLen] using hyul

/-! ## Log statement execution -/

private theorem eventLogStmt_continue_zero
    {state : IRState} {ptr dataSize topic0 : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (htopic0 : state.getVar "__evt_topic0" = some topic0) :
    StmtsContinueFromTo state
      [YulStmt.expr (YulExpr.call (eventLogFunction ([] : List (EventParam × Expr × YulExpr)).length)
        (eventLogArgs (YulExpr.lit dataSize)
          (scalarEventIndexedTopicParts ([] : List (EventParam × Expr × YulExpr)))))]
      (state.appendYulLog ptr dataSize [topic0]) := by
  refine ⟨state.appendYulLog ptr dataSize [topic0], ?_, rfl⟩
  intro extraFuel
  apply eventExecIRStmt_log1_step
  simp [eventLogFunction, eventLogArgs, scalarEventIndexedTopicParts, evalIRExprs,
    evalIRExpr, hptr, htopic0]

private theorem eventLogStmt_continue_one
    {scope : List String} {state : IRState}
    {ptr dataSize topic0 : Nat}
    {p1 : EventParam × Expr × YulExpr} {v1 : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hrel : List.Forall₂ (EventIndexedEntryOk scope state) [p1] [v1]) :
    StmtsContinueFromTo state
      [YulStmt.expr (YulExpr.call (eventLogFunction [p1].length)
        (eventLogArgs (YulExpr.lit dataSize)
          (scalarEventIndexedTopicParts [p1])))]
      (state.appendYulLog ptr dataSize
        [topic0, SourceSemantics.normalizeEventValue p1.1.ty v1]) := by
  rcases hrel with _ | ⟨hpv, _⟩
  rcases p1 with ⟨param1, src1, arg1⟩
  rcases hpv with ⟨heval1, hsupport1, hlt1, _hshape1, hkind1⟩
  have hnorm1 := eventEvalIRExpr_normalizeEventWord param1.ty hsupport1 heval1 hlt1
  refine ⟨state.appendYulLog ptr dataSize
      [topic0, SourceSemantics.normalizeEventValue param1.ty v1], ?_, rfl⟩
  intro extraFuel
  apply eventExecIRStmt_log2_step
  simp [eventLogFunction, eventLogArgs, scalarEventIndexedTopicParts,
    evalIRExprs, evalIRExpr, hptr, htopic0, hnorm1]

private theorem eventLogStmt_continue_two
    {scope : List String} {state : IRState}
    {ptr dataSize topic0 : Nat}
    {p1 p2 : EventParam × Expr × YulExpr} {v1 v2 : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hrel : List.Forall₂ (EventIndexedEntryOk scope state) [p1, p2] [v1, v2]) :
    StmtsContinueFromTo state
      [YulStmt.expr (YulExpr.call (eventLogFunction [p1, p2].length)
        (eventLogArgs (YulExpr.lit dataSize)
          (scalarEventIndexedTopicParts [p1, p2])))]
      (state.appendYulLog ptr dataSize
        [topic0, SourceSemantics.normalizeEventValue p1.1.ty v1,
          SourceSemantics.normalizeEventValue p2.1.ty v2]) := by
  rcases hrel with _ | ⟨hpv1, hrelTail⟩
  rcases hrelTail with _ | ⟨hpv2, _⟩
  rcases p1 with ⟨param1, src1, arg1⟩
  rcases p2 with ⟨param2, src2, arg2⟩
  rcases hpv1 with ⟨heval1, hsupport1, hlt1, _hshape1, _hkind1⟩
  rcases hpv2 with ⟨heval2, hsupport2, hlt2, _hshape2, _hkind2⟩
  have hnorm1 := eventEvalIRExpr_normalizeEventWord param1.ty hsupport1 heval1 hlt1
  have hnorm2 := eventEvalIRExpr_normalizeEventWord param2.ty hsupport2 heval2 hlt2
  refine ⟨state.appendYulLog ptr dataSize
      [topic0, SourceSemantics.normalizeEventValue param1.ty v1,
        SourceSemantics.normalizeEventValue param2.ty v2], ?_, rfl⟩
  intro extraFuel
  apply eventExecIRStmt_log3_step
  simp [eventLogFunction, eventLogArgs, scalarEventIndexedTopicParts,
    evalIRExprs, evalIRExpr, hptr, htopic0, hnorm1, hnorm2]

private theorem eventLogStmt_continue_three
    {scope : List String} {state : IRState}
    {ptr dataSize topic0 : Nat}
    {p1 p2 p3 : EventParam × Expr × YulExpr} {v1 v2 v3 : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hrel : List.Forall₂ (EventIndexedEntryOk scope state)
      [p1, p2, p3] [v1, v2, v3]) :
    StmtsContinueFromTo state
      [YulStmt.expr (YulExpr.call (eventLogFunction [p1, p2, p3].length)
        (eventLogArgs (YulExpr.lit dataSize)
          (scalarEventIndexedTopicParts [p1, p2, p3])))]
      (state.appendYulLog ptr dataSize
        [topic0, SourceSemantics.normalizeEventValue p1.1.ty v1,
          SourceSemantics.normalizeEventValue p2.1.ty v2,
          SourceSemantics.normalizeEventValue p3.1.ty v3]) := by
  rcases hrel with _ | ⟨hpv1, hrelTail⟩
  rcases hrelTail with _ | ⟨hpv2, hrelTail⟩
  rcases hrelTail with _ | ⟨hpv3, _⟩
  rcases p1 with ⟨param1, src1, arg1⟩
  rcases p2 with ⟨param2, src2, arg2⟩
  rcases p3 with ⟨param3, src3, arg3⟩
  rcases hpv1 with ⟨heval1, hsupport1, hlt1, _hshape1, _hkind1⟩
  rcases hpv2 with ⟨heval2, hsupport2, hlt2, _hshape2, _hkind2⟩
  rcases hpv3 with ⟨heval3, hsupport3, hlt3, _hshape3, _hkind3⟩
  have hnorm1 := eventEvalIRExpr_normalizeEventWord param1.ty hsupport1 heval1 hlt1
  have hnorm2 := eventEvalIRExpr_normalizeEventWord param2.ty hsupport2 heval2 hlt2
  have hnorm3 := eventEvalIRExpr_normalizeEventWord param3.ty hsupport3 heval3 hlt3
  refine ⟨state.appendYulLog ptr dataSize
      [topic0, SourceSemantics.normalizeEventValue param1.ty v1,
        SourceSemantics.normalizeEventValue param2.ty v2,
        SourceSemantics.normalizeEventValue param3.ty v3], ?_, rfl⟩
  intro extraFuel
  apply eventExecIRStmt_log4_step
  simp [eventLogFunction, eventLogArgs, scalarEventIndexedTopicParts,
    evalIRExprs, evalIRExpr, hptr, htopic0, hnorm1, hnorm2, hnorm3]

private theorem eventRuntimeStateMatchesIR_after_emit
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {sourceMemory : Nat → Verity.Core.Uint256} {irMemory : Nat → Nat}
    {event : Verity.Event} {irEvent : List Nat}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hmemory : irMemory = fun o => (sourceMemory o).val)
    (hevent : irEvent = SourceSemantics.encodeEvent event) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            memory := sourceMemory
            events := runtime.world.events ++ [event] } }
      { state with
          memory := irMemory
          events := state.events ++ [irEvent] } := by
  have hevents :
      state.events ++ [irEvent] =
        SourceSemantics.encodeEvents (runtime.world.events ++ [event]) := by
    have hstateEvents :
        state.events = SourceSemantics.encodeEvents runtime.world.events := by
      exact hmatch.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    simp [hstateEvents, hevent, eventEncodeEvents_snoc]
  exact FunctionBody.runtimeStateMatchesIR_updateMemoryEvents
    hmatch sourceMemory irMemory (runtime.world.events ++ [event])
      (state.events ++ [irEvent]) hmemory hevents

private theorem eventBindingsExactlyMatch_after_emit
    {scope : List String} {bindings : List (String × Nat)} {state : IRState}
    {ptr topic0 : Nat} {irMemory : Nat → Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hfresh : "__evt_ptr" ∉ scope ∧ "__evt_topic0" ∉ scope) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { (state.setVar "__evt_ptr" ptr).setVar "__evt_topic0" topic0 with
          memory := irMemory
          events := ((state.setVar "__evt_ptr" ptr).setVar "__evt_topic0" topic0).events } := by
  have hexactPtr :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
        (state.setVar "__evt_ptr" ptr) :=
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact hfresh.1
  have hexactTopic :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
        ((state.setVar "__evt_ptr" ptr).setVar "__evt_topic0" topic0) :=
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexactPtr hfresh.2
  intro name hname
  simpa [IRState.getVar] using hexactTopic name hname

private theorem eventCompileStmt_emit_scalar_shape
    {fields : List Field} {spec : CompilationModel} {scope : List String}
    {eventName : String} {args : List Expr} {compiledIR : List YulStmt}
    (hsupport : eventEmissionProofSupported spec.events eventName args = true)
    (hsurface : args.any exprTouchesUnsupportedContractSurface = false)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata
        [] false scope [] (Stmt.emit eventName args) = Except.ok compiledIR) :
    ∃ eventDef argExprs,
      spec.events.find? (·.name == eventName) = some eventDef ∧
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs ∧
      compiledIR = compileScalarEmitFromCompiledArgs eventDef args argExprs := by
  have hcore := eventExprList_compile_core_of_contractSurfaceClosed hsurface
  rcases compileExprList_core_ok (fields := fields) hcore with ⟨argExprs, hargExprs⟩
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨eventDef, hfind, hscalar, hlen⟩
  have hindexedGuard :
      ¬ 3 < (eventIndexedArgs (eventZippedWithSource eventDef args argExprs)).length := by
    exact Nat.not_lt.mpr
      (eventEmissionProofSupported_eventIndexedArgs_length_le_three
        argExprs hsupport hfind)
  have hscalarCompile :
      eventDefScalarCompileSupported eventDef = true := by
    simpa [eventDefScalarProofSupported] using hscalar
  simp only [CompilationModel.compileStmt, CompilationModel.compileEmit] at hcompile
  simp [hfind, hlen, hargExprs, hindexedGuard, hscalarCompile,
    Bind.bind, Except.bind, pure, Except.pure] at hcompile
  exact ⟨eventDef, argExprs, hfind, hargExprs, hcompile.symm⟩

private theorem eventParams_supported_and_head_size
    {events : List EventDef} {eventName : String} {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    (∀ param ∈ eventDef.params, eventParamScalarProofSupported param.ty = true) ∧
      (∀ param ∈ eventDef.params, eventHeadWordSize param.ty = 32) := by
  constructor
  · intro param hparam
    exact eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
      hsupport hfind hparam
  · intro param hparam
    exact eventEmissionProofSupported_param_eventHeadWordSize_eq_thirty_two
      hsupport hfind hparam

private theorem eventUnindexedEntriesOk_of_eval :
    ∀ {scope : List String} {state : IRState}
      {params : List EventParam} {args : List Expr}
      {argExprs : List YulExpr} {values : List Nat},
      List.Forall₂ (fun argExpr value => evalIRExpr state argExpr = some value)
        argExprs values →
      List.Forall₂ (fun argExpr _ => AtomicArgIR scope argExpr) argExprs args →
      (∀ param ∈ params, eventParamScalarProofSupported param.ty = true) →
      (∀ param ∈ params, eventHeadWordSize param.ty = 32) →
      (∀ value ∈ values, value < Compiler.Constants.evmModulus) →
      args.length = params.length →
      List.Forall₂ (EventUnindexedEntryOk scope state)
        (((params.zip args).zip argExprs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr))).filter
            (fun (p, _, _) => p.kind == EventParamKind.unindexed))
        (eventValuesForKind EventParamKind.unindexed params values)
  | _, _, [], [], [], [], _, _, _, _, _, _ => by
      simp [eventValuesForKind]
  | scope, state, param :: params, arg :: args, argExpr :: argExprs,
      value :: values, hevals, hshapes, hsupport, hsizes, hvaluesLt, hlen => by
      rcases hevals with _ | ⟨heval, hevalsTail⟩
      rcases hshapes with _ | ⟨hshape, hshapesTail⟩
      have htail := eventUnindexedEntriesOk_of_eval
        (scope := scope) (state := state) (params := params) (args := args)
        (argExprs := argExprs) (values := values) hevalsTail hshapesTail
        (by intro p hp; exact hsupport p (by simp [hp]))
        (by intro p hp; exact hsizes p (by simp [hp]))
        (by intro v hv; exact hvaluesLt v (by simp [hv]))
        (by simpa using Nat.succ.inj hlen)
      by_cases hkind : (param.kind == EventParamKind.unindexed) = true
      · simp [eventValuesForKind, hkind, htail, EventUnindexedEntryOk, heval,
          hshape, hsupport param (by simp), hsizes param (by simp)]
        exact hvaluesLt value (by simp)
      · have hkindFalse : (param.kind == EventParamKind.unindexed) = false := by
          cases h : param.kind == EventParamKind.unindexed <;> simp [h] at hkind ⊢
        simp [eventValuesForKind, hkindFalse, htail]
  | _, _, [], [], [], _ :: _, hevals, _, _, _, _, _ => by
      cases hevals
  | _, _, [], [], _ :: _, _, _, hshapes, _, _, _, _ => by
      cases hshapes
  | _, _, [], _ :: _, _, _, _, _, _, _, _, hlen => by
      simp at hlen
  | _, _, _ :: _, [], _, _, _, _, _, _, _, hlen => by
      simp at hlen
  | _, _, _ :: _, _ :: _, [], _, _, hshapes, _, _, _, _ => by
      cases hshapes
  | _, _, _ :: _, _ :: _, _ :: _, [], hevals, _, _, _, _, _ => by
      cases hevals

private theorem eventIndexedEntriesOk_of_eval :
    ∀ {scope : List String} {state : IRState}
      {params : List EventParam} {args : List Expr}
      {argExprs : List YulExpr} {values : List Nat},
      List.Forall₂ (fun argExpr value => evalIRExpr state argExpr = some value)
        argExprs values →
      List.Forall₂ (fun argExpr _ => AtomicArgIR scope argExpr) argExprs args →
      (∀ param ∈ params, eventParamScalarProofSupported param.ty = true) →
      (∀ value ∈ values, value < Compiler.Constants.evmModulus) →
      args.length = params.length →
      List.Forall₂ (EventIndexedEntryOk scope state)
        (((params.zip args).zip argExprs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr))).filter
            (fun (p, _, _) => p.kind == EventParamKind.indexed))
        (eventValuesForKind EventParamKind.indexed params values)
  | _, _, [], [], [], [], _, _, _, _, _ => by
      simp [eventValuesForKind]
  | scope, state, param :: params, arg :: args, argExpr :: argExprs,
      value :: values, hevals, hshapes, hsupport, hvaluesLt, hlen => by
      rcases hevals with _ | ⟨heval, hevalsTail⟩
      rcases hshapes with _ | ⟨hshape, hshapesTail⟩
      have htail := eventIndexedEntriesOk_of_eval
        (scope := scope) (state := state) (params := params) (args := args)
        (argExprs := argExprs) (values := values) hevalsTail hshapesTail
        (by intro p hp; exact hsupport p (by simp [hp]))
        (by intro v hv; exact hvaluesLt v (by simp [hv]))
        (by simpa using Nat.succ.inj hlen)
      by_cases hkind : (param.kind == EventParamKind.indexed) = true
      · simp [eventValuesForKind, hkind, htail, EventIndexedEntryOk, heval,
          hshape, hsupport param (by simp)]
        exact hvaluesLt value (by simp)
      · have hkindFalse : (param.kind == EventParamKind.indexed) = false := by
          cases h : param.kind == EventParamKind.indexed <;> simp [h] at hkind ⊢
        simp [eventValuesForKind, hkindFalse, htail]
  | _, _, [], [], [], _ :: _, hevals, _, _, _, _ => by
      cases hevals
  | _, _, [], [], _ :: _, _, _, hshapes, _, _, _ => by
      cases hshapes
  | _, _, [], _ :: _, _, _, _, _, _, _, hlen => by
      simp at hlen
  | _, _, _ :: _, [], _, _, _, _, _, _, hlen => by
      simp at hlen
  | _, _, _ :: _, _ :: _, [], _, _, hshapes, _, _, _ => by
      cases hshapes
  | _, _, _ :: _, _ :: _, _ :: _, [], hevals, _, _, _, _ => by
      cases hevals

private theorem eventCollectExprListNames_subset_scope
    {scope : List String} {args : List Expr}
    (hcore : ∀ expr ∈ args, FunctionBody.ExprCompileCore expr)
    (hinScope : ∀ expr ∈ args, FunctionBody.exprBoundNamesInScope expr scope) :
    ∀ name, name ∈ collectExprListNames args → name ∈ scope := by
  induction args with
  | nil =>
      intro name hmem
      simp [collectExprListNames] at hmem
  | cons arg rest ih =>
      intro name hmem
      simp [collectExprListNames] at hmem
      rcases hmem with hmem | hmem
      · exact hinScope arg (by simp) name
          (collectExprNames_mem_exprBoundNames_of_core
            (hcore arg (by simp)) name hmem)
      · exact ih
          (by intro expr hexpr; exact hcore expr (by simp [hexpr]))
          (by intro expr hexpr; exact hinScope expr (by simp [hexpr]))
          name hmem

private theorem eventStmtNextScope_emit_included
    {scope : List String} {eventName : String} {args : List Expr}
    (hcore : ∀ expr ∈ args, FunctionBody.ExprCompileCore expr)
    (hinScope : ∀ expr ∈ args, FunctionBody.exprBoundNamesInScope expr scope) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (Stmt.emit eventName args)) scope := by
  intro name hmem
  simp [stmtNextScope, collectStmtNames] at hmem
  rcases hmem with hmem | hmem
  · exact eventCollectExprListNames_subset_scope hcore hinScope name hmem
  · exact hmem

end Compiler.Proofs.IRGeneration
