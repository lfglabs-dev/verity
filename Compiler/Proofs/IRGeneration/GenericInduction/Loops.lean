import Compiler.Proofs.IRGeneration.GenericInduction.Storage

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

private def forEachZeroUsedNames (scope : List String) (varName : String) (body : List Stmt) :
    List String :=
  varName :: (scope ++ collectExprNames (Expr.literal 0) ++ collectStmtListNames body)

private def forEachZeroIdxName (scope : List String) (varName : String) (body : List Stmt) :
    String :=
  pickFreshName "__forEach_idx" (forEachZeroUsedNames scope varName body)

private def forEachZeroCountName (scope : List String) (varName : String) (body : List Stmt) :
    String :=
  pickFreshName "__forEach_count"
    (forEachZeroIdxName scope varName body :: forEachZeroUsedNames scope varName body)

private def forEachZeroInitStmts (scope : List String) (varName : String) (body : List Stmt) :
    List YulStmt :=
  [
    YulStmt.let_ (forEachZeroIdxName scope varName body) (YulExpr.lit 0),
    YulStmt.let_ (forEachZeroCountName scope varName body) (YulExpr.lit 0),
    YulStmt.let_ varName (YulExpr.lit 0)
  ]

private def forEachZeroCondExpr (scope : List String) (varName : String) (body : List Stmt) :
    YulExpr :=
  YulExpr.call "lt"
    [YulExpr.ident (forEachZeroIdxName scope varName body),
      YulExpr.ident (forEachZeroCountName scope varName body)]

private def forEachZeroPostStmts (scope : List String) (varName : String) (body : List Stmt) :
    List YulStmt :=
  [YulStmt.assign (forEachZeroIdxName scope varName body)
    (YulExpr.call "add" [YulExpr.ident (forEachZeroIdxName scope varName body), YulExpr.lit 1])]

private def forEachZeroBodyWithBind
    (scope : List String) (varName : String) (body : List Stmt) (bodyIR : List YulStmt) :
    List YulStmt :=
  YulStmt.assign varName (YulExpr.ident (forEachZeroIdxName scope varName body)) :: bodyIR

private def forEachZeroCompiledIR
    (scope : List String) (varName : String) (body : List Stmt) (bodyIR : List YulStmt) :
    List YulStmt :=
  [YulStmt.for_ (forEachZeroInitStmts scope varName body)
    (forEachZeroCondExpr scope varName body)
    (forEachZeroPostStmts scope varName body)
    (forEachZeroBodyWithBind scope varName body bodyIR)]

private def forEachLiteralBound (n : Nat) : Nat :=
  SourceSemantics.wordNormalize n

private def forEachLiteralUsedNames (scope : List String) (varName : String) (n : Nat) :
    List String :=
  varName :: (scope ++ collectExprNames (Expr.literal n) ++ collectStmtListNames [])

private def forEachLiteralIdxName (scope : List String) (varName : String) (n : Nat) :
    String :=
  pickFreshName "__forEach_idx" (forEachLiteralUsedNames scope varName n)

private def forEachLiteralCountName (scope : List String) (varName : String) (n : Nat) :
    String :=
  pickFreshName "__forEach_count"
    (forEachLiteralIdxName scope varName n :: forEachLiteralUsedNames scope varName n)

private def forEachLiteralInitStmts (scope : List String) (varName : String) (n : Nat) :
    List YulStmt :=
  [
    YulStmt.let_ (forEachLiteralIdxName scope varName n) (YulExpr.lit 0),
    YulStmt.let_ (forEachLiteralCountName scope varName n)
      (YulExpr.lit (forEachLiteralBound n)),
    YulStmt.let_ varName (YulExpr.lit 0)
  ]

private def forEachLiteralCompiledIR (scope : List String) (varName : String) (n : Nat) :
    List YulStmt :=
  [YulStmt.for_ (forEachLiteralInitStmts scope varName n)
    (YulExpr.call "lt"
      [YulExpr.ident (forEachLiteralIdxName scope varName n),
        YulExpr.ident (forEachLiteralCountName scope varName n)])
    [YulStmt.assign (forEachLiteralIdxName scope varName n)
      (YulExpr.call "add" [YulExpr.ident (forEachLiteralIdxName scope varName n), YulExpr.lit 1])]
    [YulStmt.assign varName (YulExpr.ident (forEachLiteralIdxName scope varName n))]]

private def forEachZeroRuntimeLoop
    (runtime : SourceSemantics.RuntimeState) (varName : String) :
    SourceSemantics.RuntimeState :=
  { runtime with bindings := SourceSemantics.bindValue runtime.bindings varName 0 }

private theorem sourceExec_forEach_literal_zero
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {varName : String}
    {body : List Stmt} :
    SourceSemantics.execStmt fields runtime (Stmt.forEach varName (Expr.literal 0) body) =
      .continue (forEachZeroRuntimeLoop runtime varName) := by
  change
    SourceSemantics.execForEachLoop varName
      (fun loopState => SourceSemantics.execStmtList fields loopState body)
      (forEachZeroRuntimeLoop runtime varName) 0 0 =
        .continue (forEachZeroRuntimeLoop runtime varName)
  rfl

private theorem sourceExec_forEach_literal_empty
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {varName : String}
    {n : Nat} :
    SourceSemantics.execStmt fields runtime (Stmt.forEach varName (Expr.literal n) []) =
      .continue
        (SourceSemantics.execForEachEmptyLoopFinal varName
          (forEachZeroRuntimeLoop runtime varName) 0 (forEachLiteralBound n)) := by
  change
    SourceSemantics.execForEachLoop varName
      (fun loopState => SourceSemantics.execStmtList fields loopState [])
      (forEachZeroRuntimeLoop runtime varName) 0 (SourceSemantics.wordNormalize n) =
        .continue
          (SourceSemantics.execForEachEmptyLoopFinal varName
            (forEachZeroRuntimeLoop runtime varName) 0 (forEachLiteralBound n))
  simpa [SourceSemantics.execStmtList, forEachLiteralBound] using
    SourceSemantics.execForEachLoop_empty_body varName
      (forEachZeroRuntimeLoop runtime varName) 0 (SourceSemantics.wordNormalize n)

private theorem forEachZero_fresh_facts
    {scope : List String}
    {varName : String}
    {body : List Stmt} :
    let idxName := forEachZeroIdxName scope varName body
    let countName := forEachZeroCountName scope varName body
    idxName ≠ varName ∧ countName ≠ varName ∧ countName ≠ idxName ∧
      idxName ∉ scope ∧ countName ∉ scope := by
  intro idxName countName
  have hidxFreshUsed :
      idxName ∉ forEachZeroUsedNames scope varName body := by
    simpa [idxName, forEachZeroIdxName] using
      CompilationModel.pickFreshName_not_mem_usedNames "__forEach_idx"
        (forEachZeroUsedNames scope varName body)
  have hcountFreshUsed :
      countName ∉ idxName :: forEachZeroUsedNames scope varName body := by
    simpa [countName, forEachZeroCountName, idxName] using
      CompilationModel.pickFreshName_not_mem_usedNames "__forEach_count"
        (idxName :: forEachZeroUsedNames scope varName body)
  constructor
  · intro h; exact hidxFreshUsed (by simp [forEachZeroUsedNames, h])
  constructor
  · intro h; exact hcountFreshUsed (by simp [forEachZeroUsedNames, h])
  constructor
  · intro h; exact hcountFreshUsed (by simp [h])
  constructor
  · intro hmem; exact hidxFreshUsed (by simp [forEachZeroUsedNames, hmem])
  · intro hmem; exact hcountFreshUsed (by simp [forEachZeroUsedNames, hmem])

private theorem forEachLiteral_fresh_facts
    {scope : List String}
    {varName : String}
    {n : Nat} :
    let idxName := forEachLiteralIdxName scope varName n
    let countName := forEachLiteralCountName scope varName n
    idxName ≠ varName ∧ countName ≠ varName ∧ countName ≠ idxName ∧
      idxName ∉ scope ∧ countName ∉ scope := by
  intro idxName countName
  have hidxFreshUsed :
      idxName ∉ forEachLiteralUsedNames scope varName n := by
    simpa [idxName, forEachLiteralIdxName] using
      CompilationModel.pickFreshName_not_mem_usedNames "__forEach_idx"
        (forEachLiteralUsedNames scope varName n)
  have hcountFreshUsed :
      countName ∉ idxName :: forEachLiteralUsedNames scope varName n := by
    simpa [countName, forEachLiteralCountName, idxName] using
      CompilationModel.pickFreshName_not_mem_usedNames "__forEach_count"
        (idxName :: forEachLiteralUsedNames scope varName n)
  constructor
  · intro h; exact hidxFreshUsed (by simp [forEachLiteralUsedNames, h])
  constructor
  · intro h; exact hcountFreshUsed (by simp [forEachLiteralUsedNames, h])
  constructor
  · intro h; exact hcountFreshUsed (by simp [h])
  constructor
  · intro hmem; exact hidxFreshUsed (by simp [forEachLiteralUsedNames, hmem])
  · intro hmem; exact hcountFreshUsed (by simp [forEachLiteralUsedNames, hmem])

private theorem evalIRExpr_forEachZeroCond_after_init
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {state : IRState}
    (hidx_ne_var : forEachZeroIdxName scope varName body ≠ varName)
    (hcount_ne_var : forEachZeroCountName scope varName body ≠ varName)
    (hcount_ne_idx :
      forEachZeroCountName scope varName body ≠ forEachZeroIdxName scope varName body) :
    evalIRExpr (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
      (forEachZeroCountName scope varName body) 0).setVar varName 0)
      (forEachZeroCondExpr scope varName body) = some 0 := by
  let idxName := forEachZeroIdxName scope varName body
  let countName := forEachZeroCountName scope varName body
  let stateIdx := state.setVar idxName 0
  let stateCount := stateIdx.setVar countName 0
  let stateLoop := stateCount.setVar varName 0
  have hidx_after : stateLoop.getVar idxName = some 0 := by
    dsimp [stateLoop, stateCount, stateIdx]
    rw [FunctionBody.getVar_setVar_ne _ varName idxName 0 hidx_ne_var]
    rw [FunctionBody.getVar_setVar_ne _ countName idxName 0 hcount_ne_idx.symm]
    simp
  have hcount_after : stateLoop.getVar countName = some 0 := by
    dsimp [stateLoop, stateCount, stateIdx]
    rw [FunctionBody.getVar_setVar_ne _ varName countName 0 hcount_ne_var]
    simp
  change evalIRExpr stateLoop (forEachZeroCondExpr scope varName body) = some 0
  simp [forEachZeroCondExpr, idxName, countName, evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    hidx_after, hcount_after]

private theorem forEachZero_initFuel_of_slack
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {bodyIR : List YulStmt}
    {extraFuel : Nat}
    (hslack : sizeOf (forEachZeroCompiledIR scope varName body bodyIR) -
      (forEachZeroCompiledIR scope varName body bodyIR).length ≤ extraFuel) :
    4 ≤ extraFuel := by
  have hmin : 4 ≤
      sizeOf (forEachZeroCompiledIR scope varName body bodyIR) -
        (forEachZeroCompiledIR scope varName body bodyIR).length := by
    dsimp [forEachZeroCompiledIR, forEachZeroInitStmts, forEachZeroCondExpr,
      forEachZeroPostStmts, forEachZeroBodyWithBind]
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, YulStmt.for_.sizeOf_spec,
      YulStmt.let_.sizeOf_spec, YulStmt.assign.sizeOf_spec, YulExpr.call.sizeOf_spec,
      YulExpr.ident.sizeOf_spec, YulExpr.lit.sizeOf_spec]
    omega
  omega

private def forEachEmptyLoopFinal
    (idxName varName : String) : Nat → IRState → Nat → IRState
  | _, state, 0 => state
  | idx, state, Nat.succ remaining =>
      forEachEmptyLoopFinal idxName varName (idx + 1)
        ((state.setVar varName idx).setVar idxName (idx + 1))
        remaining

private theorem execIRStmts_forEach_empty_body_assign
    {idxName varName : String}
    {fuel idx : Nat}
    {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hfuel : 2 ≤ fuel) :
    execIRStmts fuel state [YulStmt.assign varName (YulExpr.ident idxName)] =
      .continue (state.setVar varName idx) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [execIRStmts, execIRStmt, evalIRExpr, hidx]

private theorem execIRStmts_forEach_empty_post_increment
    {idxName varName : String}
    {fuel idx : Nat}
    {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hidx_ne_var : idxName ≠ varName)
    (hidxNextLt : idx + 1 < Compiler.Constants.evmModulus)
    (hfuel : 2 ≤ fuel) :
    execIRStmts fuel (state.setVar varName idx)
        [YulStmt.assign idxName
          (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])] =
      .continue ((state.setVar varName idx).setVar idxName (idx + 1)) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hidx_read :
              (state.setVar varName idx).getVar idxName = some idx := by
            rw [FunctionBody.getVar_setVar_ne _ varName idxName idx hidx_ne_var]
            exact hidx
          have hidxNextMod :
              (idx + 1) % Compiler.Constants.evmModulus = idx + 1 :=
            Nat.mod_eq_of_lt hidxNextLt
          simp [execIRStmts, execIRStmt, evalIRExpr, evalIRExprs, evalIRCall,
            Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
            hidx_read, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
            hidxNextMod]

private theorem evalIRExpr_forEach_empty_cond_lt
    {idxName countName : String}
    {idx remaining : Nat}
    {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some (idx + Nat.succ remaining))
    (hboundLt : idx + Nat.succ remaining < Compiler.Constants.evmModulus) :
    evalIRExpr state
        (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]) =
      some 1 := by
  have hidxLt : idx < Compiler.Constants.evmModulus := by omega
  simp [evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    hidx, hcount, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt hidxLt, Nat.mod_eq_of_lt hboundLt]

private theorem evalIRExpr_forEach_empty_cond_eq
    {idxName countName : String}
    {idx : Nat}
    {state : IRState}
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some idx) :
    evalIRExpr state
        (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]) =
      some 0 := by
  simp [evalIRExpr, evalIRExprs, evalIRCall,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    hidx, hcount]

private theorem execIRStmt_forEach_empty_loop_from_idx
    {idxName countName varName : String}
    (remaining idx fuel : Nat)
    (state : IRState)
    (hidx_ne_var : idxName ≠ varName)
    (hcount_ne_var : countName ≠ varName)
    (hcount_ne_idx : countName ≠ idxName)
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some (idx + remaining))
    (hboundLt : idx + remaining < Compiler.Constants.evmModulus)
    (hfuel : remaining + 2 ≤ fuel) :
    execIRStmt fuel state
        (.for_ []
          (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
          [YulStmt.assign idxName
            (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
          [YulStmt.assign varName (YulExpr.ident idxName)]) =
      .continue (forEachEmptyLoopFinal idxName varName idx state remaining) := by
  induction remaining generalizing idx fuel state with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact execIRStmt_for_init_cond_zero fuel state state []
            [YulStmt.assign idxName
              (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
            [YulStmt.assign varName (YulExpr.ident idxName)]
            (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
            (by simp [execIRStmts])
            (evalIRExpr_forEach_empty_cond_eq hidx (by simpa using hcount))
  | succ remaining ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfuelBody : 2 ≤ fuel := by omega
          have hbody :
              execIRStmts fuel state
                [YulStmt.assign varName (YulExpr.ident idxName)] =
                  .continue (state.setVar varName idx) :=
            execIRStmts_forEach_empty_body_assign hidx hfuelBody
          have hpost :
              execIRStmts fuel (state.setVar varName idx)
                [YulStmt.assign idxName
                  (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])] =
                  .continue ((state.setVar varName idx).setVar idxName (idx + 1)) :=
            execIRStmts_forEach_empty_post_increment hidx hidx_ne_var (by omega) hfuelBody
          have hidxNext :
              ((state.setVar varName idx).setVar idxName (idx + 1)).getVar idxName =
                some (idx + 1) :=
            FunctionBody.getVar_setVar_eq _ idxName (idx + 1)
          have hcountAfterVar :
              (state.setVar varName idx).getVar countName =
                some (idx + Nat.succ remaining) := by
            rw [FunctionBody.getVar_setVar_ne _ varName countName idx hcount_ne_var]
            exact hcount
          have hcountNext :
              ((state.setVar varName idx).setVar idxName (idx + 1)).getVar countName =
                some ((idx + 1) + remaining) := by
            rw [FunctionBody.getVar_setVar_ne _ idxName countName (idx + 1) hcount_ne_idx]
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcountAfterVar
          have htail :
              execIRStmt fuel ((state.setVar varName idx).setVar idxName (idx + 1))
                (.for_ []
                  (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
                  [YulStmt.assign idxName
                    (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
                  [YulStmt.assign varName (YulExpr.ident idxName)]) =
                .continue (forEachEmptyLoopFinal idxName varName (idx + 1)
                  ((state.setVar varName idx).setVar idxName (idx + 1)) remaining) :=
            ih (idx := idx + 1) (fuel := fuel)
              (state := (state.setVar varName idx).setVar idxName (idx + 1))
              hidxNext hcountNext (by omega) (by omega)
          rw [execIRStmt_for_one_continue
            (fuel := fuel) (state := state) (sInit := state)
            (sBody := state.setVar varName idx)
            (sPost := (state.setVar varName idx).setVar idxName (idx + 1))
            (init := [])
            (post := [YulStmt.assign idxName
              (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])])
            (body := [YulStmt.assign varName (YulExpr.ident idxName)])
            (cond := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
            (condValue := 1)]
          · exact htail
          · simp [execIRStmts]
          · exact evalIRExpr_forEach_empty_cond_lt hidx hcount hboundLt
          · norm_num
          · exact hbody
          · exact hpost

private theorem execIRStmt_forEach_empty_loop_idx_bound
    {idxName countName varName : String}
    (idx bound fuel : Nat)
    (state : IRState)
    (hidx_ne_var : idxName ≠ varName)
    (hcount_ne_var : countName ≠ varName)
    (hcount_ne_idx : countName ≠ idxName)
    (hidx : state.getVar idxName = some idx)
    (hcount : state.getVar countName = some bound)
    (hidx_le_bound : idx ≤ bound)
    (hboundLt : bound < Compiler.Constants.evmModulus)
    (hfuel : bound - idx + 2 ≤ fuel) :
    execIRStmt fuel state
        (.for_ []
          (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
          [YulStmt.assign idxName
            (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
          [YulStmt.assign varName (YulExpr.ident idxName)]) =
      .continue (forEachEmptyLoopFinal idxName varName idx state (bound - idx)) := by
  exact execIRStmt_forEach_empty_loop_from_idx
    (idxName := idxName) (countName := countName) (varName := varName)
    (remaining := bound - idx) (idx := idx) (fuel := fuel) (state := state)
    hidx_ne_var hcount_ne_var hcount_ne_idx hidx
    (by simpa [Nat.add_sub_of_le hidx_le_bound] using hcount)
    (by
      have hsum : idx + (bound - idx) = bound := Nat.add_sub_of_le hidx_le_bound
      simpa [hsum] using hboundLt)
    hfuel

private theorem forEachLiteral_loopFuel_of_slack
    {scope : List String}
    {varName : String}
    {n extraFuel : Nat}
    (hslack : sizeOf (forEachLiteralCompiledIR scope varName n) -
      (forEachLiteralCompiledIR scope varName n).length ≤ extraFuel) :
    forEachLiteralBound n + 2 ≤ extraFuel := by
  have hmin : forEachLiteralBound n + 2 ≤
      sizeOf (forEachLiteralCompiledIR scope varName n) -
        (forEachLiteralCompiledIR scope varName n).length := by
    dsimp [forEachLiteralCompiledIR, forEachLiteralInitStmts, forEachLiteralBound]
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, YulStmt.for_.sizeOf_spec,
      YulStmt.let_.sizeOf_spec, YulStmt.assign.sizeOf_spec, YulExpr.call.sizeOf_spec,
      YulExpr.ident.sizeOf_spec, YulExpr.lit.sizeOf_spec]
    have hboundSize :
        SourceSemantics.wordNormalize n ≤ sizeOf (SourceSemantics.wordNormalize n) := by
      simp
    omega
  omega

private theorem forEachLiteral_initFuel_of_slack
    {scope : List String}
    {varName : String}
    {n extraFuel : Nat}
    (hslack : sizeOf (forEachLiteralCompiledIR scope varName n) -
      (forEachLiteralCompiledIR scope varName n).length ≤ extraFuel) :
    4 ≤ extraFuel := by
  have hmin : 4 ≤
      sizeOf (forEachLiteralCompiledIR scope varName n) -
        (forEachLiteralCompiledIR scope varName n).length := by
    dsimp [forEachLiteralCompiledIR, forEachLiteralInitStmts, forEachLiteralBound]
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, YulStmt.for_.sizeOf_spec,
      YulStmt.let_.sizeOf_spec, YulStmt.assign.sizeOf_spec, YulExpr.call.sizeOf_spec,
      YulExpr.ident.sizeOf_spec, YulExpr.lit.sizeOf_spec]
    omega
  omega

private theorem execIRStmts_forEach_literal_empty_compiled
    {scope : List String}
    {varName : String}
    {n : Nat}
    {state : IRState}
    {extraFuel : Nat}
    (hslack : sizeOf (forEachLiteralCompiledIR scope varName n) -
      (forEachLiteralCompiledIR scope varName n).length ≤ extraFuel)
    (hidx_ne_var : forEachLiteralIdxName scope varName n ≠ varName)
    (hcount_ne_var : forEachLiteralCountName scope varName n ≠ varName)
    (hcount_ne_idx :
      forEachLiteralCountName scope varName n ≠ forEachLiteralIdxName scope varName n) :
    execIRStmts ((forEachLiteralCompiledIR scope varName n).length + extraFuel + 1) state
        (forEachLiteralCompiledIR scope varName n) =
      .continue
        (forEachEmptyLoopFinal (forEachLiteralIdxName scope varName n) varName 0
          (((state.setVar (forEachLiteralIdxName scope varName n) 0).setVar
            (forEachLiteralCountName scope varName n) (forEachLiteralBound n)).setVar
              varName 0)
          (forEachLiteralBound n)) := by
  let idxName := forEachLiteralIdxName scope varName n
  let countName := forEachLiteralCountName scope varName n
  let bound := forEachLiteralBound n
  let stateIdx := state.setVar idxName 0
  let stateCount := stateIdx.setVar countName bound
  let stateLoop := stateCount.setVar varName 0
  have hfuelInit : 4 ≤ extraFuel := forEachLiteral_initFuel_of_slack hslack
  have hfuelLoop : bound + 2 ≤ extraFuel := by
    simpa [bound] using forEachLiteral_loopFuel_of_slack
      (scope := scope) (varName := varName) (n := n) hslack
  have hinit : execIRStmts extraFuel state
      (forEachLiteralInitStmts scope varName n) = .continue stateLoop := by
    simpa [forEachLiteralInitStmts, stateIdx, stateCount, stateLoop, idxName, countName,
      bound] using
      execIRStmts_forEach_init_literal
        (fuel := extraFuel) (state := state) (idxName := idxName)
        (countName := countName) (varName := varName) (bound := bound)
        (hfuel := hfuelInit)
  have hidx_after_init : stateLoop.getVar idxName = some 0 := by
    dsimp [stateLoop, stateCount, stateIdx]
    rw [FunctionBody.getVar_setVar_ne _ varName idxName 0 hidx_ne_var]
    rw [FunctionBody.getVar_setVar_ne _ countName idxName bound hcount_ne_idx.symm]
    simp
  have hcount_after_init : stateLoop.getVar countName = some bound := by
    dsimp [stateLoop, stateCount, stateIdx]
    rw [FunctionBody.getVar_setVar_ne _ varName countName 0 hcount_ne_var]
    simp
  have hboundLt : bound < Compiler.Constants.evmModulus := by
    dsimp [bound, forEachLiteralBound]
    exact FunctionBody.wordNormalize_lt_evmModulus n
  have hloop :
      execIRStmt (Nat.succ extraFuel) stateLoop
        (.for_ []
          (YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
          [YulStmt.assign idxName
            (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
          [YulStmt.assign varName (YulExpr.ident idxName)]) =
        .continue (forEachEmptyLoopFinal idxName varName 0 stateLoop bound) := by
    simpa [Nat.zero_add] using
      execIRStmt_forEach_empty_loop_idx_bound
        (idxName := idxName) (countName := countName) (varName := varName)
        (idx := 0) (bound := bound) (fuel := Nat.succ extraFuel) (state := stateLoop)
        hidx_ne_var hcount_ne_var hcount_ne_idx hidx_after_init
        hcount_after_init (by omega) hboundLt (by omega)
  dsimp [forEachLiteralCompiledIR]
  have hfuelEq : extraFuel + 1 + 1 = 1 + extraFuel + 1 := by omega
  rw [← hfuelEq]
  exact execIRStmts_single_for_init_continue
    (fuel := extraFuel) (state := state) (sInit := stateLoop)
    (sFinal := forEachEmptyLoopFinal idxName varName 0 stateLoop bound)
    (init := forEachLiteralInitStmts scope varName n)
    (post := [YulStmt.assign idxName
      (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])])
    (body := [YulStmt.assign varName (YulExpr.ident idxName)])
    (cond := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName])
    hinit hloop

private theorem execIRStmts_forEach_literal_zero_compiled
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {bodyIR : List YulStmt}
    {state : IRState}
    {extraFuel : Nat}
    (hslack : sizeOf (forEachZeroCompiledIR scope varName body bodyIR) -
      (forEachZeroCompiledIR scope varName body bodyIR).length ≤ extraFuel)
    (hidx_ne_var : forEachZeroIdxName scope varName body ≠ varName)
    (hcount_ne_var : forEachZeroCountName scope varName body ≠ varName)
    (hcount_ne_idx :
      forEachZeroCountName scope varName body ≠ forEachZeroIdxName scope varName body) :
    execIRStmts ((forEachZeroCompiledIR scope varName body bodyIR).length + extraFuel + 1) state
        (forEachZeroCompiledIR scope varName body bodyIR) =
      .continue (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0).setVar varName 0) := by
  let idxName := forEachZeroIdxName scope varName body
  let countName := forEachZeroCountName scope varName body
  let stateIdx := state.setVar idxName 0
  let stateCount := stateIdx.setVar countName 0
  let stateLoop := stateCount.setVar varName 0
  have hfuelInit : 4 ≤ extraFuel := forEachZero_initFuel_of_slack hslack
  have hinit : execIRStmts extraFuel state
      (forEachZeroInitStmts scope varName body) = .continue stateLoop := by
    simpa [forEachZeroInitStmts, stateIdx, stateCount, stateLoop, idxName, countName] using
      execIRStmts_forEach_init_literal_zero
        (fuel := extraFuel) (state := state) (idxName := idxName)
        (countName := countName) (varName := varName) (hfuel := hfuelInit)
  have hcond : evalIRExpr stateLoop (forEachZeroCondExpr scope varName body) = some 0 := by
    simpa [stateLoop, stateCount, stateIdx, idxName, countName] using
      evalIRExpr_forEachZeroCond_after_init
        (scope := scope) (varName := varName) (body := body) (state := state)
        hidx_ne_var hcount_ne_var hcount_ne_idx
  dsimp [forEachZeroCompiledIR]
  have hfuelEq : extraFuel + 1 + 1 = 1 + extraFuel + 1 := by omega
  rw [← hfuelEq]
  exact execIRStmts_single_for_init_cond_zero
    (fuel := extraFuel) (state := state) (sInit := stateLoop)
    (init := forEachZeroInitStmts scope varName body)
    (post := forEachZeroPostStmts scope varName body)
    (body := forEachZeroBodyWithBind scope varName body bodyIR)
    (cond := forEachZeroCondExpr scope varName body) hinit hcond

private theorem forEachZero_nextScopeIncluded
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    (hbodyNames : ∀ name, name ∈ collectStmtListNames body → name ∈ varName :: scope) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (Stmt.forEach varName (Expr.literal 0) body))
      (varName :: scope) := by
  intro name hmem
  simp [stmtNextScope, collectStmtNames, collectExprNames] at hmem
  rcases hmem with hvar | hbody | hscopeMem
  · simp [hvar]
  · exact hbodyNames name hbody
  · simp [hscopeMem]

private theorem runtimeStateMatchesIR_forEachZeroLoop
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    FunctionBody.runtimeStateMatchesIR fields (forEachZeroRuntimeLoop runtime varName)
      (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0).setVar varName 0) := by
  simpa [forEachZeroRuntimeLoop] using
    FunctionBody.runtimeStateMatchesIR_setVar_bindValue
      (fields := fields)
      (runtime := runtime)
      (state := (state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0)
      (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
        (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime))
      varName 0

private theorem bindingsExactly_forEachZeroBase
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hidx_not_scope : forEachZeroIdxName scope varName body ∉ scope)
    (hcount_not_scope : forEachZeroCountName scope varName body ∉ scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
      (forEachZeroRuntimeLoop runtime varName).bindings
      (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0).setVar varName 0) := by
  have hexactCount :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
        ((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
          (forEachZeroCountName scope varName body) 0) :=
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact hidx_not_scope)
      hcount_not_scope
  simpa [forEachZeroRuntimeLoop] using
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
      (boundName := varName) (value := 0) hexactCount

private theorem stmtStepMatches_forEach_literal_zero_final
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hbodyNames : ∀ name, name ∈ collectStmtListNames body → name ∈ varName :: scope)
    (hidx_not_scope : forEachZeroIdxName scope varName body ∉ scope)
    (hcount_not_scope : forEachZeroCountName scope varName body ∉ scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    stmtStepMatchesIRExec fields
      (stmtNextScope scope (Stmt.forEach varName (Expr.literal 0) body))
      (.continue (forEachZeroRuntimeLoop runtime varName))
      (.continue (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0).setVar varName 0)) := by
  let runtimeLoop := forEachZeroRuntimeLoop runtime varName
  have hexactBase :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
        runtimeLoop.bindings
        (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
          (forEachZeroCountName scope varName body) 0).setVar varName 0) :=
    bindingsExactly_forEachZeroBase hidx_not_scope hcount_not_scope hexact
  have hNextScopeIncl := forEachZero_nextScopeIncluded
    (scope := scope) (varName := varName) (body := body) hbodyNames
  have hscopeBase : FunctionBody.scopeNamesPresent (varName :: scope) runtimeLoop.bindings := by
    simpa [runtimeLoop, forEachZeroRuntimeLoop] using
      FunctionBody.scopeNamesPresent_cons_bindValue
        (boundName := varName) (value := 0) hscope
  have hboundedLoop : FunctionBody.bindingsBounded runtimeLoop.bindings :=
    FunctionBody.bindingsBounded_bindValue hbounded varName 0
      (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS])
  simp [stmtStepMatchesIRExec]
  exact ⟨runtimeStateMatchesIR_forEachZeroLoop
      (fields := fields) (scope := scope) (varName := varName) (body := body)
      (runtime := runtime) (state := state) hruntime,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexactBase hNextScopeIncl,
    hboundedLoop,
    FunctionBody.scopeNamesPresent_of_included hscopeBase hNextScopeIncl⟩

private theorem forEach_empty_final_rel
    {fields : List Field}
    {scope : List String}
    {idxName varName : String}
    (idx remaining : Nat)
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hidx_not_next : idxName ∉ varName :: scope)
    (hboundLt : idx + remaining < Compiler.Constants.evmModulus)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
      runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent (varName :: scope) runtime.bindings) :
    FunctionBody.runtimeStateMatchesIR fields
        (SourceSemantics.execForEachEmptyLoopFinal varName runtime idx remaining)
        (forEachEmptyLoopFinal idxName varName idx state remaining) ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
        (SourceSemantics.execForEachEmptyLoopFinal varName runtime idx remaining).bindings
        (forEachEmptyLoopFinal idxName varName idx state remaining) ∧
      FunctionBody.bindingsBounded
        (SourceSemantics.execForEachEmptyLoopFinal varName runtime idx remaining).bindings ∧
      FunctionBody.scopeNamesPresent (varName :: scope)
        (SourceSemantics.execForEachEmptyLoopFinal varName runtime idx remaining).bindings := by
  induction remaining generalizing idx runtime state with
  | zero =>
      simpa [SourceSemantics.execForEachEmptyLoopFinal, forEachEmptyLoopFinal] using
        And.intro hruntime (And.intro hexact (And.intro hbounded hscope))
  | succ remaining ih =>
      have hidxLt : idx < Compiler.Constants.evmModulus := by omega
      have hnorm : SourceSemantics.wordNormalize idx = idx := by
        simp [SourceSemantics.wordNormalize, Compiler.Constants.evmModulus,
          Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt hidxLt]
      have hmod : idx % Compiler.Constants.evmModulus = idx :=
        Nat.mod_eq_of_lt hidxLt
      let runtimeStep : SourceSemantics.RuntimeState :=
        { runtime with bindings := SourceSemantics.bindValue runtime.bindings varName idx }
      let stateStep : IRState := (state.setVar varName idx).setVar idxName (idx + 1)
      have hruntimeStep :
          FunctionBody.runtimeStateMatchesIR fields runtimeStep stateStep := by
        dsimp [runtimeStep, stateStep]
        exact FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime varName idx)
      have hexactBind :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
            runtimeStep.bindings (state.setVar varName idx) := by
        dsimp [runtimeStep]
        exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
          (scope := scope) (boundName := varName) (value := idx)
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact
            (by intro name hmem; simp [hmem]))
      have hexactStep :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
            runtimeStep.bindings stateStep := by
        dsimp [stateStep]
        exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (state := state.setVar varName idx) (tempName := idxName) (value := idx + 1)
          hexactBind hidx_not_next
      have hboundedStep :
          FunctionBody.bindingsBounded runtimeStep.bindings := by
        dsimp [runtimeStep]
        exact FunctionBody.bindingsBounded_bindValue hbounded varName idx hidxLt
      have hscopeStep :
          FunctionBody.scopeNamesPresent (varName :: scope) runtimeStep.bindings := by
        dsimp [runtimeStep]
        exact FunctionBody.scopeNamesPresent_cons_bindValue
          (FunctionBody.scopeNamesPresent_of_included hscope
            (by intro name hmem; simp [hmem]))
      have htail := ih (idx := idx + 1) (runtime := runtimeStep) (state := stateStep)
        (by omega) hruntimeStep hexactStep hboundedStep hscopeStep
      simpa [SourceSemantics.execForEachEmptyLoopFinal, forEachEmptyLoopFinal,
        runtimeStep, stateStep, hnorm, hmod] using htail

private theorem stmtStepMatches_forEach_literal_empty_final
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {n : Nat}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hidx_ne_var : forEachLiteralIdxName scope varName n ≠ varName)
    (hidx_not_scope : forEachLiteralIdxName scope varName n ∉ scope)
    (hcount_not_scope : forEachLiteralCountName scope varName n ∉ scope)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    stmtStepMatchesIRExec fields
      (stmtNextScope scope (Stmt.forEach varName (Expr.literal n) []))
      (.continue
        (SourceSemantics.execForEachEmptyLoopFinal varName
          (forEachZeroRuntimeLoop runtime varName) 0 (forEachLiteralBound n)))
      (.continue
        (forEachEmptyLoopFinal (forEachLiteralIdxName scope varName n) varName 0
          (((state.setVar (forEachLiteralIdxName scope varName n) 0).setVar
            (forEachLiteralCountName scope varName n) (forEachLiteralBound n)).setVar
              varName 0)
          (forEachLiteralBound n))) := by
  let idxName := forEachLiteralIdxName scope varName n
  let countName := forEachLiteralCountName scope varName n
  let runtimeLoop := forEachZeroRuntimeLoop runtime varName
  let stateCount := (state.setVar idxName 0).setVar countName (forEachLiteralBound n)
  let stateLoop := stateCount.setVar varName 0
  have hidx_not_next : idxName ∉ varName :: scope := by
    intro hmem
    simp at hmem
    rcases hmem with hvar | hscopeMem
    · exact hidx_ne_var hvar
    · exact hidx_not_scope hscopeMem
  have hexactCount :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings stateCount := by
    dsimp [stateCount]
    exact FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact hidx_not_scope)
      hcount_not_scope
  have hexactLoop :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope (varName :: scope)
        runtimeLoop.bindings stateLoop := by
    simpa [runtimeLoop, forEachZeroRuntimeLoop, stateLoop] using
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
        (boundName := varName) (value := 0) hexactCount
  have hruntimeLoop :
      FunctionBody.runtimeStateMatchesIR fields runtimeLoop stateLoop := by
    simpa [runtimeLoop, forEachZeroRuntimeLoop, stateLoop, stateCount] using
      FunctionBody.runtimeStateMatchesIR_setVar_bindValue
        (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime))
        varName 0
  have hscopeLoop : FunctionBody.scopeNamesPresent (varName :: scope) runtimeLoop.bindings := by
    simpa [runtimeLoop, forEachZeroRuntimeLoop] using
      FunctionBody.scopeNamesPresent_cons_bindValue
        (boundName := varName) (value := 0) hscope
  have hboundedLoop : FunctionBody.bindingsBounded runtimeLoop.bindings :=
    FunctionBody.bindingsBounded_bindValue hbounded varName 0
      (by norm_num [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS])
  have hboundLt : 0 + forEachLiteralBound n < Compiler.Constants.evmModulus := by
    simpa [forEachLiteralBound] using FunctionBody.wordNormalize_lt_evmModulus n
  rcases forEach_empty_final_rel
      (fields := fields) (scope := scope) (idxName := idxName) (varName := varName)
      (idx := 0) (remaining := forEachLiteralBound n)
      (runtime := runtimeLoop) (state := stateLoop)
      hidx_not_next hboundLt hruntimeLoop hexactLoop hboundedLoop hscopeLoop with
    ⟨hruntimeFinal, hexactFinal, hboundedFinal, hscopeFinal⟩
  have hNextScopeIncl :
      FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (Stmt.forEach varName (Expr.literal n) []))
        (varName :: scope) := by
    intro name hmem
    simp [stmtNextScope, collectStmtNames, collectExprNames] at hmem
    rcases hmem with hvar | hscopeMem
    · simp [hvar]
    · rcases hscopeMem with hbody | hscopeMem
      · exact False.elim (by simpa [collectStmtListNames] using hbody)
      · simp [hscopeMem]
  simp [stmtStepMatchesIRExec]
  exact ⟨by simpa [idxName, countName, runtimeLoop, stateLoop, stateCount] using hruntimeFinal,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (by simpa [idxName, countName, runtimeLoop, stateLoop, stateCount] using hexactFinal)
      hNextScopeIncl,
    by simpa [runtimeLoop] using hboundedFinal,
    FunctionBody.scopeNamesPresent_of_included
      (by simpa [runtimeLoop] using hscopeFinal) hNextScopeIncl⟩

theorem compiledStmtStep_forEach_literal_zero
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {body : List Stmt}
    (hbodyNames : ∀ name, name ∈ collectStmtListNames body → name ∈ varName :: scope)
    (hbodyGeneric : StmtListGenericCore fields (varName :: scope) body) :
    ∃ compiledIR,
      CompiledStmtStep fields scope (Stmt.forEach varName (Expr.literal 0) body) compiledIR := by
  rcases compileStmtList_ok_of_stmtListGenericCore_early
      (fields := fields)
      (scope := varName :: scope)
      (inScopeNames := CompilationModel.forEachBodyScope scope varName (Expr.literal 0) body)
      hbodyGeneric
      (fun name hmem => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)) with
    ⟨bodyIR, hbodyCompile⟩
  refine ⟨forEachZeroCompiledIR scope varName body bodyIR, ?_⟩
  refine
    { compileOk := ?_
      preserves := ?_ }
  · dsimp [forEachZeroCompiledIR, forEachZeroInitStmts, forEachZeroCondExpr,
      forEachZeroPostStmts, forEachZeroBodyWithBind, forEachZeroIdxName,
      forEachZeroCountName, forEachZeroUsedNames]
    try unfold CompilationModel.compileStmt
    unfold CompilationModel.compileStmtWithFork
    simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
      CompilationModel.compileExpr, hbodyCompile]
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    rcases forEachZero_fresh_facts (scope := scope) (varName := varName) (body := body) with
      ⟨hidx_ne_var, hcount_ne_var, hcount_ne_idx, hidx_not_scope, hcount_not_scope⟩
    refine ⟨.continue (forEachZeroRuntimeLoop runtime varName),
      .continue (((state.setVar (forEachZeroIdxName scope varName body) 0).setVar
        (forEachZeroCountName scope varName body) 0).setVar varName 0),
      sourceExec_forEach_literal_zero, ?_, ?_⟩
    · exact execIRStmts_forEach_literal_zero_compiled
        (scope := scope) (varName := varName) (body := body) (bodyIR := bodyIR)
        (state := state) (extraFuel := extraFuel) hslack
        hidx_ne_var hcount_ne_var hcount_ne_idx
    · exact stmtStepMatches_forEach_literal_zero_final
        (fields := fields) (scope := scope) (varName := varName) (body := body)
        (runtime := runtime) (state := state) hbodyNames hidx_not_scope
        hcount_not_scope hexact hscope hbounded hruntime

theorem compiledStmtStep_forEach_literal_empty
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {n : Nat} :
    ∃ compiledIR,
      CompiledStmtStep fields scope (Stmt.forEach varName (Expr.literal n) []) compiledIR := by
  refine ⟨forEachLiteralCompiledIR scope varName n, ?_⟩
  refine
    { compileOk := ?_
      preserves := ?_ }
  · dsimp [forEachLiteralCompiledIR, forEachLiteralInitStmts, forEachLiteralIdxName,
      forEachLiteralCountName, forEachLiteralUsedNames, forEachLiteralBound]
    try unfold CompilationModel.compileStmt
    unfold CompilationModel.compileStmtWithFork
    simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
      FunctionBody.compileStmtList_nil_eq_ok,
      CompilationModel.compileExpr, CompilationModel.uint256Modulus]
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    rcases forEachLiteral_fresh_facts (scope := scope) (varName := varName) (n := n) with
      ⟨hidx_ne_var, hcount_ne_var, hcount_ne_idx, hidx_not_scope, hcount_not_scope⟩
    refine ⟨.continue
        (SourceSemantics.execForEachEmptyLoopFinal varName
          (forEachZeroRuntimeLoop runtime varName) 0 (forEachLiteralBound n)),
      .continue
        (forEachEmptyLoopFinal (forEachLiteralIdxName scope varName n) varName 0
          (((state.setVar (forEachLiteralIdxName scope varName n) 0).setVar
            (forEachLiteralCountName scope varName n) (forEachLiteralBound n)).setVar
              varName 0)
          (forEachLiteralBound n)),
      sourceExec_forEach_literal_empty, ?_, ?_⟩
    · exact execIRStmts_forEach_literal_empty_compiled
        (scope := scope) (varName := varName) (n := n)
        (state := state) (extraFuel := extraFuel) hslack
        hidx_ne_var hcount_ne_var hcount_ne_idx
    · exact stmtStepMatches_forEach_literal_empty_final
        (fields := fields) (scope := scope) (varName := varName) (n := n)
        (runtime := runtime) (state := state)
        hidx_ne_var hidx_not_scope hcount_not_scope
        hexact hscope hbounded hruntime

end Compiler.Proofs.IRGeneration
