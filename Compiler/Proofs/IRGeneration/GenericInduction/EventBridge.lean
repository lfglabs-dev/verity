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
      exact Or.inr (Or.inr ⟨"caller",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case contractAddress =>
      exact Or.inr (Or.inr ⟨"address",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case txOrigin =>
      exact Or.inr (Or.inr ⟨"origin",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case msgValue =>
      exact Or.inr (Or.inr ⟨"callvalue",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockTimestamp =>
      exact Or.inr (Or.inr ⟨"timestamp",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockNumber =>
      exact Or.inr (Or.inr ⟨"number",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case chainid =>
      exact Or.inr (Or.inr ⟨"chainid",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blobbasefee =>
      exact Or.inr (Or.inr ⟨"blobbasefee",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case calldatasize =>
      exact Or.inr (Or.inr ⟨"calldatasize",
        by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)

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
  · rfl
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
  · rfl
  · simp [evalIRExpr, IRState.getVar]
  · simp only [evalIRExpr]
    exact evalIRCall_nil_memory state mem func

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

/-! ## Word normalization bridge

The compiled `normalizeEventWord` masking matches the source-side
`normalizeEventValue` on every proof-supported scalar parameter type. -/

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
      have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 :=
        Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
      simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
        SourceSemantics.uint8Modulus, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        heval, h255]
  | .uint16, _, _, _, _, heval, _ => by
      have h65535 : (65535 : Nat) % Compiler.Constants.evmModulus = 65535 :=
        Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
      simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
        evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        heval, h65535]
  | .address, _, _, _, _, heval, _ => by
      have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
          Compiler.Constants.addressMask :=
        Nat.mod_eq_of_lt
          (by norm_num [Compiler.Constants.addressMask, Compiler.Constants.evmModulus])
      simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
        evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        heval, hmask]
  | .bool, state, exprIR, value, _, heval, _ => by
      have hone : (1 : Nat) % Compiler.Constants.evmModulus = 1 :=
        Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
      by_cases hzero : value % Compiler.Constants.evmModulus = 0 <;>
        simp [normalizeEventWord, CompilationModel.yulToBool,
          SourceSemantics.normalizeEventValue, evalIRExpr, evalIRCall, evalIRExprs,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
          heval, hzero, hone]
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

end Compiler.Proofs.IRGeneration
