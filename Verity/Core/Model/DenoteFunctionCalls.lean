import Verity.Core.Model.Denote
import Verity.Core.Model.DenoteExternalCalls
import Verity.Core.Model.MultiContract

/-!
# FunctionSpec denotation of raw and linked external calls

`Denote.evalExpr` maps `Expr.call` to `none`.
`Denote.execStmt` gives `Stmt.externalCallBind` /
`Stmt.tryExternalCallBind` oracle-driven semantics that mirror
`SourceSemantics`, keeping `DenoteAgreement` definitional.

This module is the widened fragment: a `CallEnv` supplies the
`AdversaryModel` (callee effect) and the link-time
target / value / siteId for a named external. ETH is debited from
the caller `selfBalance` only on a successful `call`. Failure and
revert keep the pre-call balance (journal still records the
attempt). No keccak injectivity, no new axiom.
-/

namespace Compiler.CompilationModel.DenoteFunctionCalls

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.DenoteExternalCalls
open Verity

/-- Link-time resolution of a named external. -/
structure LinkedExternal where
  target : Nat
  value : Nat := 0
  siteId : Nat := 0
  deriving Repr

/-- Environment for the widened call fragment. -/
structure CallEnv where
  oracle : DenoteOracle
  adversary : AdversaryModel
  resolve : String → Option LinkedExternal

/-- Word-addressed calldata read for `Expr.call` memory operands. -/
def readMemoryWords (mem : Nat → Core.Uint256) (offset size : Nat) : List Nat :=
  (List.range size).map (fun i => (mem (offset + i)).val)

/-- Word-addressed returndata write. Writes `min words.length outSize` words. -/
def writeMemoryWords (mem : Nat → Core.Uint256) (offset : Nat) :
    List Nat → Nat → (Nat → Core.Uint256)
  | _, 0 => mem
  | [], _ => mem
  | w :: rest, n + 1 =>
      writeMemoryWords
        (fun o => if o = offset then (w : Core.Uint256) else mem o)
        (offset + 1) rest n

def identityAdversary : AdversaryModel where
  stateTransition := fun _ w => w
  result := fun _ _ => .success []
  gasUsed := fun _ _ => 0

def echoAdversary : AdversaryModel where
  stateTransition := fun _ w => w
  result := fun site _ => .success site.calldata
  gasUsed := fun _ _ => 0

/-- Payable-call frame: `withTransactionContext` plus `selfBalance`
    credited by `msg.value`. The base helper is left unchanged. -/
def withPayableCallContext (world : ContractState) (tx : DenoteTransaction) :
    ContractState :=
  let framed := withTransactionContext world tx
  { framed with selfBalance := framed.selfBalance + tx.msgValue }

theorem selfBalance_withPayableCallContext
    (world : ContractState) (tx : DenoteTransaction) :
    (withPayableCallContext world tx).selfBalance =
      world.selfBalance + tx.msgValue :=
  rfl

/-- Debit `value` from `selfBalance` when the account can pay. -/
def debitSelfBalance (w : ContractState) (value : Nat) : Option ContractState :=
  if value ≤ w.selfBalance.val then
    some { w with selfBalance := w.selfBalance - (value : Core.Uint256) }
  else
    none

/-- Successful `call` commits the adversary transition, journals, debits
    ETH, and writes returndata into memory. Failure / revert keeps the
    pre-call balance and still journals. -/
def applyRawCall (env : CallEnv) (state : DenoteState) (site : CallSite)
    (outOff outSize : Nat) : Option (Nat × DenoteState) :=
  match site.kind with
  | .call =>
      match debitSelfBalance state.world site.value with
      | none => some (0, state)
      | some paid =>
          let obs := denoteCallJournaled env.adversary site
            { world := paid, gasRemaining := site.gas }
          match obs.result with
          | .success data =>
              let mem := writeMemoryWords obs.state.world.memory outOff data outSize
              some (1, { state with world := { obs.state.world with memory := mem } })
          | .failure _ | .revert _ =>
              some (0, { state with
                world := { state.world with
                  calls := state.world.calls ++
                    [journalEntry site obs.result] } })
  | .staticcall | .delegatecall =>
      let obs := denoteCallJournaled env.adversary site
        { world := state.world, gasRemaining := site.gas }
      match obs.result with
      | .success data =>
          let mem := writeMemoryWords obs.state.world.memory outOff data outSize
          some (1, { state with world := { obs.state.world with memory := mem } })
      | .failure _ | .revert _ =>
          some (0, { state with
            world := { state.world with
              calls := state.world.calls ++
                [journalEntry site obs.result] } })

/-- Denote `Expr.call` / `staticcall` / `delegatecall`. Returns the EVM
    success bit and the post-call state. Other expressions stay
    observationally silent (same as `evalExpr`). -/
def evalExprCall (env : CallEnv) (fields : List Field) (state : DenoteState) :
    Expr → Option (Nat × DenoteState)
  | .call gas target value inOff inSize outOff outSize => do
      let g ← evalExpr env.oracle fields state gas
      let t ← evalExpr env.oracle fields state target
      let v ← evalExpr env.oracle fields state value
      let io ← evalExpr env.oracle fields state inOff
      let isz ← evalExpr env.oracle fields state inSize
      let oo ← evalExpr env.oracle fields state outOff
      let osz ← evalExpr env.oracle fields state outSize
      let site : CallSite :=
        { siteId := t, kind := .call, target := t, value := v
          calldata := readMemoryWords state.world.memory io isz, gas := g }
      applyRawCall env state site oo osz
  | .staticcall gas target inOff inSize outOff outSize => do
      let g ← evalExpr env.oracle fields state gas
      let t ← evalExpr env.oracle fields state target
      let io ← evalExpr env.oracle fields state inOff
      let isz ← evalExpr env.oracle fields state inSize
      let oo ← evalExpr env.oracle fields state outOff
      let osz ← evalExpr env.oracle fields state outSize
      let site : CallSite :=
        { siteId := t, kind := .staticcall, target := t, value := 0
          calldata := readMemoryWords state.world.memory io isz, gas := g }
      applyRawCall env state site oo osz
  | .delegatecall gas target inOff inSize outOff outSize => do
      let g ← evalExpr env.oracle fields state gas
      let t ← evalExpr env.oracle fields state target
      let io ← evalExpr env.oracle fields state inOff
      let isz ← evalExpr env.oracle fields state inSize
      let oo ← evalExpr env.oracle fields state outOff
      let osz ← evalExpr env.oracle fields state outSize
      let site : CallSite :=
        { siteId := t, kind := .delegatecall, target := t, value := 0
          calldata := readMemoryWords state.world.memory io isz, gas := g }
      applyRawCall env state site oo osz
  | e =>
      (evalExpr env.oracle fields state e).map (fun n => (n, state))

def bindResultWords (bindings : Env) : List String → List Nat → Env
  | [], _ => bindings
  | _ :: _, [] => bindings
  | name :: names, w :: ws =>
      bindResultWords (bindValue bindings name (wordNormalize w)) names ws

/-- `Stmt.externalCallBind`: named linked call with resolved target and
    value. Auto-reverts on failure or missing link, matching the AST
    comment. -/
def execExternalCallBind (env : CallEnv) (fields : List Field)
    (state : DenoteState) (resultVars : List String) (externalName : String)
    (args : List Expr) : StmtOutcome :=
  match env.resolve externalName, evalExprList env.oracle fields state args with
  | some link, some argWords =>
      match debitSelfBalance state.world link.value with
      | none => .revert
      | some paid =>
          let site : CallSite :=
            { siteId := link.siteId, kind := .call, target := link.target
              value := link.value, calldata := argWords, gas := paid.selfBalance.val }
          let obs := denoteCallJournaled env.adversary site
            { world := paid, gasRemaining := site.gas }
          match obs.result with
          | .success data =>
              if data.length < resultVars.length then .revert
              else
                .continue
                  { state with
                    world := obs.state.world
                    bindings := bindResultWords state.bindings resultVars data }
          | .failure _ | .revert _ => .revert
  | _, _ => .revert

/-- `Stmt.tryExternalCallBind`: same call, but binds a success flag
    instead of reverting. -/
def execTryExternalCallBind (env : CallEnv) (fields : List Field)
    (state : DenoteState) (successVar : String) (resultVars : List String)
    (externalName : String) (args : List Expr) : StmtOutcome :=
  match env.resolve externalName, evalExprList env.oracle fields state args with
  | some link, some argWords =>
      match debitSelfBalance state.world link.value with
      | none =>
          .continue
            { state with
              bindings := bindValue state.bindings successVar 0 }
      | some paid =>
          let site : CallSite :=
            { siteId := link.siteId, kind := .call, target := link.target
              value := link.value, calldata := argWords, gas := paid.selfBalance.val }
          let obs := denoteCallJournaled env.adversary site
            { world := paid, gasRemaining := site.gas }
          match obs.result with
          | .success data =>
              .continue
                { state with
                  world := obs.state.world
                  bindings :=
                    bindResultWords
                      (bindValue state.bindings successVar 1) resultVars data }
          | .failure _ | .revert _ =>
              .continue
                { state with
                  world :=
                    { state.world with
                      calls := state.world.calls ++
                        [journalEntry site obs.result] }
                  bindings := bindValue state.bindings successVar 0 }
  | _, _ =>
      .continue { state with bindings := bindValue state.bindings successVar 0 }

mutual
  def execStmtWithCalls (env : CallEnv) (fields : List Field) :
      DenoteState → Stmt → StmtOutcome
    | state, .externalCallBind resultVars name args =>
        execExternalCallBind env fields state resultVars name args
    | state, .tryExternalCallBind successVar resultVars name args =>
        execTryExternalCallBind env fields state successVar resultVars name args
    | state, .ite cond thenBranch elseBranch =>
        match evalExpr env.oracle fields state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtListWithCalls env fields state thenBranch
            else
              execStmtListWithCalls env fields state elseBranch
        | none => .revert
    | state, .forEach varName count body =>
        match evalExpr env.oracle fields state count with
        | some bound =>
            let initialLoopState :=
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtListWithCalls env fields loopState body)
              initialLoopState 0 bound
        | none => .revert
    | state, .forEachSetBit varName bitmap body =>
        match evalExpr env.oracle fields state bitmap with
        | some bits =>
            execForEachSetBitLoop varName
              (fun loopState => execStmtListWithCalls env fields loopState body)
              256 state bits
        | none => .revert
    | state, other =>
        execStmt env.oracle fields state other

  def execStmtListWithCalls (env : CallEnv) (fields : List Field) :
      DenoteState → List Stmt → StmtOutcome
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmtWithCalls env fields state stmt with
        | .continue next => execStmtListWithCalls env fields next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
end

/-- Execution-level result retained for composition into an explicit callee
frame.  Unlike `DenoteResult`, this keeps the actual post-world. -/
structure FunctionExecution where
  result : ExternalCallResult
  world : ContractState

/-- Execute a FunctionSpec with raw / linked calls in-fragment. -/
def executeFunctionWithCalls (env : CallEnv) (spec : CompilationModel)
    (fn : FunctionSpec) (tx : DenoteTransaction) (initialWorld : ContractState) :
    FunctionExecution :=
  let worldWithTx := withPayableCallContext initialWorld tx
  let fields := effectiveFields spec
  match bindExternalParams tx.functionSelector fn.params tx.args with
  | none => { result := .revert [], world := worldWithTx }
  | some bindings =>
      match execStmtListWithCalls env fields
          { world := worldWithTx, bindings := bindings, selector := tx.functionSelector }
          fn.body with
      | .continue state | .stop state =>
          { result := .success [], world := state.world }
      | .return value state =>
          { result := .success [value], world := state.world }
      | .revert => { result := .revert [], world := worldWithTx }

/-- Canonical FunctionSpec denotation, projected from the composable
execution result so the two semantics cannot drift. -/
def denoteFunctionWithCalls (env : CallEnv) (spec : CompilationModel)
    (fn : FunctionSpec) (tx : DenoteTransaction) (initialWorld : ContractState) :
    DenoteResult :=
  let execution := executeFunctionWithCalls env spec fn tx initialWorld
  match execution.result with
  | .success [] => successResult env.oracle spec execution.world none
  | .success (word :: _) => successResult env.oracle spec execution.world (some word)
  | .failure _ | .revert _ => revertedResult env.oracle spec execution.world

/-- Adapt a source-shaped FunctionSpec execution to the official framed
multi-contract boundary.  The frame's pre-credit callee snapshot is supplied
to the function denotation; `msg.value` is credited exactly once by its
payable transaction context. -/
def runFunctionInFrame (env : CallEnv) (spec : CompilationModel)
    (fn : FunctionSpec) (selector : Nat)
    (frame : Verity.MultiContract.CallFrame) :
    Verity.MultiContract.CalleeExecution :=
  let execution := executeFunctionWithCalls env spec fn
    { sender := frame.caller.toNat
      msgValue := frame.site.value
      thisAddress := frame.callee.toNat
      functionSelector := selector
      args := frame.site.calldata }
    frame.calleeBefore
  { result := execution.result, post := execution.world }

/-- Official source-shaped multi-contract call path.  Frame construction,
FunctionSpec execution, value transfer, commit/rollback, returndata, and the
call journal are composed here; callers cannot supply an observed result or
post-state independently of the executed function. -/
def callFunction (env : CallEnv) (spec : CompilationModel)
    (fn : FunctionSpec) (selector : Nat) (world : Verity.MultiContract.MultiWorld)
    (caller callee : Address) (site : CallSite) :
    Option Verity.MultiContract.FramedCallObservation :=
  Verity.MultiContract.call world caller callee site
    (runFunctionInFrame env spec fn selector)

theorem callFunction_eq (env : CallEnv) (spec : CompilationModel)
    (fn : FunctionSpec) (selector : Nat) (world : Verity.MultiContract.MultiWorld)
    (caller callee : Address) (site : CallSite) :
    callFunction env spec fn selector world caller callee site = (do
      let frame ← Verity.MultiContract.callEntry world caller callee site
      some (Verity.MultiContract.executeCall world frame
        (runFunctionInFrame env spec fn selector))) :=
  rfl

/-! ## Atomic compiled multi-call transactions -/

/-- One call in a transaction program.  Unlike `CalleeExecution`, the result
and post-state are not inputs: they are computed from this `FunctionSpec` by
`callFunction`. -/
structure CompiledCall where
  env : CallEnv
  spec : CompilationModel
  fn : FunctionSpec
  selector : Nat
  caller : Address
  callee : Address
  site : CallSite

inductive TransactionControl where
  | success
  | invalidCall (index : Nat)
  | callFailed (index : Nat) (result : ExternalCallResult)
  deriving Repr

structure TransactionExecution where
  control : TransactionControl
  world : Verity.MultiContract.MultiWorld
  calls : List Verity.MultiContract.FramedCallObservation

/-- Execute a finite sequence of compiled calls in one shared world.  Every
successful call commits into the input of the next call.  An invalid frame,
failure, or revert restores the transaction-entry world, including all
callee state and ETH balances committed by earlier calls. -/
def denoteTransactionFrom (before current : Verity.MultiContract.MultiWorld) :
    Nat → List CompiledCall →
      List Verity.MultiContract.FramedCallObservation → TransactionExecution
  | _, [], observations =>
      { control := .success, world := current, calls := observations.reverse }
  | index, c :: rest, observations =>
      match callFunction c.env c.spec c.fn c.selector current
          c.caller c.callee c.site with
      | none =>
          { control := .invalidCall index, world := before,
            calls := observations.reverse }
      | some observation =>
          if observation.result.succeeded then
            denoteTransactionFrom before observation.world (index + 1) rest
              (observation :: observations)
          else
            { control := .callFailed index observation.result, world := before,
              calls := (observation :: observations).reverse }

def denoteTransaction (before : Verity.MultiContract.MultiWorld)
    (program : List CompiledCall) : TransactionExecution :=
  denoteTransactionFrom before before 0 program []

theorem denoteTransaction_nil (before : Verity.MultiContract.MultiWorld) :
    (denoteTransaction before []).world = before :=
  rfl

theorem denoteTransaction_invalid_first_rolls_back
    (before : Verity.MultiContract.MultiWorld) (c : CompiledCall)
    (h : callFunction c.env c.spec c.fn c.selector before
      c.caller c.callee c.site = none) :
    (denoteTransaction before [c]).world = before := by
  simp [denoteTransaction, denoteTransactionFrom, h]

/-! ## Laws -/

theorem debitSelfBalance_none_of_lt (w : ContractState) (value : Nat)
    (h : w.selfBalance.val < value) :
    debitSelfBalance w value = none := by
  simp [debitSelfBalance, Nat.not_le_of_gt h]

theorem debitSelfBalance_some (w : ContractState) (value : Nat)
    (h : value ≤ w.selfBalance.val) :
    debitSelfBalance w value =
      some { w with selfBalance := w.selfBalance - (value : Core.Uint256) } := by
  simp [debitSelfBalance, h]

theorem evalExpr_call_still_none (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState)
    (g t v io isz oo osz : Expr) :
    evalExpr oracle fields state (.call g t v io isz oo osz) = none :=
  rfl

theorem execStmt_externalCallBind_args_none (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState)
    (vars : List String) (name : String) (args : List Expr)
    (h : evalExprList oracle fields state args = none) :
    execStmt oracle fields state (.externalCallBind vars name args) = .revert := by
  simp [execStmt, h]

theorem execStmt_externalCallBind_call_fails (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState)
    (vars : List String) (name : String) (args : List Expr) (vals : List Nat)
    (hargs : evalExprList oracle fields state args = some vals)
    (hfail : state.externalCallSucceeded state.externalCallIndex = false) :
    execStmt oracle fields state (.externalCallBind vars name args) = .revert := by
  simp [execStmt, hargs, hfail]

/-- A successful source-level external call advances the oracle receipt and
    binds its returned words.  This pins the widened denotation to the exact
    receipt consumed by `SourceSemantics`. -/
theorem execStmt_externalCallBind_call_succeeds (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState)
    (vars : List String) (name : String) (args : List Expr) (vals : List Nat)
    (hargs : evalExprList oracle fields state args = some vals)
    (hsuccess : state.externalCallSucceeded state.externalCallIndex = true)
    (harity : ¬ (state.externalCallReturnValues state.externalCallIndex).length != vars.length) :
    execStmt oracle fields state (.externalCallBind vars name args) =
      .continue
        { state with
          world := (state.externalCallPostWorld state.externalCallIndex).getD state.world
          bindings := bindValues state.bindings vars
            ((state.externalCallReturnValues state.externalCallIndex).map wordNormalize)
          externalCallIndex := state.externalCallIndex + 1 } := by
  simp [execStmt, hargs, hsuccess, harity]

private def dummyOracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0
    keccakMemorySlice := fun _ _ _ => 0 }

theorem evalExpr_call_outside_base_fragment :
    evalExpr dummyOracle []
      { world := defaultState, bindings := [] }
      (.call (.literal 0) (.literal 1) (.literal 0)
        (.literal 0) (.literal 0) (.literal 0) (.literal 0)) = none :=
  rfl

theorem execStmt_externalCallBind_outside_base_fragment :
    execStmt dummyOracle []
      { world := defaultState, bindings := [] }
      (.externalCallBind ["r"] "echo" [.literal 42]) = .revert := by
  rfl

end Compiler.CompilationModel.DenoteFunctionCalls
