import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.CreationIRDispatch

/-! Effectful IR expression/statement execution. Each creation consumes an
actual opcode-entry context supplied by the native caller executor. A returned
post-opcode gas value is not reused as the entry gas of another opcode. This
module does not authenticate the supplied schedule or meter ordinary builtins;
those remain native execution/agreement obligations before Solidity admission.
Legacy pure IR definitions and their universal compatibility proofs stay intact.
-/
namespace Compiler.Proofs.IRGeneration.IRCreationInterpreter
open Compiler.Yul Verity.Core.Model

structure Runtime where
  state : IRState
  creationContexts : List ExecutionContext

/-- One actual boundary, not a fabricated schedule for a whole function. -/
def ofBoundary (state : IRState) : Runtime :=
  { state, creationContexts := state.executionContext.toList }

inductive Outcome (α : Type) where
  | value (result : α) (runtime : Runtime)
  | stop (runtime : Runtime)
  | revert (data : List UInt8) (runtime : Runtime)
  | interpretationError (message : String)
  | exceptional (runtime : Runtime)

def Outcome.bind (result : Outcome α) (next : α → Runtime → Outcome β) : Outcome β :=
  match result with
  | .value resolved runtime => next resolved runtime
  | .stop runtime => .stop runtime
  | .revert data runtime => .revert data runtime
  | .interpretationError message => .interpretationError message
  | .exceptional runtime => .exceptional runtime

/-- Full primitive effects are carried through expression position. -/
def invokeCreate2 (runtime : Runtime) (args : List Nat) : Outcome Nat :=
  match runtime.creationContexts with
  | [] => .interpretationError "CREATE2 requires the next actual opcode-entry execution context"
  | context :: rest =>
      match CreationIRDispatch.dispatch { runtime.state with executionContext := some context } args with
      | .error message => .interpretationError message
      | .ok (.exceptional (_, state)) =>
          .exceptional { state, creationContexts := rest }
      | .ok (.continued (address, state)) =>
          .value address { state, creationContexts := rest }

/-- Physical word stores retain canonical account and schedule effects. Gas
charging belongs to the authenticated native prefix, not evaluation fuel. -/
def invokeMstore (runtime : Runtime) (args : List Nat) : Outcome Unit :=
  match args with
  | [offset, value] => .value () { runtime with state := (runtime.state.writePhysicalMemoryValue
        (offset % Compiler.Constants.evmModulus) value) }
  | _ => .interpretationError "effectful IR mstore requires exactly two operands"

/-- EVM mstore8 writes the low byte and expands physical memory to words. -/
def invokeMstore8 (runtime : Runtime) (args : List Nat) : Outcome Unit :=
  match args with
  | [offset, value] => .value () { runtime with state := (runtime.state.installPhysicalMemory
        (runtime.state.byteMemory.writeByte (offset % Compiler.Constants.evmModulus)
          ⟨value % 256, Nat.mod_lt _ (by decide)⟩)) }
  | _ => .interpretationError "effectful IR mstore8 requires exactly two operands"

/-- Copy exact bytes within the real whole-word returndata carrier. Bounds
failure needs the actual opcode context to retain the exceptional gas state;
unknown context is a refusal, not a fabricated EVM revert. This staged operation
does not authenticate context or meter successful copy/memory expansion. -/
def invokeReturndatacopy (runtime : Runtime) (args : List Nat) : Outcome Unit :=
  match args with
  | [destination, source, extent] =>
      let destination := destination % Compiler.Constants.evmModulus
      let source := source % Compiler.Constants.evmModulus
      let extent := extent % Compiler.Constants.evmModulus
      if source + extent ≤ 32 * runtime.state.returndata.length then
        .value () { runtime with state := runtime.state.copyPhysicalReturndata destination source extent }
      else
        match runtime.state.executionContext with
        | none => .interpretationError "effectful IR returndata copy exceptional exit requires actual opcode context"
        | some context =>
            .exceptional { runtime with state := { runtime.state with
              executionContext := some { context with opcode := { context.opcode with gas := 0 } } } }
  | _ => .interpretationError "effectful IR returndatacopy requires exactly three operands"

/-- A REVERT observes actual physical memory and retains its computed bytes.
This is distinct from refusal and exceptional halt. Native execution must still
establish opcode gas/memory admission before whole-function correspondence. -/
def invokeRevert (runtime : Runtime) (args : List Nat) : Outcome Unit :=
  match args with
  | [offset, size] =>
      let offset := offset % Compiler.Constants.evmModulus
      let size := size % Compiler.Constants.evmModulus
      let state := runtime.state.captureRevert offset size
      .revert ((List.range size).map (fun index =>
        UInt8.ofNat (state.byteMemory.readByte (offset + index)).val))
        { runtime with state := state }
  | _ => .interpretationError "effectful IR revert requires exactly two operands"

/-- Read-only builtins use the existing native-backed scalar interpretation.
Unknown or malformed calls fail interpretation, never become an EVM revert. -/
def invoke (runtime : Runtime) (name : String) (args : List Nat) : Outcome Nat :=
  if name = "create2" then invokeCreate2 runtime args
  else
    match evalIRCall runtime.state name (args.map YulExpr.lit) with
    | some value => .value value runtime
    | none => .interpretationError s!"unsupported effectful IR builtin or arity: {name}"

mutual
/-- Resource fuel is a bound on model evaluation, not opcode gas. -/
def evalExpr : Nat → Runtime → YulExpr → Outcome Nat
  | 0, _, _ => .interpretationError "effectful IR expression fuel exhausted"
  | fuel + 1, runtime, expr =>
      match expr with
      | .lit value | .hex value => .value value runtime
      | .str _ => .interpretationError "effectful IR string expressions are unsupported"
      | .ident name =>
          match runtime.state.getVar name with
          | some value => .value value runtime
          | none => .interpretationError s!"unbound effectful IR variable: {name}"
      | .call name args =>
          (evalArgs fuel runtime args).bind (fun values next => invoke next name values)

/-- Yul evaluates call arguments right-to-left, retaining their source-order
positions in the resulting list. Each argument threads all creation effects. -/
def evalArgs : Nat → Runtime → List YulExpr → Outcome (List Nat)
  | _, runtime, [] => .value [] runtime
  | 0, _, _ :: _ => .interpretationError "effectful IR argument fuel exhausted"
  | fuel + 1, runtime, expr :: rest =>
      (evalArgs fuel runtime rest).bind (fun tail afterTail =>
        (evalExpr fuel afterTail expr).bind (fun head afterHead =>
          .value (head :: tail) afterHead))
end

/-- Compiler-generated Yul never shadows an accessible binding. Reject a
near miss rather than silently overwrite an outer local. -/
def declare (runtime : Runtime) (name : String) (value : Nat) : Outcome Unit :=
  match runtime.state.getVar name with
  | some _ => .interpretationError s!"effectful IR variable already declared: {name}"
  | none => .value () { runtime with state := runtime.state.setVar name value }

def assign (runtime : Runtime) (name : String) (value : Nat) : Outcome Unit :=
  match runtime.state.getVar name with
  | none => .interpretationError s!"assignment to unbound effectful IR variable: {name}"
  | some _ => .value () { runtime with state := runtime.state.setVar name value }

/-- Drop block-local declarations while preserving assignments to outer
bindings and every world/context effect. Shadowing is explicitly refused. -/
def closeScope (outer : IRState) (result : Outcome Unit) : Outcome Unit :=
  match result with
  | .value _ runtime => .value () { runtime with state :=
      { runtime.state with vars := runtime.state.vars.filter (fun binding =>
          outer.vars.any (fun prior => prior.1 == binding.1)) } }
  | .stop runtime => .stop runtime
  | .revert data runtime => .revert data runtime
  | .interpretationError message => .interpretationError message
  | .exceptional runtime => .exceptional runtime

mutual
/-- Effectful statement traversal; unsupported helper definitions, leave and
void/effectful builtins fail precisely until their semantics are integrated. -/
def execStmt : Nat → Runtime → YulStmt → Outcome Unit
  | 0, _, _ => .interpretationError "effectful IR statement fuel exhausted"
  | fuel + 1, runtime, stmt =>
      match stmt with
      | .comment _ => .value () runtime
      | .let_ name value =>
          (evalExpr fuel runtime value).bind (fun value next => declare next name value)
      | .assign name value =>
          (evalExpr fuel runtime value).bind (fun value next => assign next name value)
      | .letMany [name] value =>
          (evalExpr fuel runtime value).bind (fun value next => declare next name value)
      | .letMany _ _ => .interpretationError "effectful IR multi-value helper calls are unsupported"
      | .exprStmt (.call "stop" []) => .stop runtime
      | .exprStmt (.call "mstore" args) =>
          (evalArgs fuel runtime args).bind (fun values next => invokeMstore next values)
      | .exprStmt (.call "mstore8" args) =>
          (evalArgs fuel runtime args).bind (fun values next => invokeMstore8 next values)
      | .exprStmt (.call "returndatacopy" args) =>
          (evalArgs fuel runtime args).bind (fun values next => invokeReturndatacopy next values)
      | .exprStmt (.call "revert" args) =>
          (evalArgs fuel runtime args).bind (fun values next => invokeRevert next values)
      | .exprStmt expr => (evalExpr fuel runtime expr).bind (fun _ next => .value () next)
      | .if_ cond body =>
          (evalExpr fuel runtime cond).bind (fun value next =>
            if value = 0 then .value () next
            else closeScope next.state (execStmts fuel next body))
      | .switch expr cases defaultBody =>
          (evalExpr fuel runtime expr).bind (fun value next =>
            match cases.find? (fun entry => entry.1 == value) with
            | some (_, body) => closeScope next.state (execStmts fuel next body)
            | none => match defaultBody with
              | some body => closeScope next.state (execStmts fuel next body)
              | none => .value () next)
      | .block body => closeScope runtime.state (execStmts fuel runtime body)
      | .for_ init cond post body =>
          closeScope runtime.state
            ((execStmts fuel runtime init).bind (fun _ next => execLoop fuel next cond post body))
      | .leave => .interpretationError "effectful IR leave requires an internal helper frame"
      | .funcDef _ _ _ _ => .interpretationError "effectful IR helper definitions are unsupported"

def execStmts : Nat → Runtime → List YulStmt → Outcome Unit
  | _, runtime, [] => .value () runtime
  | 0, _, _ :: _ => .interpretationError "effectful IR statement-list fuel exhausted"
  | fuel + 1, runtime, stmt :: rest =>
      (execStmt fuel runtime stmt).bind (fun _ next => execStmts fuel next rest)

def execLoop : Nat → Runtime → YulExpr → List YulStmt → List YulStmt → Outcome Unit
  | 0, _, _, _, _ => .interpretationError "effectful IR loop fuel exhausted"
  | fuel + 1, runtime, cond, post, body =>
      (evalExpr fuel runtime cond).bind (fun value next =>
        if value = 0 then .value () next
        else (closeScope next.state (execStmts fuel next body)).bind (fun _ afterBody =>
          (closeScope afterBody.state (execStmts fuel afterBody post)).bind (fun _ afterPost =>
            execLoop fuel afterPost cond post body)))
end

theorem invokeMstore_two (runtime : Runtime) (offset value : Nat) :
    invokeMstore runtime [offset, value] = .value ()
      { runtime with state := (runtime.state.writePhysicalMemoryValue
        (offset % Compiler.Constants.evmModulus) value) } := rfl

theorem invokeMstore8_two (runtime : Runtime) (offset value : Nat) :
    invokeMstore8 runtime [offset, value] = .value ()
      { runtime with state := (runtime.state.installPhysicalMemory
        (runtime.state.byteMemory.writeByte (offset % Compiler.Constants.evmModulus)
          ⟨value % 256, Nat.mod_lt _ (by decide)⟩)) } := rfl

theorem invokeCreate2_no_context (state : IRState) (args : List Nat) :
    invokeCreate2 { state, creationContexts := [] } args =
      .interpretationError "CREATE2 requires the next actual opcode-entry execution context" := rfl

theorem evalExpr_literal (fuel value : Nat) (runtime : Runtime) :
    evalExpr (fuel + 1) runtime (.lit value) = .value value runtime := rfl

theorem evalArgs_nil (fuel : Nat) (runtime : Runtime) :
    evalArgs fuel runtime [] = .value [] runtime := by
  cases fuel <;> rfl

theorem execStmt_let (fuel : Nat) (runtime : Runtime) (name : String) (expr : YulExpr) :
    execStmt (fuel + 1) runtime (.let_ name expr) =
      (evalExpr fuel runtime expr).bind (fun value next => declare next name value) := rfl

theorem execStmts_interpretationError (fuel : Nat) (runtime : Runtime)
    (stmt : YulStmt) (rest : List YulStmt) (message : String)
    (failed : execStmt fuel runtime stmt = .interpretationError message) :
    execStmts (fuel + 1) runtime (stmt :: rest) = .interpretationError message := by
  simp only [execStmts, failed, Outcome.bind]

theorem execStmts_exceptional (fuel : Nat) (runtime next : Runtime)
    (stmt : YulStmt) (rest : List YulStmt)
    (failed : execStmt fuel runtime stmt = .exceptional next) :
    execStmts (fuel + 1) runtime (stmt :: rest) = .exceptional next := by
  simp only [execStmts, failed, Outcome.bind]

/-- Exact byteful terminal outcomes skip every following statement. -/
theorem execStmts_revert (fuel : Nat) (runtime next : Runtime)
    (stmt : YulStmt) (rest : List YulStmt) (data : List UInt8)
    (failed : execStmt fuel runtime stmt = .revert data next) :
    execStmts (fuel + 1) runtime (stmt :: rest) = .revert data next := by
  simp only [execStmts, failed, Outcome.bind]

/-- The outcome payload is precisely the slice recorded by actual REVERT. -/
theorem invokeRevert_payload (runtime : Runtime) (offset size : Nat) :
    ∃ data next, invokeRevert runtime [offset, size] = .revert data next ∧
      next.state.revertBytes = some data := by
  refine ⟨_, _, rfl, ?_⟩
  rfl

/-- Exhausting a copy leaves physical memory and the supplied creation schedule
untouched while exhausting the actual context's gas. -/
theorem invokeReturndatacopy_exceptional (runtime : Runtime) (destination source extent : Nat)
    (context : ExecutionContext)
    (present : runtime.state.executionContext = some context)
    (outside : 32 * runtime.state.returndata.length <
      source % Compiler.Constants.evmModulus + extent % Compiler.Constants.evmModulus) :
    invokeReturndatacopy runtime [destination, source, extent] =
      .exceptional { runtime with state := { runtime.state with
        executionContext := some { context with opcode := { context.opcode with gas := 0 } } } } := by
  simp only [invokeReturndatacopy, Nat.not_le.mpr outside, if_false, present]

end Compiler.Proofs.IRGeneration.IRCreationInterpreter
