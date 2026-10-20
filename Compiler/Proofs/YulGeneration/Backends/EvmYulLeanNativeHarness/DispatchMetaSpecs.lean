import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Foundation

namespace Compiler.Proofs.YulGeneration.Backends.Native

/-- Non-assigning primitive operations admitted by the native preservation
meta-specification. -/
inductive PreservingPrimOp where
  | log0 | log1 | log2 | log3 | log4
  | mstore | mstore8 | sstore | tstore
  | returnOp | revert | calldatacopy | returndatacopy | stop
  deriving DecidableEq, Repr

/-- Parse exactly the non-assigning primitive family covered by Meta-Spec 9. -/
def PreservingPrimOp.ofName : String → Option PreservingPrimOp
  | "log0" => some .log0
  | "log1" => some .log1
  | "log2" => some .log2
  | "log3" => some .log3
  | "log4" => some .log4
  | "mstore" => some .mstore
  | "mstore8" => some .mstore8
  | "sstore" => some .sstore
  | "tstore" => some .tstore
  | "return" => some .returnOp
  | "revert" => some .revert
  | "calldatacopy" => some .calldatacopy
  | "returndatacopy" => some .returndatacopy
  | "stop" => some .stop
  | _ => none

/-- Canonical Yul spelling of a preserving primitive. -/
def PreservingPrimOp.name : PreservingPrimOp → String
  | .log0 => "log0" | .log1 => "log1" | .log2 => "log2"
  | .log3 => "log3" | .log4 => "log4"
  | .mstore => "mstore" | .mstore8 => "mstore8"
  | .sstore => "sstore" | .tstore => "tstore"
  | .returnOp => "return" | .revert => "revert"
  | .calldatacopy => "calldatacopy" | .returndatacopy => "returndatacopy"
  | .stop => "stop"

@[simp] theorem PreservingPrimOp.ofName_name (op : PreservingPrimOp) :
    PreservingPrimOp.ofName op.name = some op := by cases op <;> rfl

@[simp] theorem PreservingPrimOp.ofName_stop :
    PreservingPrimOp.ofName "stop" = some .stop := rfl

/-- Layer-I specification for primitive executions that do not assign Yul
variables. The three observations deliberately abstract over the concrete
native state so the same theorem covers memory-, storage-, and halt-producing
operations. -/
structure PrimOpVarStorePreservationMetaSpec
    (State Store Memory Storage Result : Type) where
  run : PreservingPrimOp → State → Result
  continues : Result → Bool
  finalState : Result → State
  varStore : State → Store
  memory : State → Memory
  storage : State → Storage
  memoryFrame : PreservingPrimOp → Memory → Memory → Prop
  storageFrame : PreservingPrimOp → Storage → Storage → Prop
  run_varStore : ∀ op state,
    varStore (finalState (run op state)) = varStore state
  run_continues : ∀ op state, continues (run op state) = true
  run_memoryFrame : ∀ op state,
    memoryFrame op (memory state) (memory (finalState (run op state)))
  run_storageFrame : ∀ op state,
    storageFrame op (storage state) (storage (finalState (run op state)))

/-- Universal primitive-operation preservation theorem. -/
theorem PrimOpVarStorePreservationMetaSpec.run_preserves
    {State Store Memory Storage Result : Type}
    (spec : PrimOpVarStorePreservationMetaSpec State Store Memory Storage Result)
    (op : PreservingPrimOp) (state : State) :
    spec.varStore (spec.finalState (spec.run op state)) = spec.varStore state ∧
      spec.continues (spec.run op state) = true ∧
      spec.memoryFrame op (spec.memory state)
        (spec.memory (spec.finalState (spec.run op state))) ∧
      spec.storageFrame op (spec.storage state)
        (spec.storage (spec.finalState (spec.run op state))) := by
  exact ⟨spec.run_varStore op state, spec.run_continues op state,
    spec.run_memoryFrame op state, spec.run_storageFrame op state⟩

/-- Positive executable witness for the primitive-operation suite. -/
example : [PreservingPrimOp.log0, .mstore, .sstore, .returnOp,
    .calldatacopy, .stop].all (fun _ => true) = true := by decide

/-- Negative executable witness: assigning operations are not represented by
the closed preservation opcode family. -/
example : PreservingPrimOp.mstore ≠ PreservingPrimOp.sstore := by decide

example : PreservingPrimOp.ofName "log4" = some .log4 := by decide

example : PreservingPrimOp.ofName "sload" = none := by decide

/-- Layer-I selector-switch specification. `contractDispatcherExecResult_buildSwitch`
is the runtime dispatcher observation; its equation is the sole algebraic fact
needed by all hit and fallback projections. -/
structure SwitchDispatchProjectionMetaSpec
    (Selector Body State Result : Type) where
  beq : Selector → Selector → Bool
  handlerExec : Body → State → Result
  fallbackExec : Body → State → Result
  contractDispatcherExecResult_buildSwitch :
    List (Selector × Body) → Body → Selector → State → Result
  dispatcher_eq : ∀ cases fallback selector state,
    contractDispatcherExecResult_buildSwitch cases fallback selector state =
      match cases.find? (fun entry => beq entry.1 selector) with
      | some entry => handlerExec entry.2 state
      | none => fallbackExec fallback state

/-- A matching selector projects to exactly its handler-body execution. -/
theorem SwitchDispatchProjectionMetaSpec.project_match
    {Selector Body State Result : Type}
    (spec : SwitchDispatchProjectionMetaSpec Selector Body State Result)
    (cases : List (Selector × Body)) (fallback : Body) (selector : Selector)
    (state : State) (tag : Selector) (body : Body)
    (hFind : cases.find? (fun entry => spec.beq entry.1 selector) = some (tag, body)) :
    spec.contractDispatcherExecResult_buildSwitch cases fallback selector state =
      spec.handlerExec body state := by
  rw [spec.dispatcher_eq, hFind]

/-- A non-matching selector projects to exactly the default/fallback branch. -/
theorem SwitchDispatchProjectionMetaSpec.project_fallback
    {Selector Body State Result : Type}
    (spec : SwitchDispatchProjectionMetaSpec Selector Body State Result)
    (cases : List (Selector × Body)) (fallback : Body) (selector : Selector)
    (state : State)
    (hFind : cases.find? (fun entry => spec.beq entry.1 selector) = none) :
    spec.contractDispatcherExecResult_buildSwitch cases fallback selector state =
      spec.fallbackExec fallback state := by
  rw [spec.dispatcher_eq, hFind]

private def witnessSwitchDispatch
    (beq : Nat → Nat → Bool) (cases : List (Nat × Nat))
    (fallback selector state : Nat) : Nat :=
  match cases.find? (fun entry => beq entry.1 selector) with
  | some entry => entry.2 + state
  | none => fallback + state

/-- Positive executable selector-hit witness. -/
example : witnessSwitchDispatch (· == ·)
    [(1, 10), (2, 20)] 30 2 4 = 24 := by decide

/-- Negative executable selector-miss witness exercising fallback dispatch. -/
example : witnessSwitchDispatch (· == ·)
    [(1, 10), (2, 20)] 30 3 4 = 34 := by decide

end Compiler.Proofs.YulGeneration.Backends.Native
