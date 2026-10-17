import Compiler.Proofs.IRGeneration.SourceSemantics

/-! Typed source-expression effects. These primitives are the migration target,
not a preflight over the legacy Option evaluator. No new Solidity admission. -/
namespace Compiler.Proofs.IRGeneration.SourceExpressionOutcome
open Compiler.CompilationModel
open SourceSemantics

inductive Result (α : Type) where
  | value (value : α) (state : RuntimeState)
  | revert
  | revertWithData (data : List UInt8)
  | halt (state : RuntimeState)
  | interpretationError (message : String)
  | exceptional (state : RuntimeState)

def Result.bind (result : Result α) (next : α → RuntimeState → Result β) : Result β :=
  match result with
  | .value resolved state => next resolved state
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .halt state => .halt state
  | .interpretationError message => .interpretationError message
  | .exceptional state => .exceptional state

/-- A helper's locals do not escape. Its full world, opcode context and call
index do escape on successful return. Refusal and exceptional state stay typed. -/
def ofHelperBody (caller : RuntimeState) : StmtResult → Result Nat
  | .return value final => .value value { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }
  | .stop final =>
      match final.observedReturnWords with
      | none => .halt { final with bindings := caller.bindings }
      | some [value] =>
          let restored := { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }
          .value value restored
      | some _ => .interpretationError "expression helper returned non-scalar values"
  | .continue _ =>
      .interpretationError "expression helper completed without a scalar return"
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .interpretationError message => .interpretationError message
  | .exceptional final => .exceptional final

/-- Execute the helper body once with the actual caller context. The callback
is the typed statement executor; no Option projection of its result occurs. -/
def invoke (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (caller : RuntimeState)
    (name : String) (args : List Nat) : Result Nat :=
  match spec.functions.filter (fun fn => fn.isInternal && fn.name == name) with
  | [helper] =>
      match bindInternalArgs helper.params args with
      | none => .interpretationError s!"expression helper argument mismatch: {name}"
      | some bindings =>
          ofHelperBody caller (runBody { caller with bindings := bindings, observedReturnWords := none } helper.body)
  | _ => .interpretationError s!"expression helper is missing or ambiguous: {name}"

/-- Left-to-right source argument evaluation threads the computed state of
all preceding arguments. A terminal result prevents subsequent evaluation. -/
def evalList (eval : RuntimeState → Expr → Result Nat) :
    RuntimeState → List Expr → Result (List Nat)
  | state, [] => .value [] state
  | state, expr :: rest =>
      (eval state expr).bind (fun value next =>
        (evalList eval next rest).bind (fun values final => .value (value :: values) final))

/-- A real expression consumer, retaining every terminal outcome. -/
def assign (name : String) (result : Result Nat) : StmtResult :=
  match result with
  | .value value state => .continue { state with bindings := bindValue state.bindings name value }
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .halt state => .stop state
  | .interpretationError message => .interpretationError message
  | .exceptional state => .exceptional state

theorem bind_refusal (message : String) (next : α → RuntimeState → Result β) :
    Result.bind (.interpretationError message) next = .interpretationError message := rfl

theorem bind_exceptional (state : RuntimeState) (next : α → RuntimeState → Result β) :
    Result.bind (.exceptional state) next = .exceptional state := rfl

theorem helper_refusal (caller : RuntimeState) (message : String) :
    ofHelperBody caller (.interpretationError message) = .interpretationError message := rfl

theorem helper_exceptional (caller final : RuntimeState) :
    ofHelperBody caller (.exceptional final) = .exceptional final := rfl

theorem helper_return_world (caller final : RuntimeState) (value : Nat) :
    ofHelperBody caller (.return value final) =
      .value value { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords } := rfl

theorem assign_refusal (name message : String) :
    assign name (.interpretationError message) = .interpretationError message := rfl

end Compiler.Proofs.IRGeneration.SourceExpressionOutcome
