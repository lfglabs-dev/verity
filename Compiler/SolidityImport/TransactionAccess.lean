import Compiler.SolidityImport.Transactions

/-! Access instrumentation for straight-line scalar Denote bodies. Unsupported
forms fail before they can be reported as observed. Execution itself always
uses `Denote.execStmt`; this module does not reimplement arithmetic or writes. -/
namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote Verity.Core

private def fieldKey (field : Field) (slot : Nat) : Verity.StorageKey :=
  if field.isTransient then .transient (wordNormalize slot) else .slot (wordNormalize slot)

def expressionAccesses (fields : List Field) : Expr → Except String (List Verity.StorageKey)
  | .literal _ | .param _ | .localVar _ => .ok []
  | .storage name => do
      let some (field, slot) := findFieldWithResolvedSlot fields name
        | throw s!"unknown observed field {name}"
      return [fieldKey field slot]
  | expression => .error s!"unsupported storage observation expression: {repr expression}"

def statementAccesses (fields : List Field) : Stmt → Except String (List Verity.StorageKey)
  | .letVar _ value | .assignVar _ value | .return value | .panicCode value =>
      expressionAccesses fields value
  | .returnValues values => do
      return (← values.mapM (expressionAccesses fields)).flatten
  | .panic _ => .ok []
  | .setStorage name value => do
      let reads ← expressionAccesses fields value
      let some (field, _) := findFieldWithResolvedSlot fields name
        | throw s!"unknown observed field {name}"
      let some slots := findFieldWriteSlots fields name
        | throw s!"unknown observed write slots for {name}"
      return reads ++ slots.map (fieldKey field)
  | statement => .error s!"unsupported storage observation statement: {repr statement}"

structure AccessResult where
  outcome : StmtOutcome
  touched : List Verity.StorageKey

/-- Keep accesses made before a revert, including writes rolled back later.
Only the continuation case executes another statement. -/
def traceStraightLine (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) : List Stmt → Except String AccessResult
  | [] => .ok ⟨.continue state, []⟩
  | statement :: rest => do
      let accesses ← statementAccesses fields statement
      let outcome := execStmt oracle fields state statement
      match outcome with
      | .continue next =>
          let result ← traceStraightLine oracle fields next rest
          return ⟨result.outcome, accesses ++ result.touched⟩
      | stopped => return ⟨stopped, accesses⟩

structure TracedFrameResult where
  frame : FrameResult
  touched : List Verity.StorageKey

/-- Execute and retain accesses even when the frame rolls back. The returned
world is suitable as the persistent input to the next transaction. -/
def executeTracedBody (oracle : DenoteOracle) (fields : List Field)
    (world : Verity.ContractState) (bindings : Env) (body : List Stmt) :
    Except String TracedFrameResult := do
  let initial := beginTransaction world
  let traced ← traceStraightLine oracle fields { world := initial, bindings } body
  let frame ← finishFrame initial traced.outcome
  return ⟨frame, traced.touched⟩

/-- A successful access trace preserves the complete Denote outcome, including
its final world and exact revert payload. No observable projection is erased. -/
theorem traceStraightLine_agrees (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (body : List Stmt) (result : AccessResult)
    (h : traceStraightLine oracle fields state body = .ok result) :
    result.outcome = execStmtList oracle fields state body := by
  induction body generalizing state result with
  | nil =>
      simp [traceStraightLine] at h
      cases h
      rfl
  | cons statement rest ih =>
      cases ha : statementAccesses fields statement with
      | error reason => simp [traceStraightLine, ha, bind, Except.bind] at h
      | ok accesses =>
          cases he : execStmt oracle fields state statement with
          | «continue» next =>
              cases hr : traceStraightLine oracle fields next rest with
              | error reason => simp [traceStraightLine, ha, he, hr, bind, Except.bind] at h
              | ok tail =>
                  simp [traceStraightLine, ha, he, hr, bind, Except.bind, pure, Except.pure] at h
                  cases h
                  simpa [execStmtList, he] using ih next tail hr
          | stop final =>
              simp [traceStraightLine, ha, he, bind, Except.bind, pure, Except.pure] at h
              cases h
              simp [execStmtList, he]
          | «return» value final =>
              simp [traceStraightLine, ha, he, bind, Except.bind, pure, Except.pure] at h
              cases h
              simp [execStmtList, he]
          | revert =>
              simp [traceStraightLine, ha, he, bind, Except.bind, pure, Except.pure] at h
              cases h
              simp [execStmtList, he]
          | revertWithData bytes =>
              simp [traceStraightLine, ha, he, bind, Except.bind, pure, Except.pure] at h
              cases h
              simp [execStmtList, he]

end Compiler.CompilationModel.SolidityImport.Transactions
