import Compiler.SolidityImport.Transactions

/-! Access instrumentation for scalar and mapping Denote bodies. Unsupported
forms fail before they can be reported as observed. Execution itself always
uses `Denote.execStmt`; this module does not reimplement arithmetic or writes. -/
namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote Verity.Core

private def fieldKey (field : Field) (slot : Nat) : Verity.StorageKey :=
  if field.isTransient then .transient (wordNormalize slot) else .slot (wordNormalize slot)

private def mappingMemberKeys (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name memberName : String) (keys : List Expr)
    (writing : Bool) : Except String (List Verity.StorageKey) := do
  let some (field, slot) := findFieldWithResolvedSlot fields name
    | throw s!"unknown observed mapping {name}"
  let some members := findStructMembers fields name
    | throw s!"observed mapping {name} has no member layout"
  let some member := findStructMember members memberName
    | throw s!"unknown observed mapping member {name}.{memberName}"
  let values ← keys.mapM fun key => do
    let some value := evalExpr oracle fields state key
      | throw "mapping observation could not evaluate a key"
    pure value
  let slots ← if writing then do
      let some slots := findFieldWriteSlots fields name
        | throw s!"unknown observed mapping write slots for {name}"
      pure slots
    else pure [slot]
  return slots.map fun base =>
    fieldKey field (values.foldl oracle.mappingSlot base + member.wordOffset)

def expressionAccesses (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) : Expr → Except String (List Verity.StorageKey)
  | .literal _ | .param _ | .localVar _ => .ok []
  | .caller | .contractAddress | .blockTimestamp | .blockNumber | .chainid => .ok []
  | .storage name => do
      let some (field, slot) := findFieldWithResolvedSlot fields name
        | throw s!"unknown observed field {name}"
      return [fieldKey field slot]
  | .add left right | .sub left right | .mul left right | .div left right
  | .bitAnd left right | .bitXor left right | .eq left right | .lt left right
  | .gt left right | .le left right | .ge left right => do
      return (← expressionAccesses oracle fields state left) ++ (← expressionAccesses oracle fields state right)
  | .logicalNot value => expressionAccesses oracle fields state value
  | .structMember name key member => do
      let reads ← expressionAccesses oracle fields state key
      return reads ++ (← mappingMemberKeys oracle fields state name member [key] false)
  | .structMember2 name key1 key2 member => do
      let reads1 ← expressionAccesses oracle fields state key1
      let reads2 ← expressionAccesses oracle fields state key2
      return reads1 ++ reads2 ++ (← mappingMemberKeys oracle fields state name member [key1, key2] false)
  | expression => .error s!"unsupported storage observation expression: {repr expression}"

def statementAccesses (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (statement : Stmt)
    (events : List EventDef := []) : Except String (List Verity.StorageKey) :=
  match statement with
  | .letVar _ value | .assignVar _ value | .return value | .panicCode value =>
      expressionAccesses oracle fields state value
  | .stop => pure []
  | .returnValues values => do
      return (← values.mapM (expressionAccesses oracle fields state)).flatten
  | .panic _ => .ok []
  | .emit name values => do
      let [definition] := events.filter (·.name == name)
        | throw s!"observed event must resolve uniquely: {name}"
      unless definition.params.length == values.length do throw "event argument count differs"
      unless definition.params.all (fun p => p.ty == .uint256) do
        throw "event observation currently requires uint256 parameters"
      unless (definition.params.filter (fun p => p.kind == .indexed)).length ≤ 3 do
        throw "event has more than three indexed parameters"
      return (← values.mapM (expressionAccesses oracle fields state)).flatten
  | .setStorage name value => do
      let reads ← expressionAccesses oracle fields state value
      let some (field, _) := findFieldWithResolvedSlot fields name
        | throw s!"unknown observed field {name}"
      let some slots := findFieldWriteSlots fields name
        | throw s!"unknown observed write slots for {name}"
      return reads ++ slots.map (fieldKey field)
  | .setStructMember name key member value => do
      let keyReads ← expressionAccesses oracle fields state key
      let valueReads ← expressionAccesses oracle fields state value
      return keyReads ++ valueReads ++ (← mappingMemberKeys oracle fields state name member [key] true)
  | .setStructMember2 name key1 key2 member value => do
      let keyReads1 ← expressionAccesses oracle fields state key1
      let keyReads2 ← expressionAccesses oracle fields state key2
      let valueReads ← expressionAccesses oracle fields state value
      return keyReads1 ++ keyReads2 ++ valueReads ++
        (← mappingMemberKeys oracle fields state name member [key1, key2] true)
  | statement => .error s!"unsupported storage observation statement: {repr statement}"

structure AccessResult where
  outcome : StmtOutcome
  touched : List Verity.StorageKey

mutual

/-- Error arguments are evaluated only on the failing Denote branch. Observe
that branch using the same evaluator, retaining condition reads in either case.
The accepted expressions remain the explicit scalar access subset above. -/
def observedStatementAccesses (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (statement : Stmt) (events : List EventDef) :
    Except String (List Verity.StorageKey) := do
  match statement with
  | .ite condition yes no => do
      let reads ← expressionAccesses oracle fields state condition
      match evalExpr oracle fields state condition with
      | none => throw "conditional observation could not evaluate the condition"
      | some value =>
          if value != 0 then
            return reads ++ (← observedBodyAccesses oracle fields state yes events)
          else
            return reads ++ (← observedBodyAccesses oracle fields state no events)
  | .require condition _ => expressionAccesses oracle fields state condition
  | .requireError condition _ arguments =>
      let reads ← expressionAccesses oracle fields state condition
      match evalExpr oracle fields state condition with
      | some 0 => return reads ++ (← arguments.mapM (expressionAccesses oracle fields state)).flatten
      | some _ | none => return reads
  | .revertError _ arguments =>
      return (← arguments.mapM (expressionAccesses oracle fields state)).flatten
  | _ => statementAccesses oracle fields state statement events

/-- Follow only executed statements, retaining accesses before a stop or revert.
State advancement uses the original Denote executor. -/
def observedBodyAccesses (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (body : List Stmt) (events : List EventDef) :
    Except String (List Verity.StorageKey) := do
  match body with
  | [] => return []
  | head :: tail =>
      let accesses ← observedStatementAccesses oracle fields state head events
      match execStmt oracle fields state head with
      | .continue next =>
          return accesses ++ (← observedBodyAccesses oracle fields next tail events)
      | _ => return accesses

end

/-- Keep accesses made before a revert, including writes rolled back later.
Only the continuation case executes another statement. -/
def traceStraightLine (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (body : List Stmt) (events : List EventDef := []) :
    Except String AccessResult :=
  match body with
  | [] => .ok ⟨.continue state, []⟩
  | statement :: rest => do
      let accesses ← observedStatementAccesses oracle fields state statement events
      let outcome := execStmt oracle fields state statement
      match outcome with
      | .continue next =>
          let result ← traceStraightLine oracle fields next rest events
          return ⟨result.outcome, accesses ++ result.touched⟩
      | stopped => return ⟨stopped, accesses⟩

structure TracedFrameResult where
  frame : FrameResult
  touched : List Verity.StorageKey

/-- Execute and retain accesses even when the frame rolls back. The returned
world is suitable as the persistent input to the next transaction. -/
def executeTracedBody (oracle : DenoteOracle) (fields : List Field)
    (world : Verity.ContractState) (bindings : Env) (body : List Stmt)
    (events : List EventDef := []) (errors : List ErrorDef := []) :
    Except String TracedFrameResult := do
  let initial := beginTransaction world
  let traced ← traceStraightLine oracle fields { world := initial, bindings, errors } body events
  let frame ← finishFrame initial traced.outcome
  return ⟨frame, traced.touched⟩

/-- A successful access trace preserves the complete Denote outcome, including
its final world and exact revert payload. No observable projection is erased. -/
theorem traceStraightLine_agrees (oracle : DenoteOracle) (fields : List Field)
    (events : List EventDef)
    (state : DenoteState) (body : List Stmt) (result : AccessResult)
    (h : traceStraightLine oracle fields state body events = .ok result) :
    result.outcome = execStmtList oracle fields state body := by
  induction body generalizing state result with
  | nil =>
      simp [traceStraightLine] at h
      cases h
      rfl
  | cons statement rest ih =>
      cases ha : observedStatementAccesses oracle fields state statement events with
      | error reason => simp [traceStraightLine, ha, bind, Except.bind] at h
      | ok accesses =>
          cases he : execStmt oracle fields state statement with
          | «continue» next =>
              cases hr : traceStraightLine oracle fields next rest events with
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
