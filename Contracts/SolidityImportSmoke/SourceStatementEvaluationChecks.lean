import Compiler.Proofs.IRGeneration.SourceExternalEvaluationLaws
import Compiler.Proofs.IRGeneration.DenoteTypedCreationAgreement
import Compiler.Proofs.IRGeneration.SourceHaltingLaws
import Compiler.Proofs.IRGeneration.SourceRevertTransport
namespace SolidityImportSmoke.SourceStatementEvaluationChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics SourceExpressionOutcome
private def refusalHelper : FunctionSpec :=
  { name := "refused", params := [], returnType := some .uint256, isInternal := true,
    body := [.create2 "created" (.literal 0) (.literal 0) (.literal 0), .return (.literal 1)] }
private def valueHelper : FunctionSpec :=
  { name := "value", params := [], returnType := some .uint256, isInternal := true,
    body := [.letVar "local" (.literal 8), .mstore (.literal 96) (.literal 9), .return (.literal 7)] }
private def model : CompilationModel :=
  { name := "TypedExpressions", fields := [], constructor := none,
    functions := [refusalHelper, valueHelper] }
private def caller : RuntimeState :=
  { world := Verity.defaultState.writeSlot 0 19, bindings := [("outer", 11)] }
private def runBody := SourceStatementEvaluation.execInternalStmts model [] 64
private def expected := "CREATE2 requires an actual opcode-entry execution context"
private def expectRefusal (result : StmtResult) : IO Unit := do
  match result with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "typed expression refusal became an EVM result")
private def receiptHelper : FunctionSpec :=
    { name := "receipt", params := [], returnType := some .uint256, isInternal := true,
      body := [.externalCallBind ["received"] "oracle" [], .return (.localVar "received")] }
private def externalModel : CompilationModel := { model with functions := model.functions ++ [receiptHelper] }
private def scheduled : RuntimeState :=
    { caller with
      externalCallIndex := 3
      externalCallOracle := fun index =>
        { succeeded := index != 4, returnValues := [100 + index],
          postCallWorld := some (caller.world.writeSlot 0 (700 + index)) } }
private def successfulSchedule : RuntimeState :=
  { scheduled with externalCallOracle := fun index =>
      { scheduled.externalCallOracle index with succeeded := true } }
private def externalModule : Compiler.ECM.ExternalCallModule :=
  { name := "typed-receipt", numArgs := 1, resultVars := ["last"],
    writesState := true, readsState := true, compile := fun _ _ => pure [] }

def runChecks : IO Unit := do
  expectRefusal (assign "result" (invoke runBody model caller "refused" []))
  expectRefusal (assign "result" ((invoke runBody model caller "refused" []).bind
    (fun value state => .value (value + 1) state)))
  match invoke runBody model caller "value" [] with
  | .value value next =>
      unless value == 7 && lookupValue next.bindings "outer" == 11 &&
          next.bindings.length == 1 && (next.world.memory 96).val == 9 && next.world.memory 0 == caller.world.memory 0 &&
          next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed helper dropped returned world or leaked locals")
  | _ => throw (IO.userError "typed helper success failed")
  let context : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := 0, depth := 0, isStatic := false }, warm := fun _ => false }
  let exceptional : RuntimeState := { caller with executionContext := some context }
  match assign "result" (ofHelperBody caller (.exceptional exceptional)) with
  | .exceptional next =>
      unless next.executionContext.isSome && next.bindings == caller.bindings do
        throw (IO.userError "typed expression lost exceptional state")
  | _ => throw (IO.userError "typed expression exceptional result became ordinary revert")
  match assign "result" (ofHelperBody caller .revert) with
  | .revert => pure ()
  | _ => throw (IO.userError "ordinary expression revert changed")
  match ofHelperBody caller (.continue caller) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "void helper fabricated expression value")
  let evaluate : RuntimeState → Expr → Result Nat := fun state expr =>
    match expr with
    | .internalCall name args =>
        if args.isEmpty then invoke runBody model state name []
        else .interpretationError "test evaluator requires no arguments"
    | .literal value => .value value { state with world := state.world.writeSlot 1 value }
    | .storage _ => .value (state.world.readSlot 1).val state
    | _ => .interpretationError "test evaluator unsupported expression"
  match evalList evaluate caller [.literal 23, .storage "probe"] with
  | .value values next =>
      unless values == [23, 23] && (next.world.readSlot 1).val == 23 do
        throw (IO.userError "typed expression arguments lost order or threaded state")
  | _ => throw (IO.userError "typed expression argument list failed")
  match evalList evaluate caller [.internalCall "refused" [], .literal 99] with
  | .interpretationError message => unless message == expected do throw (IO.userError message)
  | _ => throw (IO.userError "typed expression list continued after refusal")
  match invoke runBody model caller "absent" [] with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "missing typed expression helper accepted")
  let checked := SourceExpressionEvaluation.eval runBody model [] 64 caller
  expectRefusal (assign "result" (checked (.internalCall "refused" [])))
  expectRefusal (assign "result" (checked (.add (.literal 1) (.internalCall "refused" []))))
  match checked (.add (.internalCall "value" []) (.mload (.literal 96))) with
  | .value value next =>
      unless value == 16 && (next.world.memory 96).val == 9 && next.bindings == caller.bindings do
        throw (IO.userError "recursive typed expression lost helper poststate")
  | _ => throw (IO.userError "recursive typed expression success refused")
  match checked (.ite (.literal 0) (.internalCall "refused" []) (.literal 17)) with
  | .value value _ => unless value == 17 do throw (IO.userError "typed conditional wrong result")
  | _ => throw (IO.userError "typed conditional evaluated untaken helper")
  match SourceExpressionEvaluation.eval runBody model [] 0 caller (.literal 1) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed expression fuel became EVM outcome")
  let expression : Expr := .internalCall "refused" []
  for stmt in [Stmt.letVar "result" expression,
      .letVar "result" (.add (.literal 1) expression),
      .return expression, .require expression "helper failed",
      .mstore (.literal 0) expression, .ite expression [.stop] [],
      .forEach "i" expression [.stop]] do
    expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller stmt)
  let middle : FunctionSpec :=
    { name := "middle", params := [], returnType := some .uint256, isInternal := true,
      body := [.letVar "result" (.internalCall "refused" []), .return (.localVar "result")] }
  let nested := { model with functions := model.functions ++ [middle] }
  expectRefusal (SourceStatementEvaluation.execStmt nested [] 64 caller
    (.letVar "result" (.internalCall "middle" [])))
  match SourceStatementEvaluation.execStmts model [] 64 caller [
      .letVar "result" (.internalCall "value" []),
      .letVar "combined" (.add (.localVar "result") (.mload (.literal 96)))] with
  | .continue next =>
      unless lookupValue next.bindings "combined" == 16 &&
          lookupValue next.bindings "outer" == 11 && (next.world.memory 96).val == 9 do
        throw (IO.userError "typed statements lost helper effects or caller locals")
  | _ => throw (IO.userError "typed statement sequence failed")
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
    (.forEach "i" (.literal 1) [.letVar "result" expression]))
  match SourceStatementEvaluation.execStmt model [] 64 caller (.returnArray "not-supported") with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "unimplemented typed statement fabricated an EVM result")
  match SourceExpressionEvaluation.eval runBody model [] 0 caller (.literal 1) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed expression resource exhaustion changed")
  for statement in [
      Stmt.setStorageAddr "field" expression,
      .setStorageWord "field" 1 expression,
      .setMapping "field" expression (.literal 1),
      .setMappingWord "field" (.literal 1) 1 expression,
      .setMappingPackedWord "field" expression 1 { offset := 0, width := 8 } (.literal 1),
      .setMapping2 "field" (.literal 1) expression (.literal 1),
      .setMapping2Word "field" (.literal 1) (.literal 2) 1 expression,
      .setMappingUint "field" expression (.literal 1),
      .setStructMember "field" expression "member" (.literal 1),
      .setStructMember2 "field" (.literal 1) expression "member" (.literal 1),
      .storageArrayPush "field" expression,
      .setStorageArrayElement "field" (.literal 1) expression] do
    expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller statement)
  let chained := { model with fields := [{ name := "chain", ty := .mappingTyped (.simple .uint256), slot := some 6 }] }
  let chainSlot := SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain 6 [7, 3])
  match SourceStatementEvaluation.execStmt chained chained.fields 64 caller
      (.setMappingChain "chain" [.internalCall "value" [], .literal 3] (.mload (.literal 96))) with
  | .continue next =>
      unless (next.world.readSlot chainSlot).val == 9 && (next.world.memory 96).val == 9 &&
          next.bindings == caller.bindings && (next.world.readSlot 0).val == 19 do
        throw (IO.userError "typed mapping chain lost key order, helper state, value or frame")
  | _ => throw (IO.userError "typed mapping chain refused successful helper")
  for statement in [
      Stmt.setMappingChain "chain" [.internalCall "refused" []] (.literal 1),
      .setMappingChain "chain" [.literal 1] (.internalCall "refused" [])] do
    expectRefusal (SourceStatementEvaluation.execStmt chained chained.fields 64 caller statement)
  match SourceStatementEvaluation.execStmt chained chained.fields 64 caller
      (.setMappingChain "missing" [.literal 1] (.literal 1)) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed mapping chain accepted missing field")
  let stored := { model with fields := [{ name := "count", ty := .uint256, slot := some 3 }] }
  match SourceStatementEvaluation.execStmt stored stored.fields 64 caller
      (.setStorageWord "count" 1 (.internalCall "value" [])) with
  | .continue next =>
      unless (next.world.storage 4).val == 7 && (next.world.memory 96).val == 9 &&
          (next.world.readSlot 0).val == 19 do
        throw (IO.userError "typed storage word lost computed value, helper world or frame")
  | _ => throw (IO.userError "typed storage word refused successful helper")
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
    (.returnValues [.literal 1, expression]))
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
    (.calldatacopy (.literal 0) expression (.literal 1)))
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
    (.returndataCopy (.literal 0) (.literal 0) expression))
  match SourceStatementEvaluation.execStmt model [] 64 caller
      (.returnValues [.literal 3, .internalCall "value" []]) with
  | .stop next =>
      unless next.observedReturnWords == some [3, 7] && (next.world.memory 96).val == 9 do
        throw (IO.userError "typed multivalue return lost words or helper effects")
  | _ => throw (IO.userError "typed multivalue return failed")
  match SourceStatementEvaluation.execStmt model [] 64 caller
      (.returndataCopy (.literal 0) (.literal 0) (.literal 1)) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "returndata bounds failure fabricated an uncontextualized EVM outcome")
  let actualContext : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := 100, depth := 2, isStatic := false }, warm := fun _ => false }
  match SourceStatementEvaluation.execStmt model [] 64 { caller with executionContext := some actualContext }
      (.returndataCopy (.literal 0) (.literal 0) (.literal 1)) with
  | .exceptional next =>
      match next.executionContext with
      | some context => unless context.opcode.gas == 0 && context.opcode.depth == 2 do
          throw (IO.userError "returndata exceptional exit lost exhausted context")
      | none => throw (IO.userError "returndata exceptional exit lost context")
  | _ => throw (IO.userError "returndata bounds violation became ordinary revert")
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
    (.setImmutable "created" expression))
  match SourceStatementEvaluation.execStmt model [] 64 caller
      (.setImmutable "created" (.internalCall "value" [])) with
  | .continue next =>
      unless next.immutable "created" == 7 && next.immutable "other" == caller.immutable "other" &&
          (next.world.memory 96).val == 9 && next.bindings == caller.bindings do
        throw (IO.userError "typed immutable assignment lost value, effects or frame")
  | _ => throw (IO.userError "typed immutable assignment failed")
  let copyWorld := { caller.world with calldata := [0], returndata := [0xabcdef] }
  let copyState := { caller with selector := 0x12345678, world := copyWorld }
  match SourceStatementEvaluation.execStmt model [] 64 copyState
      (.calldatacopy (.literal 7) (.literal 1) (.literal 4)) with
  | .continue next =>
      unless (next.world.byteMemory.readByte 7).val == 0x34 &&
          (next.world.byteMemory.readByte 8).val == 0x56 &&
          (next.world.byteMemory.readByte 9).val == 0x78 &&
          (next.world.byteMemory.readByte 10).val == 0 &&
          next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed calldata copy lost selector crossing or storage frame")
  | _ => throw (IO.userError "typed calldata copy failed")
  match SourceStatementEvaluation.execStmt model [] 64 copyState
      (.returndataCopy (.literal 7) (.literal 29) (.literal 3)) with
  | .continue next =>
      unless (next.world.byteMemory.readByte 7).val == 0xab &&
          (next.world.byteMemory.readByte 8).val == 0xcd &&
          (next.world.byteMemory.readByte 9).val == 0xef &&
          next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed returndata copy lost bytes or storage frame")
  | _ => throw (IO.userError "typed returndata copy failed")
  let eventModel := { model with events := [{ name := "Value", params := [
    { name := "value", ty := .uint256, kind := .unindexed }] }] }
  expectRefusal (SourceStatementEvaluation.execStmt eventModel [] 64 caller
    (.emit "Value" [expression]))
  match SourceStatementEvaluation.execStmt eventModel [] 64 caller
      (.emit "Value" [.internalCall "value" []]) with
  | .continue next =>
      unless next.world.events.length == 1 && (next.world.memory 96).val == 9 &&
          next.bindings == caller.bindings && next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed emit lost helper effects, event or frame")
      match next.world.events with
      | [event] => unless event.name == "Value" && event.args == [7] && event.indexedArgs.length == 1 do
          throw (IO.userError "typed emit encoded wrong arguments or signature")
      | _ => throw (IO.userError "typed emit wrong event count")
  | _ => throw (IO.userError "typed emit failed")
  match SourceStatementEvaluation.execStmt model [] 64 caller (.emit "Unknown" []) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed emit fabricated undeclared event")
  let pairHelper : FunctionSpec :=
    { name := "pair", params := [], returnType := none, returns := [.uint256, .uint256],
      isInternal := true, body := [.letVar "private" (.literal 99),
        .mstore (.literal 96) (.literal 9), .returnValues [.literal 3, .literal 7]] }
  let pairModel := { model with functions := model.functions ++ [pairHelper] }
  let pairCaller := { caller with observedReturnWords := some [55] }
  match SourceStatementEvaluation.execStmt pairModel [] 64 pairCaller
      (.internalCallAssign ["first", "second"] "pair" []) with
  | .continue next =>
      unless lookupValue next.bindings "first" == 3 && lookupValue next.bindings "second" == 7 &&
          lookupValue next.bindings "outer" == 11 && next.bindings.length == 3 &&
          next.observedReturnWords == some [55] && (next.world.memory 96).val == 9 &&
          next.world.readSlot 0 == caller.world.readSlot 0 do
        throw (IO.userError "typed pair helper lost return order, effects or caller frame")
  | _ => throw (IO.userError "typed pair helper failed")
  match SourceStatementEvaluation.execStmt pairModel [] 64 caller
      (.internalCallAssign ["first"] "pair" []) with
  | .interpretationError _ => pure ()
  | _ => throw (IO.userError "typed pair helper silently truncated return values")
  expectRefusal (SourceStatementEvaluation.execStmt model [] 64 caller
      (.internalCallAssign ["first", "second"] "refused" []))
  match SourceStatementEvaluation.execStmts model [] 64 caller [
      .mstore (.literal 0) (.literal 19), .letVar "ignored" (.internalCall "value" []),
      .returnValues [.mload (.literal 0)]] with
  | .stop next => unless next.observedReturnWords == some [19] && (next.world.memory 96).val == 9 do
      throw (IO.userError "internal scalar return overwrote caller memory or lost helper writes")
  | _ => throw (IO.userError "internal return memory regression refused")
  for frame in [caller, pairCaller] do
    match SourceStatementEvaluation.execStmt pairModel [] 64 frame (.internalCall "pair" []) with
    | .continue next =>
        unless next.observedReturnWords == frame.observedReturnWords && next.bindings == frame.bindings &&
            (next.world.memory 96).val == 9 do
          throw (IO.userError "discarded helper leaked its return marker or lost effects")
    | _ => throw (IO.userError "discarded pair helper failed")
    match invoke runBody model frame "value" [] with
    | .value value next =>
        unless value == 7 && next.observedReturnWords == frame.observedReturnWords &&
            next.bindings == frame.bindings && (next.world.memory 96).val == 9 do
          throw (IO.userError "expression helper leaked return marker or lost effects")
    | _ => throw (IO.userError "expression helper return marker test failed")
  let stopped : FunctionSpec := { name := "stopped", params := [], returnType := some .uint256, isInternal := true, body := [.mstore (.literal 96) (.literal 9), .stop] }
  let stopModel := { model with functions := model.functions ++ [stopped] }
  for stmt in [Stmt.require (.internalCall "stopped" []) "unreachable", Stmt.internalCall "stopped" [], .internalCallAssign ["ignored"] "stopped" [],
      .letVar "ignored" (.internalCall "stopped" []),
      .letVar "ignored" (.add (.literal 1) (.internalCall "stopped" []))] do
    match SourceStatementEvaluation.execStmts stopModel [] 64 pairCaller [stmt,
        .mstore (.literal 128) (.literal 99)] with
    | .stop next =>
        unless (next.world.memory 96).val == 9 && (next.world.memory 128).val == 0 &&
            next.observedReturnWords == none && next.bindings == pairCaller.bindings do
          throw (IO.userError "global helper STOP lost effects or executed caller continuation")
    | _ => throw (IO.userError "global helper STOP became a caller continuation")
  let payload : List UInt8 := [0, 1, 255, 0, 7]
  let reverted : FunctionSpec := { name := "reverted", params := [], returnType := some .uint256, isInternal := true, body := [.panic .arithmeticOverflow] }
  let revertModel := { model with functions := model.functions ++ [reverted] }
  for stmt in [Stmt.internalCall "reverted" [], .internalCallAssign ["ignored"] "reverted" [],
      .letVar "ignored" (.internalCall "reverted" []),
      .require (.internalCall "reverted" []) "unreachable"] do
    match SourceStatementEvaluation.execStmts revertModel [] 64 caller [stmt, .stop] with
    | .revertWithData actual =>
        unless actual == Denote.panicBytes Verity.Core.PanicCode.arithmeticOverflow.toNat do
          throw (IO.userError "helper panic payload was altered")
    | _ => throw (IO.userError "helper panic payload was erased")
  match SourceExpressionOutcome.ofHelperBody caller (.revertWithData payload) with
  | .revertWithData actual => unless actual == payload do throw (IO.userError "helper byte transport changed")
  | _ => throw (IO.userError "helper byte transport erased")
  let errors : List ErrorDef := [{ name := "Denied", params := [.uint256, .address] }]
  let errorModel := { model with errors := errors }
  let oracle : Denote.DenoteOracle := { mappingSlot := Compiler.Proofs.abstractMappingSlot, keccakMemorySlice := SourceSemantics.keccakMemorySlice }
  let expectedError := Denote.customErrorBytes oracle errors "Denied" [7, 9]
  for stmt in [Stmt.revertError "Denied" [.literal 7, .literal 9],
      .requireError (.literal 0) "Denied" [.literal 7, .literal 9]] do
    match SourceStatementEvaluation.execStmt errorModel [] 64 caller stmt with
    | .revertWithData actual => unless some actual == expectedError do
        throw (IO.userError "custom error bytes changed")
    | _ => throw (IO.userError "custom error lost payload")
  match SourceStatementEvaluation.execStmt errorModel [] 64 caller
      (.requireError (.literal 1) "missing" [.internalCall "refused" []]) with
  | .continue next => unless next.bindings == caller.bindings do throw (IO.userError "require success changed frame")
  | _ => throw (IO.userError "require success evaluated error operands")
  for stmt in [Stmt.revertError "missing" [],
      .revertError "Denied" [.literal 7, .literal (2^160)],
      .revertError "Denied" [.literal 7]] do
    match SourceStatementEvaluation.execStmt errorModel [] 64 caller stmt with
    | .interpretationError message =>
        let name := match stmt with | .revertError name _ => name | _ => ""
        unless message == s!"typed source custom error is unsupported or arguments are noncanonical: {name}" do
          throw (IO.userError "custom error refusal diagnostic changed")
    | _ => throw (IO.userError "unsupported custom error fabricated EVM revert")
  expectRefusal (SourceStatementEvaluation.execStmt errorModel [] 64 caller
    (.revertError "Denied" [.internalCall "refused" [], .literal 9]))
  match SourceStatementEvaluation.execStmt errorModel [] 64 caller (.require (.literal 0) "denied") with
  | .revertWithData actual => unless actual == Denote.errorStringBytes "denied" do
      throw (IO.userError "require string bytes changed")
  | _ => throw (IO.userError "require string payload erased")
  for stmt in [Stmt.externalCallBind ["last"] "oracle" [.internalCall "receipt" []],
      .ecm externalModule [.internalCall "receipt" []]] do
    match SourceStatementEvaluation.execStmt externalModel [] 64 successfulSchedule stmt with
    | .continue next =>
        unless next.externalCallIndex == 5 && next.world.readSlot 0 == 704 &&
            next.world.returndata == [104] && lookupBinding? next.bindings "last" == some 104 &&
            lookupBinding? next.bindings "outer" == some 11 &&
            lookupBinding? next.bindings "received" == none do
          throw (IO.userError "typed external/ECM dropped argument terminal state")
    | _ => throw (IO.userError "typed external/ECM argument helper failed")
  -- Argument helper consumes receipt 3; the caught call must consume 4 and
  -- preserve the helper's committed world, not the failed receipt's world.
  match SourceStatementEvaluation.execStmts externalModel [] 64 scheduled
      [.tryExternalCallBind "ok" ["reason"] "oracle" [.internalCall "receipt" []],
       .externalCallBind ["last"] "oracle" []] with
  | .continue next =>
      unless next.externalCallIndex == 6 && lookupBinding? next.bindings "ok" == some 0 &&
          lookupBinding? next.bindings "reason" == some 104 &&
          lookupBinding? next.bindings "last" == some 105 &&
          next.world.readSlot 0 == 705 && next.world.returndata == [105] &&
          lookupBinding? next.bindings "received" == none do
        throw (IO.userError "typed external arguments lost receipt schedule, rollback or caller locals")
  | _ => throw (IO.userError "typed external argument helper did not resume")
  match SourceStatementEvaluation.execStmt externalModel [] 64 scheduled
      (.tryExternalCallBind "ok" ["reason"] "oracle" [.internalCall "receipt" []]) with
  | .continue next =>
      unless next.world.readSlot 0 == 703 && next.world.returndata == [104] &&
          next.externalCallIndex == 5 do
        throw (IO.userError "caught typed external call discarded argument effects or committed failure world")
  | _ => throw (IO.userError "caught typed external call failed")
  for stmt in [Stmt.externalCallBind ["unused"] "oracle" [.internalCall "refused" []],
      .tryExternalCallBind "ok" ["unused"] "oracle" [.internalCall "refused" []],
      .ecm externalModule [.internalCall "refused" []]] do
    expectRefusal (SourceStatementEvaluation.execStmt externalModel [] 64 scheduled stmt)
  IO.println "typed statements and recursive nested helper refusals passed"
end SolidityImportSmoke.SourceStatementEvaluationChecks
def main : IO Unit := SolidityImportSmoke.SourceStatementEvaluationChecks.runChecks
