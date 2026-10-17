import Compiler.Proofs.IRGeneration.SourceExpressionEvaluation

/-! Typed source statements consume typed recursive expressions, including
helper bodies. This staged executor never delegates a helper to the legacy
Option API. Unsupported statements explicitly refuse; importer admission and
whole-function compiler correspondence remain separate obligations. -/
namespace Compiler.Proofs.IRGeneration.SourceStatementEvaluation
open Compiler.CompilationModel
open SourceSemantics SourceExpressionOutcome

def consume (result : Result α) (next : α → RuntimeState → StmtResult) : StmtResult :=
  match result with
  | .value resolved state => next resolved state
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .halt state => .stop state
  | .interpretationError message => .interpretationError message
  | .exceptional state => .exceptional state

def restoreCaller (caller : RuntimeState) : StmtResult → StmtResult
  | .continue final | .return _ final =>
      .continue { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }
  | .stop final =>
      match final.observedReturnWords with
      | some _ => .continue { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }
      | none => .stop { final with bindings := caller.bindings }
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .interpretationError message => .interpretationError message
  | .exceptional final => .exceptional final

/-- Assigned helper returns retain computed effects and restore the caller's
locals. Arity is checked before binding, rather than silently truncating. -/
def assignHelperResult (caller : RuntimeState) (names : List String) : StmtResult → StmtResult
  | .return value final =>
      if names.length == 1 then
        .continue { final with bindings := bindValues caller.bindings names [value], observedReturnWords := caller.observedReturnWords }
      else .interpretationError "typed scalar helper return arity mismatch"
  | .stop final =>
      match final.observedReturnWords with
      | some values =>
          if names.length == values.length then
            .continue { final with bindings := bindValues caller.bindings names values, observedReturnWords := caller.observedReturnWords }
          else .interpretationError "typed multivalue helper return arity mismatch"
      | none => .stop { final with bindings := caller.bindings }
  | .continue _ => .interpretationError "typed assigned helper completed without return values"
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .interpretationError message => .interpretationError message
  | .exceptional final => .exceptional final

/-- Resolved scalar errors retain exact ABI bytes; unsupported definitions or
noncanonical values are interpreter refusals, never fabricated EVM reverts. -/
def customError (spec : CompilationModel) (name : String) (values : List Nat) : StmtResult :=
  match Denote.customErrorBytes
    { mappingSlot := Compiler.Proofs.abstractMappingSlot, keccakMemorySlice := SourceSemantics.keccakMemorySlice }
    spec.errors name values with
  | some bytes => .revertWithData bytes
  | none => .interpretationError s!"typed source custom error is unsupported or arguments are noncanonical: {name}"

mutual
def execStmtFrame (internalFrame : Bool) (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → Stmt → StmtResult
  | 0, _, _ => .interpretationError "typed source statement fuel exhausted"
  | fuel + 1, state, stmt =>
      let evaluate := SourceExpressionEvaluation.eval (execStmtsFrame true spec fields fuel) spec fields fuel state
      let arguments := SourceExpressionEvaluation.evalArgs (execStmtsFrame true spec fields fuel) spec fields fuel state
      match stmt with
      | .letVar name expr | .assignVar name expr => assign name (evaluate expr)
      | .return expr => consume (evaluate expr) (fun resolved next =>
          if internalFrame then .return resolved next
          else SourceSemantics.execStmtWithEvents fields spec.events next (.return (.literal resolved)))
      | .require expr message => consume (evaluate expr) (fun resolved next =>
          SourceSemantics.execStmtWithEvents fields spec.events next (.require (.literal resolved) message))
      | .requireError cond name args => consume (evaluate cond) (fun resolved next =>
          if resolved != 0 then .continue next
          else consume (SourceExpressionEvaluation.evalArgs
            (execStmtsFrame true spec fields fuel) spec fields fuel next args)
            (fun values _ => customError spec name values))
      | .revertError name args => consume (arguments args) (fun values _ => customError spec name values)
      | .mstore offset value => consume (arguments [offset, value]) (fun values next =>
          match values with
          | [resolvedOffset, resolvedValue] =>
              SourceSemantics.execStmtWithEvents fields spec.events next
                (.mstore (.literal resolvedOffset) (.literal resolvedValue))
          | _ => .interpretationError "typed source store operand mismatch")
      | .tstore offset value => consume (arguments [offset, value]) (fun values next =>
          match values with
          | [resolvedOffset, resolvedValue] =>
              SourceSemantics.execStmtWithEvents fields spec.events next
                (.tstore (.literal resolvedOffset) (.literal resolvedValue))
          | _ => .interpretationError "typed source transient store operand mismatch")
      | .emit name exprs => consume (arguments exprs) (fun values next =>
          match spec.events.find? (·.name == name) with
          | none => .interpretationError s!"typed source event is missing: {name}"
          | some _ =>
              match eventFromResolvedArgs? spec.events name values,
                  eventScratchWorldAfterEmit? spec.events name values next.world with
              | some event, some scratchWorld =>
                  let emitted := { scratchWorld with events := next.world.events ++ [event] }
                  .continue { next with world := emitted }
              | _, _ => .interpretationError s!"unsupported typed source event encoding: {name}")
      | .returnValues exprs => consume (arguments exprs) (fun values next =>
          .stop { next with observedReturnWords := some (values.map wordNormalize) })
      | .setImmutable name expr => consume (evaluate expr) (fun value next =>
          .continue { next with immutable := fun query =>
            if query == name then Verity.Core.Uint256.ofNat value else next.immutable query })
      | .calldatacopy destination source size =>
          consume (arguments [destination, source, size]) (fun values next =>
            match values with
            | [dst, src, extent] => .continue
                { next with world := next.world.copyPhysicalCalldata next.selector dst src extent }
            | _ => .interpretationError "typed calldata copy operand mismatch")
      | .returndataCopy destination source size =>
          consume (arguments [destination, source, size]) (fun values next =>
            match values with
            | [dst, src, extent] => execReturndataCopy next dst src extent "typed "
            | _ => .interpretationError "typed returndata copy operand mismatch")
      | .setStorage name expr => consume (evaluate expr) (fun resolved next =>
          match findFieldWithResolvedSlot fields name with
          | none => .interpretationError s!"typed source storage field is missing: {name}"
          | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
              (.setStorage name (.literal resolved)))
      | .setStorageAddr field value => consume (arguments [value]) (fun values next =>
          match values with
          | [resolved0] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setStorageAddr field (.literal resolved0))
          | _ => .interpretationError "typed source setStorageAddr operand mismatch")
      | .setStorageWord field wordOffset value => consume (arguments [value]) (fun values next =>
          match values with
          | [resolved0] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setStorageWord field wordOffset (.literal resolved0))
          | _ => .interpretationError "typed source setStorageWord operand mismatch")
      | .storageArrayPush field value => consume (arguments [value]) (fun values next =>
          match values with
          | [resolved0] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.storageArrayPush field (.literal resolved0))
          | _ => .interpretationError "typed source storageArrayPush operand mismatch")
      | .setStorageArrayElement field index value => consume (arguments [index, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setStorageArrayElement field (.literal resolved0) (.literal resolved1))
          | _ => .interpretationError "typed source setStorageArrayElement operand mismatch")
      | .setMapping field key value => consume (arguments [key, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMapping field (.literal resolved0) (.literal resolved1))
          | _ => .interpretationError "typed source setMapping operand mismatch")
      | .setMappingWord field key wordOffset value => consume (arguments [key, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMappingWord field (.literal resolved0) wordOffset (.literal resolved1))
          | _ => .interpretationError "typed source setMappingWord operand mismatch")
      | .setMappingPackedWord field key wordOffset packed value => consume (arguments [key, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMappingPackedWord field (.literal resolved0) wordOffset packed (.literal resolved1))
          | _ => .interpretationError "typed source setMappingPackedWord operand mismatch")
      | .setMapping2 field key1 key2 value => consume (arguments [key1, key2, value]) (fun values next =>
          match values with
          | [resolved0, resolved1, resolved2] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMapping2 field (.literal resolved0) (.literal resolved1) (.literal resolved2))
          | _ => .interpretationError "typed source setMapping2 operand mismatch")
      | .setMapping2Word field key1 key2 wordOffset value => consume (arguments [key1, key2, value]) (fun values next =>
          match values with
          | [resolved0, resolved1, resolved2] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMapping2Word field (.literal resolved0) (.literal resolved1) wordOffset (.literal resolved2))
          | _ => .interpretationError "typed source setMapping2Word operand mismatch")
      | .setMappingUint field key value => consume (arguments [key, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setMappingUint field (.literal resolved0) (.literal resolved1))
          | _ => .interpretationError "typed source setMappingUint operand mismatch")
      | .setMappingChain field keys value => consume (arguments keys) (fun resolvedKeys keyState =>
          consume (SourceExpressionEvaluation.eval (execStmtsFrame true spec fields fuel)
            spec fields fuel keyState value) (fun resolved next =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                  (.setMappingChain field (resolvedKeys.map Expr.literal) (.literal resolved))))
      | .setStructMember field key memberName value => consume (arguments [key, value]) (fun values next =>
          match values with
          | [resolved0, resolved1] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setStructMember field (.literal resolved0) memberName (.literal resolved1))
          | _ => .interpretationError "typed source setStructMember operand mismatch")
      | .setStructMember2 field key1 key2 memberName value => consume (arguments [key1, key2, value]) (fun values next =>
          match values with
          | [resolved0, resolved1, resolved2] =>
              match findFieldWithResolvedSlot fields field with
              | none => .interpretationError s!"typed source storage field is missing: {field}"
              | some _ => SourceSemantics.execStmtWithEvents fields spec.events next
                (.setStructMember2 field (.literal resolved0) (.literal resolved1) memberName (.literal resolved2))
          | _ => .interpretationError "typed source setStructMember2 operand mismatch")
      | .create2 name offset size salt => consume (arguments [offset, size, salt]) (fun values next =>
          match values with
          | [resolvedOffset, resolvedSize, resolvedSalt] =>
              execCreation fields next name (.literal resolvedOffset) (.literal resolvedSize) (.literal resolvedSalt)
          | _ => .interpretationError "typed source CREATE2 operand mismatch")
      | .ite cond thenBody elseBody => consume (evaluate cond) (fun value next =>
          execStmtsFrame internalFrame spec fields fuel next (if value != 0 then thenBody else elseBody))
      | .forEach name count body => consume (evaluate count) (fun value next =>
          execLoopFrame internalFrame spec fields fuel next name body 0 value)
      -- Evaluate effectful arguments once before taking the next receipt. The
      -- resolved call delegates only the existing abstract external transition;
      -- it does not delegate expression evaluation to the legacy Option API.
      | .externalCallBind names externalName args => consume (arguments args) (fun values next =>
          SourceSemantics.execStmtWithEvents fields spec.events next
            (.externalCallBind names externalName (values.map Expr.literal)))
      | .tryExternalCallBind successName names externalName args => consume (arguments args) (fun values next =>
          SourceSemantics.execStmtWithEvents fields spec.events next
            (.tryExternalCallBind successName names externalName (values.map Expr.literal)))
      | .ecm mod args => consume (arguments args) (fun values next =>
          SourceSemantics.execStmtWithEvents fields spec.events next
            (.ecm mod (values.map Expr.literal)))
      | .internalCall name args => consume (arguments args) (fun values next =>
          match spec.functions.filter (fun fn => fn.isInternal && fn.name == name) with
          | [helper] =>
              match bindInternalArgs helper.params values with
              | none => .interpretationError s!"typed statement helper argument mismatch: {name}"
              | some bindings => restoreCaller next
                  (execStmtsFrame true spec fields fuel { next with bindings := bindings, observedReturnWords := none } helper.body)
          | _ => .interpretationError s!"typed statement helper is missing or ambiguous: {name}")
      | .internalCallAssign names helperName args => consume (arguments args) (fun values next =>
          match spec.functions.filter (fun fn => fn.isInternal && fn.name == helperName) with
          | [helper] =>
              match bindInternalArgs helper.params values with
              | none => .interpretationError s!"typed assigned helper argument mismatch: {helperName}"
              | some bindings => assignHelperResult next names
                  (execStmtsFrame true spec fields fuel
                    { next with bindings := bindings, observedReturnWords := none } helper.body)
          | _ => .interpretationError s!"typed assigned helper is missing or ambiguous: {helperName}")
      | .revertReturndata => .revertWithData (state.world.returndata.flatMap Denote.wordBytes)
      | .panic code => .revertWithData (Denote.panicBytes code.toNat)
      | .panicCode code => consume (evaluate code) (fun value _ => .revertWithData (Denote.panicBytes value))
      | .stop => .stop { state with observedReturnWords := none }
      | _ => .interpretationError "unsupported typed source statement construct"

def execStmtsFrame (internalFrame : Bool) (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → List Stmt → StmtResult
  | _, state, [] => .continue state
  | 0, _, _ :: _ => .interpretationError "typed source statement-list fuel exhausted"
  | fuel + 1, state, stmt :: rest =>
      match execStmtFrame internalFrame spec fields fuel state stmt with
      | .continue next => execStmtsFrame internalFrame spec fields fuel next rest
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert
      | .revertWithData data => .revertWithData data
      | .interpretationError message => .interpretationError message
      | .exceptional next => .exceptional next

def execLoopFrame (internalFrame : Bool) (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → String → List Stmt → Nat → Nat → StmtResult
  | _, state, _, _, _, 0 => .continue state
  | 0, _, _, _, _, _ + 1 => .interpretationError "typed source loop fuel exhausted"
  | fuel + 1, state, name, body, index, remaining + 1 =>
      match execStmtsFrame internalFrame spec fields fuel
          { state with bindings := bindValue state.bindings name (wordNormalize index) } body with
      | .continue next => execLoopFrame internalFrame spec fields fuel next name body (index + 1) remaining
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert
      | .revertWithData data => .revertWithData data
      | .interpretationError message => .interpretationError message
      | .exceptional next => .exceptional next
end

/-- External and internal frames share execution but have different return effects. -/
def execStmt (spec : CompilationModel) (fields : List Field) := execStmtFrame false spec fields
def execStmts (spec : CompilationModel) (fields : List Field) := execStmtsFrame false spec fields
def execLoop (spec : CompilationModel) (fields : List Field) := execLoopFrame false spec fields
def execInternalStmts (spec : CompilationModel) (fields : List Field) := execStmtsFrame true spec fields

theorem consume_refusal (message : String) (next : α → RuntimeState → StmtResult) :
    consume (.interpretationError message) next = .interpretationError message := rfl

theorem consume_exceptional (state : RuntimeState) (next : α → RuntimeState → StmtResult) :
    consume (.exceptional state) next = .exceptional state := rfl


theorem execStmts_refusal (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state : RuntimeState) (stmt : Stmt) (rest : List Stmt) (message : String)
    (h : execStmt spec fields fuel state stmt = .interpretationError message) :
    execStmts spec fields (fuel + 1) state (stmt :: rest) = .interpretationError message := by
  simp only [execStmt] at h
  simp only [execStmts, execStmtsFrame, h]

theorem execStmts_exceptional (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state final : RuntimeState) (stmt : Stmt) (rest : List Stmt)
    (h : execStmt spec fields fuel state stmt = .exceptional final) :
    execStmts spec fields (fuel + 1) state (stmt :: rest) = .exceptional final := by
  simp only [execStmt] at h
  simp only [execStmts, execStmtsFrame, h]

theorem execLoop_refusal (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state : RuntimeState) (name : String) (body : List Stmt)
    (index remaining : Nat) (message : String)
    (h : execStmts spec fields fuel
      { state with bindings := bindValue state.bindings name (wordNormalize index) } body =
        .interpretationError message) :
    execLoop spec fields (fuel + 1) state name body index (remaining + 1) =
      .interpretationError message := by
  simp only [execStmts] at h
  simp only [execLoop, execLoopFrame, h]

theorem assignHelperResult_refusal (caller : RuntimeState) (names : List String) (message : String) :
    assignHelperResult caller names (.interpretationError message) = .interpretationError message := rfl

theorem assignHelperResult_exceptional (caller final : RuntimeState) (names : List String) :
    assignHelperResult caller names (.exceptional final) = .exceptional final := rfl

theorem assignHelperResult_values (caller final : RuntimeState) (names : List String)
    (values : List Nat) (returns : final.observedReturnWords = some values)
    (arity : names.length = values.length) :
    assignHelperResult caller names (.stop final) =
      .continue { final with bindings := bindValues caller.bindings names values, observedReturnWords := caller.observedReturnWords } := by
  simp only [assignHelperResult, returns, arity, BEq.rfl, if_true]

end Compiler.Proofs.IRGeneration.SourceStatementEvaluation
