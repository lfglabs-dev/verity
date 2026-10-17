import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.IRGeneration.IRMemoryCoherence
open Compiler.Yul Compiler.CompilationModel DenoteMemory

def Coherent (state : IRState) : Prop :=
  ∀ query, state.memory query = (wordValue (state.byteMemory.readWord query)).val

def Preserves : IRExecResult → Prop
  | .continue state | .stop state | .return _ state | .revert state | .exceptional state => Coherent state
  | .interpretationError _ => True

theorem installed (state : IRState) (memory : Memory) :
    Coherent (state.installPhysicalMemory memory) := fun _ => rfl

theorem written (state : IRState) (offset value : Nat) :
    Coherent (state.writePhysicalMemoryValue offset value) := installed _ _

theorem copied (state : IRState) (source : Nat → Byte)
    (dst src size : Nat) (coherent : Coherent state) :
    Coherent (state.copyPhysicalBytes source dst src size) := by
  by_cases zero : size = 0
  · simpa only [zero, IRState.copyPhysicalBytes_zero] using coherent
  · simp only [IRState.copyPhysicalBytes, zero, if_false]
    exact installed _ _

private theorem calldata_copied (state : IRState) (dst src size : Nat) (coherent : Coherent state) :
    Coherent (state.copyPhysicalCalldata dst src size) := copied state _ dst src size coherent
private theorem returndata_copied (state : IRState) (dst src size : Nat) (coherent : Coherent state) :
    Coherent (state.copyPhysicalReturndata dst src size) := copied state _ dst src size coherent

theorem word_outside_store (state : IRState) (offset value query : Nat)
    (coherent : Coherent state) (outside : query + 32 ≤ offset ∨ offset + 32 ≤ query) :
    (state.writePhysicalMemoryValue offset value).memory query = state.memory query := by
  change (wordValue ((state.byteMemory.writeWord offset
    (valueWord (Verity.Core.Uint256.ofNat value))).readWord query)).val = _
  rw [Memory.readWord_writeWord_outside _ _ _ _ outside, ← coherent query]

private theorem log_coherent (state next : IRState) (func : String) (values : List Nat)
    (coherent : Coherent state) (logged : applyYulLogCall? state func values = some next) :
    Coherent next := by
  unfold applyYulLogCall? at logged
  split at logged <;> simp only [Option.some.injEq, reduceCtorEq] at logged
  all_goals subst next; exact coherent

-- Keep physical readWord internals opaque during executor case analysis.
-- Frame lemmas above explicitly expose the byte projection where needed.
attribute [irreducible] Coherent

/-- Nonrecursive expression dispatch, checked definitionally against the actual
mutual executor. This factors kernel checking without changing execution. -/
private def expressionResult (state : IRState) (e : YulExpr) : IRExecResult :=
  match e with
  | .call "sstore" [slotExpr, valExpr] =>
      match slotExpr with
      | .call "mappingSlot" [baseExpr, keyExpr] =>
          match evalIRExpr state baseExpr, evalIRExpr state keyExpr, evalIRExpr state valExpr with
          | some baseSlot, some key, some val =>
              let updated := Compiler.Proofs.abstractStoreMappingEntry
                state.storage baseSlot key val
              .continue {
                state with
                storage := updated
              }
          | _, _, _ => .revert state
      | _ =>
          match evalIRExpr state slotExpr, evalIRExpr state valExpr with
          | some slot, some val =>
              let updated := Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage slot val
              .continue {
                state with
                storage := updated
              }
          | _, _ => .revert state
  | .call "mstore" [offsetExpr, valExpr] =>
      match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
      | some offset, some val =>
        .continue (state.writePhysicalMemoryValue (Verity.Core.Uint256.ofNat offset).val val)
      | _, _ => .revert state
  | .call "tstore" [offsetExpr, valExpr] =>
      match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
      | some offset, some val =>
        let offset := offset % Compiler.Constants.evmModulus
        .continue {
          state with
          transientStorage := fun o =>
            if o = offset then val else state.transientStorage o
        }
      | _, _ => .revert state
  | .call "calldatacopy" [dstExpr, srcExpr, sizeExpr] =>
      match evalIRExpr state dstExpr, evalIRExpr state srcExpr,
          evalIRExpr state sizeExpr with
      | some dst, some src, some size =>
        .continue (state.copyPhysicalCalldata dst src size)
      | _, _, _ => .revert state
  | .call "returndatacopy" [dstExpr, srcExpr, sizeExpr] =>
      match evalIRExpr state dstExpr, evalIRExpr state srcExpr,
          evalIRExpr state sizeExpr with
      | some dst, some src, some size =>
        let dst := dst % Compiler.Constants.evmModulus
        let src := src % Compiler.Constants.evmModulus
        let size := size % Compiler.Constants.evmModulus
        if src + size ≤ 32 * state.returndata.length then
          .continue (state.copyPhysicalReturndata dst src size)
        else
          match state.executionContext with
          | some context => .exceptional { state with executionContext := some { context with opcode := { context.opcode with gas := 0 } } }
          | none => .interpretationError
              "returndata copy exceptional exit requires actual opcode context"
      | _, _, _ => .revert state
  | .call "stop" [] => .stop state
  | .call "revert" [offsetExpr, sizeExpr] =>
      match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
      | some offset, some size => .revert (state.captureRevert offset size)
      | _, _ => .revert state
  | .call "return" [offsetExpr, sizeExpr] =>
      match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
      | some offset, some size =>
        if size = 32 then
          .return (state.memory offset) state
        else
          .return 0 state
      | _, _ => .revert state
  | .call "invalid" [] => .revert state
  | .call "selfdestruct" [addrExpr] =>
      match evalIRExpr state addrExpr with
      | some _ => .stop state
      | none => .revert state
  | .call func args =>
      if isYulLogName func then
        match evalIRExprs state args with
        | some argVals =>
            match applyYulLogCall? state func argVals with
            | some next => .continue next
            | none => .revert state
        | none => .revert state
      else
        -- Keep expression-statement behavior aligned with Yul:
        -- evaluate the expression and revert on evaluation failure.
        match evalIRExpr state e with
        | some _ => .continue state
        | none => .revert state
  | _ =>
      -- Keep expression-statement behavior aligned with Yul:
      -- evaluate the expression and revert on evaluation failure.
      match evalIRExpr state e with
      | some _ => .continue state
      | none => .revert state

private theorem expression_eq (state : IRState) (e : YulExpr) (fuel : Nat) :
    execIRStmt (fuel + 1) state (.exprStmt e) = expressionResult state e := rfl

set_option diagnostics true in
private theorem expression_result_coherent (state : IRState) (expr : YulExpr)
    (coherent : Coherent state) : Preserves (expressionResult state expr) := by
  fun_cases expressionResult state expr
  case case5 => exact written state _ _
  case case9 => exact calldata_copied state _ _ _ coherent
  case case11 => exact returndata_copied state _ _ _ coherent
  case case16 => simpa only [Preserves, Coherent, IRState.captureRevert] using coherent
  case case24 => exact log_coherent state _ _ _ coherent (by assumption)
  all_goals repeat' first
    | (solve | simpa only [Preserves, Coherent] using coherent)
    | (solve | trivial)
    | split

private theorem expression_statement (state : IRState) (expr : YulExpr) (fuel : Nat)
    (coherent : Coherent state) : Preserves (execIRStmt (fuel + 1) state (.exprStmt expr)) := by
  change Preserves (expressionResult state expr)
  exact expression_result_coherent state expr coherent

/-- Factor the loop case of mutual execution preservation at a fixed smaller
fuel. The actual init, condition, body and post results are inspected in order. -/
private theorem loop_preserves (fuel : Nat) (state : IRState)
    (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    (stmtStep : ∀ state stmt, Coherent state → Preserves (execIRStmt fuel state stmt))
    (listStep : ∀ state stmts, Coherent state → Preserves (execIRStmts fuel state stmts))
    (coherent : Coherent state) :
    Preserves (execIRStmt (fuel + 1) state (.for_ init cond post body)) := by
  simp only [execIRStmt]
  have initKept := listStep state init coherent
  cases first : execIRStmts fuel state init <;> simp only [first, Preserves] at initKept ⊢
  all_goals try exact initKept
  rename_i middle
  cases condition : evalIRExpr middle cond with
  | none => simpa only [condition, Preserves] using initKept
  | some value =>
      simp only [condition]
      by_cases zero : value = 0
      · simpa only [zero, ne_eq, not_true_eq_false, if_false, Preserves] using initKept
      · simp only [zero, ne_eq, not_false_eq_true, if_true]
        have bodyKept := listStep middle body initKept
        cases second : execIRStmts fuel middle body <;> simp only [second, Preserves] at bodyKept ⊢
        all_goals try exact bodyKept
        rename_i afterBody
        have postKept := listStep afterBody post bodyKept
        cases third : execIRStmts fuel afterBody post <;> simp only [third, Preserves] at postKept ⊢
        all_goals try exact postKept
        exact stmtStep _ _ postKept

/-- Both actual mutual opcode executors preserve the physical/word invariant,
including capture, zero-copy, loops and exhaustion. -/
theorem executors (fuel : Nat) :
    (∀ state stmt, Coherent state → Preserves (execIRStmt fuel state stmt)) ∧
    (∀ state stmts, Coherent state → Preserves (execIRStmts fuel state stmts)) := by
  induction fuel with
  | zero =>
      constructor
      · intro state stmt coherent
        cases stmt <;> simpa only [execIRStmt, Preserves] using coherent
      · intro state stmts coherent
        cases stmts <;> exact coherent
  | succ fuel ih =>
      constructor
      · intro state stmt coherent
        cases stmt with
        | if_ cond body =>
            simp only [execIRStmt]
            split
            · split
              · exact ih.2 state body coherent
              · exact coherent
            · exact coherent
        | block body => exact ih.2 state body coherent
        | for_ init cond post body => exact loop_preserves fuel state init cond post body ih.1 ih.2 coherent
        | «switch» expr branches fallback =>
            simp only [execIRStmt]
            repeat' first | split | (apply ih.2; exact coherent) | exact coherent
        | exprStmt expr => exact expression_statement state expr fuel coherent
        | _ =>
            simp only [execIRStmt]
            repeat' first | split | (solve | simp_all [Preserves, Coherent, IRState.setVar])
      · intro state stmts coherent
        cases stmts with
        | nil => exact coherent
        | cons stmt rest =>
            simp only [execIRStmts]
            have firstKept := ih.1 state stmt coherent
            cases first : execIRStmt fuel state stmt <;>
              simp only [first, Preserves] at firstKept ⊢
            all_goals try exact firstKept
            exact ih.2 _ rest firstKept

end Compiler.Proofs.IRGeneration.IRMemoryCoherence
